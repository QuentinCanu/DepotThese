#! /usr/bin/env python3
# --------------------------------------------------------------------
import argparse as argp
import subprocess as sp
import itertools as it
import os
import re
import time
import math
from scripts import genlrs, lrs2common, common2certif, dict2bin, bin2coq, dict2text, coqjobs, certif2hirsch
from scripts.rank1 import lrs2dict_r1, lrs2dict_r1_pivot, lrs2dict_r1_matrix, lrs2dict_r1_vector, lrs2dict_r1_lazy
import csv
import shutil
import json
import matplotlib.pyplot as pp

CWD = os.getcwd()
TIME_MEM_PREFIX = r'TIMEFMT="%E : real time, %M : max memory" && '
HIRSCH_CEX = ["poly20dim21","poly23dim24"]
POLYTOPES = ["cube", "cross", "cyclic", "permutohedron"]
DATA_DIR = os.path.join(CWD,"data")
JOB_DIR = os.path.join(CWD,"jobs")
BUILD_DATA_DIR = os.path.join(CWD,'..','..','_build','default','enumeration','benchmarks','data')
NO_BENCH = "------"
COMMON = "common"
GRAPH_CERTIF = "graph_certif"
HIRSCH = "hirsch"
DIAMETER = "diameter"
IMPROVED = "improved"
RANK1 = "rank1"
PIVOT = "pivot"
R1_MATRIX = "r1_matrix"
R1_VECTOR = "r1_vector"
LAZY = "lazy"

GENERATORS = {
    COMMON : lrs2common.lrs2common,
    GRAPH_CERTIF : common2certif.common2certif,
    HIRSCH : certif2hirsch.certif2hirsch,
    DIAMETER : (lambda name,certif : {"g_vtx" : certif["g_vtx"]}),
    IMPROVED : (lambda name, certif : 
      {i : certif[i] for i in 
       ["A","b","g_lex","vertices","bases","inverses"]}),
    RANK1 : lrs2dict_r1.lrs2dict,
    PIVOT : lrs2dict_r1_pivot.lrs2dict,
    R1_MATRIX : lrs2dict_r1_matrix.lrs2dict,
    R1_VECTOR : lrs2dict_r1_vector.lrs2dict,
    LAZY : lrs2dict_r1_lazy.lrs2dict
    }

PREREQUISITES = {
  GRAPH_CERTIF : "PolyhedraHirschVerif",
  DIAMETER : "PolyhedraHirsch",
  IMPROVED : "PolyhedraHirschImprVerif",
  HIRSCH : "PolyhedraHirschVerif",
  RANK1 : "PolyhedraHirschRank1",
  PIVOT : "PolyhedraHirschRank1",
  R1_MATRIX : "PolyhedraHirschRank1",
  R1_VECTOR : "PolyhedraHirschRank1",
  LAZY : "PolyhedraHirschRank1",
}


# --------------------------------------------------------------------
# def chunks(lst, n):
#     """Yield successive n-sized chunks from lst."""
#     for i in range(0, len(lst), n):
#         yield lst[i:i + n]

def command_call(command, timeout=None, prefix=""):
  print(command)
  try:
    output = sp.run(prefix + command,
            shell=True, executable="/bin/zsh", check=True,
            capture_output=True, text=True, timeout=timeout)
    print(output.stdout, output.stderr)
    return output.stderr
  except:
    print("ERREUR !")
    return None

def format_time_output(st):
  if st is None:
    return None, None
  findit = re.search(r"(?P<time>\d+)[,.](?P<mtime>\d+)s.+, (?P<memory>\d+)", st)
  time, mtime = findit.group("time"), findit.group("mtime")
  memory = float(findit.group("memory"))
  return f"{time}.{mtime}", str(memory)

# --------------------------------------------------------------------
def polytope_name(polytope,param):
  return f"{polytope}_{param}_{2*param}" if polytope == "cyclic" else f"{polytope}_{param}"

def dune_name_certif(name, algo, text = False):
  return "_".join([name.upper(), algo.upper(), "DATA"] + (["TEXT"] if text else []))

def dune_name_algo(name, algo, compute = False):
  return "_".join([name.upper(), algo.upper()] + (["CMP"] if compute else []))

# --------------------------------------------------------------------
def gen_lrs(polytope, param):
  if polytope not in HIRSCH_CEX:
    if polytope == "cyclic":
      genlrs.generate_lrs(polytope, param, 2*param)
    else:
      genlrs.generate_lrs(polytope, param)

# --------------------------------------------------------------------
def compute_lrs(name):
  inefile = os.path.join(DATA_DIR, name, "lrs", name+".ine")
  extfile = os.path.join(DATA_DIR, name, "lrs", name+".ext")
  time, memory = format_time_output(command_call(f"time lrs {inefile} {extfile}",prefix=TIME_MEM_PREFIX))
  return {"time" : time, "memory" : memory}

# --------------------------------------------------------------------
def generation(tgtname, start, *certificates):
  def worker(name):
    st = time.time()
    tgtdir = os.path.join(DATA_DIR, name, "certificates", tgtname)
    os.makedirs(tgtdir,exist_ok=True)
    tgtfile = os.path.join(tgtdir,name+".json")
    startdir = os.path.join(DATA_DIR,name,"certificates", start) 
    startfile = os.path.join(startdir, name+".json")
    if not os.path.exists(startfile):
      os.makedirs(startdir, exist_ok=True)
      certif = GENERATORS[start](name)
      with open(startfile, "w") as stream:
        json.dump(certif, stream,indent=0)
    else:
      with open(startfile) as stream:
        certif = json.load(stream)
    for cert in certificates:
      certif = GENERATORS[cert](name,certif)
    et = time.time()
    with open(tgtfile,"w") as stream:
      json.dump(certif,stream,indent=0)
    return {"time" : et - st}
  return worker

# --------------------------------------------------------------------
def job(jobdir, *relpath):
  res = {}
  times = []
  max_memory = -math.inf
  files = list(os.listdir(jobdir))
  files.sort()
  files.sort(key=f"final.v".__eq__)
  for file in files:
    if file.endswith(".v"):
      rel_path = os.path.join(*relpath, file+"o")
      st = command_call("time dune build " + rel_path, prefix=TIME_MEM_PREFIX)
      time, memory = format_time_output(st)
      res[file + " execution time"] = time
      res[file + " execution memory"] = memory
      times.append(float(time if time is not None else 0.0))
      max_memory = max(max_memory,float(memory if memory is not None else 0.0))
  res["total execution time"] = str(math.fsum(times))
  res["max execution memory"] = str(max_memory)
  return res

def certif_compilation(tgtdir, *relpath):
  res = {}
  times = []
  max_memory = -math.inf
  files = sorted(os.listdir(tgtdir))
  for file in files:
    if file.endswith(".v"):
      print(f"Compiling {file}")
      rel_path = os.path.join(*relpath,file+"o")
      st = command_call("time dune build " + rel_path,prefix=TIME_MEM_PREFIX)
      time, memory = format_time_output(st)
      res[file + " compilation time"] = time
      res[file + " memory"] = memory
      times.append(float(time if time is not None else 0.0))
      max_memory = max(max_memory,float(memory if memory is not None else 0.0))
  res["total compilation time"] = str(math.fsum(times))
  res["max compilation memory"] = str(max_memory)
  return res
# --------------------------------------------------------------------
def conversion(certif_type, text=False):
  def worker(name):
    res = {}
    certif_path = os.path.join(DATA_DIR, name, "certificates", certif_type, name+".json")
    with open(certif_path) as stream:
      certif = json.load(stream)
    
    if text:
      textpath = ["data", name, certif_type, "text_certif"]
      textdir = os.path.join(CWD, *textpath)
      os.makedirs(textdir, exist_ok = True)
      st = time.time()
      bench = dict2text.dict2text(dune_name_certif(name, certif_type, True), textdir, certif)
      et = time.time()
      res["time of serialization"] = et - st 
      res.update(bench)
      res.update(certif_compilation(textdir, *textpath))
    else:
      binpath = ["data", name, certif_type, "bin_certif"]
      bindir = os.path.join(CWD, *binpath)
      os.makedirs(bindir, exist_ok = True)
      st = time.time()
      bench = dict2bin.dict2bin(bindir,certif)
      bin2coq.bin2coq(dune_name_certif(name, certif_type), bindir)
      et = time.time()
      res["time of serialization"] = et - st
      res.update(bench)
      res.update(certif_compilation(bindir, *binpath))
    return res
  return worker

# --------------------------------------------------------------------
def execution(algo,compute=False):
  def worker(name):
    tgtpath = ["data", name, algo, "compute" if compute else "vm_compute"]
    tgtdir = os.path.join(CWD, *tgtpath)
    os.makedirs(tgtdir,exist_ok = True)
    jobdir = os.path.join(JOB_DIR, algo)
    coqjobs.coqjob(name, dune_name_algo(name, algo,compute), dune_name_certif(name, algo), PREREQUISITES[algo], jobdir, tgtdir, compute)
    return job(tgtdir,*tgtpath)
  return worker

# --------------------------------------------------------------------
# --------------------------------------------------------------------
def clean(args):
  dirname = args.dirname
  taskname = args.taskname
  if dirname in os.listdir(DATA_DIR):
    taskdir = os.path.join(DATA_DIR,dirname,taskname)
    if os.path.isdir(taskdir):
      shutil.rmtree(taskdir)
    builddir = os.path.join(BUILD_DATA_DIR,dirname,taskname)
    if os.path.isdir(builddir):
      shutil.rmtree(builddir)
  benchfile = os.path.join(DATA_DIR,dirname,f"benchmarks_{dirname}.json")
  if os.path.exists(benchfile):
    with open(benchfile) as stream:
      bench = json.load(stream)
      bench[f"{taskname}_conversion"] = None
      bench[f"{taskname}_execution"] = None
    with open(benchfile, "w") as stream:
      json.dump(bench,stream,indent=0)


# --------------------------------------------------------------------
def make_benchmarks(name,taskdict):
  benchmarks_path = os.path.join(DATA_DIR,name,f"benchmarks_{name}.json")
  if os.path.exists(benchmarks_path):
    with open(benchmarks_path) as stream:
      benchmarks = json.load(stream)
  else:
    benchmarks = dict(zip(taskdict,it.repeat(None)))
  for task in taskdict.keys():
    print(f"Performing {task}")
    if benchmarks.get(task, None) is None:
      res = taskdict[task](name)
      benchmarks[task] = res
      with open(benchmarks_path, "w") as stream:
        json.dump(benchmarks,stream,indent=0)
    else:
      print(f"The task {task} has already been performed on {name}. Skipped.")
# --------------------------------------------------------------------
TASKS = {
  "lrs" : compute_lrs,
  "graph_certif_generation" : generation(GRAPH_CERTIF, COMMON,GRAPH_CERTIF),
  "graph_certif_conversion" : conversion(GRAPH_CERTIF),
  "graph_certif_conversion_text" : conversion(GRAPH_CERTIF, text=True),
  "graph_certif_execution" : execution(GRAPH_CERTIF),
  "graph_certif_execution_compute" : execution(GRAPH_CERTIF,compute=True),
  # "diameter_generation" : generation(DIAMETER, GRAPH_CERTIF, DIAMETER),
  # "diameter_conversion" : conversion(DIAMETER),
  # "diameter_execution" : execution(DIAMETER),
  "improved_generation" : generation(IMPROVED, COMMON, IMPROVED),
  "improved_conversion" : conversion(IMPROVED),
  "improved_execution" : execution(IMPROVED),
  "rank1_generation" : generation(RANK1,RANK1),
  "rank1_conversion" : conversion(RANK1),
  "rank1_execution" : execution(RANK1),
  "pivot_generation" : generation(PIVOT,PIVOT),
  "pivot_conversion" : conversion(PIVOT),
  "pivot_execution" : execution(PIVOT),
  "r1_matrix_generation" : generation(R1_MATRIX,R1_MATRIX),
  "r1_matrix_conversion" : conversion(R1_MATRIX),
  "r1_matrix_execution" : execution(R1_MATRIX),
  "r1_vector_generation" : generation(R1_VECTOR, R1_VECTOR),
  "r1_vector_conversion" : conversion(R1_VECTOR),
  "r1_vector_execution" : execution(R1_VECTOR),
  "lazy_generation" : generation(LAZY, LAZY),
  "lazy_conversion" : conversion(LAZY),
  "lazy_execution" : execution(LAZY),
}

HIRSCH_TASKS = {
    "lrs" : compute_lrs,
    "hirsch_generation" : generation(HIRSCH,COMMON, GRAPH_CERTIF, HIRSCH), 
    "hirsch_conversion" : conversion(HIRSCH),
    "hirsch_execution" : execution(HIRSCH),
    "improved_generation" : generation(IMPROVED, COMMON, IMPROVED),
    "improved_conversion" : conversion(IMPROVED),
    "improved_execution" : execution(IMPROVED),
    "rank1_generation" : generation(RANK1,RANK1),
    "rank1_conversion" : conversion(RANK1),
    "rank1_execution" : execution(RANK1),
    "pivot_generation" : generation(PIVOT,PIVOT),
    "pivot_conversion" : conversion(PIVOT),
    "pivot_execution" : execution(PIVOT),
    "r1_matrix_generation" : generation(R1_MATRIX,R1_MATRIX),
    "r1_matrix_conversion" : conversion(R1_MATRIX),
    "r1_matrix_execution" : execution(R1_MATRIX),
    "r1_vector_generation" : generation(R1_VECTOR, R1_VECTOR),
    "r1_vector_conversion" : conversion(R1_VECTOR),
    "r1_vector_execution" : execution(R1_VECTOR),
    "lazy_generation" : generation(LAZY, LAZY),
    "lazy_conversion" : conversion(LAZY),
    "lazy_execution" : execution(LAZY),
  }

def create(args):
  polytope,dim = args.polytope, args.dim[0]
  text,compute = args.text,args.compute
  if not text:
    del TASKS["graph_certif_conversion_text"]
  if not compute:
    del TASKS["graph_certif_execution_compute"]
  name = polytope_name(polytope,dim)
  gen_lrs(polytope,dim)
  make_benchmarks(name,TASKS)

def hirsch(args):
  name = args.which
  make_benchmarks(name,HIRSCH_TASKS)

# --------------------------------------------------------------------
def to_csv(json_paths, tgtfile):
  if len(json_paths) == 0:
    print(f"There is no benchmark to make {tgtfile}")
    return None
  benchmarks = []
  for (name,path) in json_paths:
    with open(path) as stream:
      bench = json.load(stream)
      res = {}
      for fst,vals in bench.items():
        for snd,val in vals.items():
          res[" : ".join([fst,snd])] = val
      benchmarks.append((name,res))
  fieldnames = ["polytope"] + list(benchmarks[0][1].keys())
  with open(tgtfile, "w") as csv_stream:
    writer = csv.DictWriter(csv_stream, fieldnames=fieldnames)
    writer.writeheader()
    for name,res in benchmarks:
      writer.writerow(dict(polytope = name, **res))


def csv_gen(_):
  hirsch_paths = []
  cube_paths = []
  cross_paths = []
  cyclic_paths = []
  permutohedron_paths = []
  for name in os.listdir(DATA_DIR):
    json_path = os.path.join(DATA_DIR,name,f"benchmarks_{name}.json")
    if os.path.exists(json_path):
      if name in HIRSCH_CEX:
        hirsch_paths.append((name,json_path))
      elif name.startswith("cube"):
        cube_paths.append((name,json_path))
      elif name.startswith("cross"):
        cross_paths.append((name,json_path))
      elif name.startswith("cyclic"):
        cyclic_paths.append((name,json_path))
      elif name.startswith("permutohedron"):
        permutohedron_paths.append((name,json_path))
  to_csv(hirsch_paths, HIRSCH + ".csv")
  to_csv(cube_paths, "cube.csv")
  to_csv(cross_paths, "cross.csv")
  to_csv(cyclic_paths, "cyclic.csv")
  to_csv(permutohedron_paths, "permutohedron.csv")


# --------------------------------------------------------------------
def plot(args):
  name = args.name
  csvname = f"{name}.csv" 
  if os.path.exists(csvname):
    with open(csvname) as stream:
      reader = csv.DictReader(stream)
      polytope = []
      lrs = []
      graph_certif = []
      improved = []
      rank1 = []
      pivot = []
      r1_matrix = []
      r1_vector = []
      lazy = []
      for row in reader:
        polytope.append(row['polytope'])
        lrs.append(float(row['lrs : time']))
        graph_certif.append(float(row['graph_certif_execution : vertex_consistent_r.v execution time']))
        improved.append(float(row['improved_execution : improved.v execution time']))
        rank1.append(float(row['rank1_execution : rank1.v execution time']))
        pivot.append(float(row['pivot_execution : pivot.v execution time']))
        r1_matrix.append(float(row['r1_matrix_execution : r1_matrix.v execution time']))
        r1_vector.append(float(row['r1_vector_execution : r1_vector.v execution time']))
        lazy.append(float(row['lazy_execution : lazy.v execution time']))
      


  pp.plot(polytope, lrs, label="lrs")
  pp.plot(polytope, graph_certif, label="graph_certif") 
  pp.plot(polytope, improved, label="improved")
  pp.plot(polytope, rank1, label="rank1")
  pp.plot(polytope, pivot, label="pivot")
  pp.plot(polytope, r1_matrix, label="r1_matrix")
  pp.plot(polytope, r1_vector, label="r1_vector")
  pp.plot(polytope, lazy, label="lazy")
  pp.legend()
  pp.show()



# --------------------------------------------------------------------
DEBUG = r'''From Coq Require Import PArray Uint63.
Require Import debug.

(*{size}*)
Check debug.
Eval vm_compute in debug.[{number}%uint63].
'''

def debug(args):
  param = args.param
  debug_build = os.path.join(CWD,'..','..','_build','default','enumeration','benchmarks','debug')
  if os.path.isdir(debug_build):
    shutil.rmtree(debug_build)

  size = 2**param
  test = [i for i in range(size)]
  res = {'debug' : test}
  tgtdir = os.path.join(CWD,"debug")
  os.makedirs(tgtdir, exist_ok=True)
  dict2bin.dict2bin(tgtdir,res)
  bin2coq.bin2coq("DEBUG",tgtdir)
  with open(os.path.join(tgtdir,"test.v"), "w") as stream:
    stream.write(DEBUG.format(number = size-1, size = size))
  command_call(f"time dune build debug/debug.vo", prefix=TIME_MEM_PREFIX)
  command_call(f"time dune build debug/test.vo", prefix=TIME_MEM_PREFIX)
  

# --------------------------------------------------------------------
def main():
  parser = argp.ArgumentParser()
  subparsers = parser.add_subparsers()
  
  clean_parser = subparsers.add_parser("clean")
  clean_parser.add_argument("dirname", choices=os.listdir(DATA_DIR).remove(".gitignore"))
  clean_parser.add_argument("taskname")
  clean_parser.set_defaults(func=clean)

  create_parser = subparsers.add_parser("create")
  create_parser.add_argument("polytope", choices=POLYTOPES)
  create_parser.add_argument("dim", type=int, nargs=1)
  create_parser.add_argument("--text", action="store_true")
  create_parser.add_argument("--compute", action="store_true")
  create_parser.set_defaults(func=create)

  hirsch_parser = subparsers.add_parser(HIRSCH)
  hirsch_parser.add_argument("which", choices=HIRSCH_CEX)
  hirsch_parser.set_defaults(func=hirsch)

  csv_parser = subparsers.add_parser("csv")
  csv_parser.set_defaults(func=csv_gen)
  
  plot_parser = subparsers.add_parser("plot")
  plot_parser.add_argument("name", type=str)
  plot_parser.set_defaults(func=plot)

  debug_parser = subparsers.add_parser("debug")
  debug_parser.add_argument("param", type=int)
  debug_parser.set_defaults(func=debug)
  
  args = parser.parse_args()
  args.func(args)
  

# --------------------------------------------------------------------
if __name__ == "__main__":
    main()