#! /usr/bin/env python3

# --------------------------------------------------------------------
import argparse as argp
import subprocess as sp
import itertools as it
import os
import re
import time
import math
from scripts import genlrs, lrs2common, common2certif, dict2bin, bin2coq, dict2text, coqjobs, common2hirsch
import csv
import shutil
import json

CWD = os.getcwd()
TIME_MEM_PREFIX = r'TIMEFMT="%E : real time, %M : max memory" && '
HIRSCH_CEX = ["poly20dim21","poly23dim24"]
POLYTOPES = ["cube", "cross", "cyclic", "permutohedron"]
DATA_DIR = os.path.join(CWD,"data")
JOB_DIR = os.path.join(CWD,"jobs")
PARALLEL_DFLT = 10
NO_BENCH = "------"

# --------------------------------------------------------------------
def chunks(lst, n):
    """Yield successive n-sized chunks from lst."""
    for i in range(0, len(lst), n):
        yield lst[i:i + n]

def command_call(command, prefix=""):
  print(command)
  try:
    output = sp.run(prefix + command,
            shell=True, executable="/bin/zsh", check=True,
            capture_output=True, text=True)
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
  return f"{polytope}_{param}_{2*param}" if polytope == "cyclic" else f"{polytope}_{param[0]}"

def dune_name_certif(name, text = False):
  return "_".join([name.upper(),"TEXT" if text else "", "DATA"])

def dune_name_algo(name, algo, compute = False):
  return "_".join([name.upper(),algo.upper(),"CMP" if compute else ""])

# --------------------------------------------------------------------
def gen(polytope, param):
  if polytope not in HIRSCH_CEX:
    if polytope == "cyclic":
      genlrs.generate_lrs(polytope, param, 2*param)
    else:
      print(param)
      genlrs.generate_lrs(polytope, param[0])

# --------------------------------------------------------------------
def compute_lrs(name):
  inefile = os.path.join(DATA_DIR, name, "lrs", name+".ine")
  extfile = os.path.join(DATA_DIR, name, "lrs", name+".ext")
  time, memory = format_time_output(command_call(f"time lrs {inefile} {extfile}",TIME_MEM_PREFIX))
  return {"time" : time, "memory" : memory}

# --------------------------------------------------------------------
def common_generation(name):
  st = time.time()
  dict = lrs2common.lrs2common(name)
  et = time.time()
  certif_path_dir = os.path.join(DATA_DIR,name,"certificates","common")
  os.makedirs(certif_path_dir,exist_ok=True)
  certif_path = os.path.join(certif_path_dir,name+".json")
  with open(certif_path, "w") as stream:
    json.dump(dict,stream)
  return {"time" : et - st}

# --------------------------------------------------------------------
def graph_certif_generation(name):
  common_path_dir = os.path.join(DATA_DIR,name,"certificates","common")
  common_path = os.path.join(common_path_dir,name+".json")
  with open(common_path) as stream:
    common_dict = json.load(stream)
  st = time.time()
  res_dict = common2certif.common2certif(common_dict)
  et = time.time()
  path_dir = os.path.join(DATA_DIR,name,"certificates","graph_certif")
  path = os.path.join(path_dir,name+".json")
  os.makedirs(path_dir,exist_ok=True)
  with open(path,"w") as stream:
    json.dump(res_dict,stream)
  return {"time" : et - st}

# --------------------------------------------------------------------
def conversion(certif_type, text=False):
  def worker(name):
    res = {}
    certif_path = os.path.join(DATA_DIR, name, "certificates", certif_type, name+".json")
    with open(certif_path) as stream:
      certif = json.load(stream)

    binpath = ["data", name, certif_type, "bin_certif"]
    bindir = os.path.join(CWD, *binpath)
    os.makedirs(bindir, exist_ok = True)
    st = time.time()
    bench = dict2bin.dict2bin(bindir,certif)
    et = time.time()
    res["generation of bin certificates"] = {"generation time of bin files" : et - st, "size of bin files" : bench}
    bin2coq.bin2coq(dune_name_certif(name),bindir)
    res["compilation of bin certificates"] = certif_compilation(bindir, *binpath)

    if text:
      textpath = ["data", name, certif_type, "text_certif"]
      textdir = os.path.join(CWD, *textpath)
      os.makedirs(textdir, exist_ok = True)
      dict2text.dict2text(dune_name_certif(name,True),textdir,certif)
      res["compilation of text certificates"] = certif_compilation(textdir, *textpath)
    return res
  return worker

def certif_compilation(tgtdir, *relpath):
  res = {}
  times = []
  max_memory = -math.inf
  files = sorted(os.listdir(tgtdir))
  for file in files:
    if file.endswith(".v"):
      print(f"Compiling {file}")
      rel_path = os.path.join(*relpath,file+"o")
      st = command_call("time dune build " + rel_path,TIME_MEM_PREFIX)
      time, memory = format_time_output(st)
      res[file + " time"] = time
      res[file + " memory"] = memory
      times.append(float(time if time is not None else 0.0))
      max_memory = max(max_memory,float(memory if memory is not None else 0.0))
  res["total time"] = str(math.fsum(times))
  res["max memory"] = str(max_memory)
  return res



# --------------------------------------------------------------------
def graph_certif_execution(name):
  res = {}
  tgtpath = ["data", name, "graph_certif", "standard"]
  tgtdir = os.path.join(CWD, *tgtpath)
  os.makedirs(tgtdir,exist_ok = True)
  jobdir = os.path.join(JOB_DIR,"graph_certif")
  coqjobs.coqjob(name, dune_name_algo(name,"verif"), dune_name_certif(name), "PolyhedraHirschVerif", jobdir, tgtdir)
  res["Execution of the graph verification algorithm"] = job(tgtdir,*tgtpath)

  tgtpath = ["data", name, "graph_certif", "compute"]
  tgtdir = os.path.join(CWD,*tgtpath)
  os.makedirs(tgtdir,exist_ok = True)
  jobdir = os.path.join(JOB_DIR,"graph_certif_compute")
  coqjobs.coqjob(name, dune_name_algo(name,"verif",compute = True), dune_name_certif(name), "PolyhedraHirschVerif", jobdir, tgtdir)
  res["Execution of the graph verification algorithm, with compute"] = job(tgtdir,*tgtpath)
  return res


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
      st = command_call("time dune build " + rel_path,TIME_MEM_PREFIX)
      time, memory = format_time_output(st)
      res[file + " time"] = time
      res[file + " memory"] = memory
      times.append(float(time if time is not None else 0.0))
      max_memory = max(max_memory,float(memory if memory is not None else 0.0))
  res["total time"] = str(math.fsum(times))
  res["max memory"] = str(max_memory)
  return res
# --------------------------------------------------------------------
def diameter_execution(name):
  res = {}
  tgtpath = ["data", name, "diameter"]
  tgtdir = os.path.join(CWD,*tgtpath)
  os.makedirs(tgtdir,exist_ok = True)
  jobdir = os.path.join(JOB_DIR,"diameter")
  coqjobs.coqjob(name, dune_name_algo(name,"diameter"), dune_name_certif(name), "PolyhedraHirsch", jobdir, tgtdir)
  res["Execution of the diameter algorithm"] = job(tgtdir,*tgtpath)
  return res

# --------------------------------------------------------------------
def hirsch_generation(name):
  certif_path = os.path.join(DATA_DIR, name, "certificates", "common", name+".json")
  with open(certif_path) as stream:
    certif = json.load(stream)
  st = time.time()
  certif = common2certif.common2certif(certif)
  certif = common2hirsch.common2hirsch(name,certif)
  et = time.time()
  path_dir = os.path.join(DATA_DIR,name,"certificates","hirsch")
  path = os.path.join(path_dir,name+".json")
  os.makedirs(path_dir,exist_ok=True)
  with open(path,"w") as stream:
    json.dump(certif,stream)
  return {"time" : et - st}

def hirsch_execution(name):
  res = {}
  tgtpath = ["data", name, "hirsch", "standard"]
  tgtdir = os.path.join(CWD,*tgtpath)
  os.makedirs(tgtdir,exist_ok = True)
  jobdir = os.path.join(JOB_DIR,"hirsch")
  coqjobs.coqjob(name, dune_name_algo(name,"hirsch"), dune_name_certif(name), "PolyhedraHirschVerif", jobdir, tgtdir)
  res["Counterexample verification to the Hirsch Conjecture"] = job(tgtdir,*tgtpath)
  return res

# --------------------------------------------------------------------
# --------------------------------------------------------------------
def make_benchmarks(name,taskdict):
  benchmarks_path = os.path.join(DATA_DIR,name,f"benchmarks_{name}.json")
  if os.path.exists(benchmarks_path):
    with open(benchmarks_path) as stream:
      benchmarks = json.load(stream)
  else:
    benchmarks = dict(zip(taskdict,it.repeat(None)))
  for task in taskdict.keys():
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
  "common_generation" : common_generation,
  "graph_certif_generation" : graph_certif_generation,
  "graph_certif_conversion" : conversion("graph_certif", text=True),
  "graph_certif_execution" : graph_certif_execution,
  "diameter_execution" : diameter_execution,
}

HIRSCH_TASKS = {
    "lrs" : compute_lrs,
    "common_generation" : common_generation,
    "hirsch_generation" : hirsch_generation,
    "hirsch_conversion" : conversion("hirsch"),
    "hirsch_execution" : hirsch_execution
  }

def create(args):
  polytope,param = args.polytope, args.param
  name = polytope_name(polytope,param)
  gen(polytope,param)
  make_benchmarks(name,TASKS)


# --------------------------------------------------------------------
def clean(args):
  for dir in os.listdir(DATA_DIR):
    dir_path = os.path.join(DATA_DIR, dir)
    if os.path.isdir(dir_path):
      if dir not in HIRSCH_CEX:
        shutil.rmtree(dir_path)
      else:
        for subdir in os.listdir(dir_path):
          if os.path.isdir(os.path.join(dir_path,subdir)) and subdir != "lrs":
            shutil.rmtree(os.path.join(dir_path,subdir))
          elif subdir.endswith(".json"):
            os.remove(os.path.join(dir_path,subdir))
          else:
            path_ext = os.path.join(dir_path,subdir,dir+".ext")
            if os.path.exists(path_ext):
              os.remove(path_ext)
  command_call("dune clean")
  command_call("dune build " + os.path.join("..", "theories"))

# --------------------------------------------------------------------
def hirsch(args):
  name = args.which
  make_benchmarks(name,HIRSCH_TASKS)




# --------------------------------------------------------------------
def main():
  parser = argp.ArgumentParser()
  subparsers = parser.add_subparsers()
  
  create_parser = subparsers.add_parser("create")
  create_parser.add_argument("polytope", choices=POLYTOPES)
  create_parser.add_argument("param", type=int, nargs=1)
  create_parser.set_defaults(func=create)

  clean_parser = subparsers.add_parser("clean")
  clean_parser.set_defaults(func=clean)

  hirsch_parser = subparsers.add_parser("hirsch")
  hirsch_parser.add_argument("which", choices=HIRSCH_CEX)
  hirsch_parser.set_defaults(func=hirsch)

  args = parser.parse_args()
  args.func(args)
  

# --------------------------------------------------------------------
if __name__ == "__main__":
    main()










# # --------------------------------------------------------------------

# # --------------------------------------------------------------------
# def command_call(command, prefix=""):
#   output = sp.run(prefix + command,
#             shell=True, executable="/bin/zsh", check=True,
#             capture_output=True, text=True)
#   print(output.stdout, output.stderr)
#   return output.stderr

# # --------------------------------------------------------------------
# def format_time_output(st,megabytes):
#   findit = re.search(r"(?P<time>\d+)[,.](?P<mtime>\d+)s.+, (?P<memory>\d+)", st)
#   time, mtime = findit.group("time"), findit.group("mtime")
#   memory = float(findit.group("memory"))
#   if megabytes:
#     memory /= 1000
#   return f"{time}.{mtime}", str(memory)

# # --------------------------------------------------------------------
# def clean_coq(**kwargs):
#   command_call("dune clean")

# def theories(**kwargs):
#   parallel = kwargs["parallel"]
#   time, _ = format_time_output(command_call(f"time dune build -j {PARALLEL_DFLT if parallel is None else parallel} " + os.path.join("..","theories"),TIME_MEM_PREFIX),kwargs["megabytes"])
#   return time

# # --------------------------------------------------------------------
# def polytopes(**kwargs):
#   profile = kwargs["profile"]
#   poly_dict = POLYTOPES[profile]
#   for poly_name, (min,max) in poly_dict.items():
#     for i in range(min,max+1):
#       poly = poly_name + "_" + str(i) + (f"_{2*i}" if poly_name == "cyclic" else "")
#       print(poly)
#       yield poly
#   for hirsch_cex in HIRSCH_CEX_PROFILE[profile]:
#     print(hirsch_cex)
#     yield hirsch_cex

# # --------------------------------------------------------------------

# def lrs(**kwargs):
#   res = []
#   for name in polytopes(**kwargs):
#     res.append({"polytope" : name})
#     inefile = core.resource(name,"lrs",name+".ine")
#     extfile = core.resource(name,"lrs",name+".ext")
#     time, memory = format_time_output(command_call(f"time lrs {inefile} {extfile}",TIME_MEM_PREFIX), kwargs["megabytes"])
#     res[-1]["time"], res[-1]["memory"] = time, memory
#   return res

# # --------------------------------------------------------------------
# def certificates(**kwargs):
#   res = []
#   compute = kwargs["compute"]
#   text = kwargs["text"]
#   for name in polytopes(**kwargs):
#     res.append({"polytope" : name})
#     hirsch = name in HIRSCH_CEX
#     st = time.time()
#     dict = lrs2dict.lrs2dict(name,hirsch)
#     et = time.time()
#     res[-1]["time"] = f"{et - st:.2f}"
#     if text:
#       res2 = dict2text.dict2text(name,dict,compute)
#     else:
#       res2 = dict2bin.dict2bin(name,dict)
#       bin2coq.main(name)
#     coqjobs.main(name,"Validation",compute)
#     coqjobs.main(name,"Validation_Compute",compute)
#     if name in ["poly20dim21", "poly23dim24"]:
#       coqjobs.main(name,"Hirsch", compute)
#       coqjobs.main(name,"Exact", compute)
#     else:
#       coqjobs.main(name,"Diameter", compute)
#     res[-1] = {**res[-1], **res2}
#   return res

# # --------------------------------------------------------------------
# def compilation(**kwargs):
#   res = []
#   parallel = kwargs["parallel"]
#   for name in polytopes(**kwargs):
#     res.append({"polytope" : name})
#     coqdir = core.resource(name,"coq")
#     if parallel is None:
#       times = []
#       max_memory = -math.inf
#       files = sorted(os.listdir(coqdir))
#       for file in files:
#         if file.endswith(".v"):
#           print(file)
#           rel_path = os.path.join("data",name,"coq",file+"o")
#           st = command_call("time dune build " + rel_path,TIME_MEM_PREFIX)
#           time, memory = format_time_output(st, kwargs["megabytes"])
#           res[-1][file + " time"] = time
#           res[-1][file + " memory"] = memory
#           times.append(float(time))
#           max_memory = max(max_memory,float(memory))
#       res[-1]["total time"] = str(math.fsum(times))
#       res[-1]["max memory"] = str(max_memory)
#     else:
#       rel_path = os.path.join("data",name,"coq")
#       st = command_call(f"time dune build -j {parallel} " + rel_path, TIME_MEM_PREFIX)
#       time, memory = format_time_output(st, kwargs["megabytes"])
#       res[-1]["total time"] = time
#       res[-1]["max memory"] = memory
#   return res

# def job(job):
#   def worker(**kwargs):
#     res = []
#     parallel = kwargs["parallel"]
#     for name in polytopes(**kwargs):
#       jobdir = core.resource(name,f"coq_{job}")
#       if not os.path.exists(jobdir):
#         continue
#       res.append({"polytope" : name})
#       if parallel is None:
#         times = []
#         max_memory = -math.inf
#         datas = list(os.listdir(jobdir))
#         datas.sort()
#         datas.sort(key=f"{job}.v".__eq__)
#         for file in datas:
#           if file.endswith(".v"):
#             print(file)
#             rel_path = os.path.join("data",name,f"coq_{job}",file+"o")
#             st = command_call("time dune build " + rel_path,TIME_MEM_PREFIX)
#             time, memory = format_time_output(st, kwargs["megabytes"])
#             res[-1][file + " time"] = time
#             res[-1][file + " memory"] = memory
#             times.append(float(time))
#             max_memory = max(max_memory,float(memory))
#         res[-1]["total time"] = str(math.fsum(times))
#         res[-1]["max memory"] = str(max_memory)
#       else:
#         rel_path = os.path.join("data",name,f"coq_{job}")
#         st = command_call(f"time dune build -j {parallel} " + rel_path, TIME_MEM_PREFIX)
#         time, memory = format_time_output(st, kwargs["megabytes"])
#         res[-1]["total time"] = time
#         res[-1]["max memory"] = memory
#     return res
#   return worker

# # --------------------------------------------------------------------
# def clean_data(**kwargs):
#   for name in polytopes(**kwargs):
#     if name not in HIRSCH_CEX:
#       shutil.rmtree(core.resource(name))
#     else:
#       for file in os.listdir(core.resource(name)):
#         if file != "lrs":
#           shutil.rmtree(core.resource(name,file))
#         else:
#           path_ext = core.resource(name,file,f"{name}.ext")
#           if os.path.exists(path_ext):
#             os.remove(path_ext)

# def clean_benchmarks(**kwargs):
#   for name in os.listdir(BENCH_DIR):
#     if not name.startswith("."):
#       shutil.rmtree(os.path.join(BENCH_DIR, name))


# # --------------------------------------------------------------------
# def gen(**kwargs):
#   polytopes = POLYTOPES[kwargs["profile"]]
#   for poly, (n, N) in polytopes.items():
#     for k in range(n, N+1):
#       if poly == "cyclic":
#         genlrs.generate_lrs(poly, k, 2*k)
#       else:
#         genlrs.generate_lrs(poly, k)
# # --------------------------------------------------------------------
# def writer(stream):
#   def output(st):
#     print(st,file=stream)
#   return output

# def sort_res(res):
#   def key(elt):
#     name = elt["polytope"]
#     pref_match = re.search(f"([^_]+)_(\d+)", name)
#     if pref_match is not None:
#       return (pref_match.group(1), int(pref_match.group(2)))
#     else:
#       return (name,0)
#   return sorted(res, key=key)


# def bench2csv(kind,res,compute,text,parallel):
#   taskdir = os.path.join(BENCH_DIR,kind)
#   os.makedirs(taskdir,exist_ok=True)
#   file_name = f"{kind}_" + (f"{compute}_" if compute == "compute" else "") + ("text_" if text else "") + (f"parallel_{parallel}_" if parallel is not None else "") + time.strftime("%m-%d-%H-%M-%S") + (".log" if kind == "theories" else ".csv")
#   taskfile = os.path.join(taskdir, file_name)
#   with open(taskfile, "w", newline='') as stream:
#     output = writer(stream)
#     if kind == "theories":
#       output(f"Compilation of theories time : {res}")
#     else:
#       if res != []:
#         idx = max(range(len(res)), key = (lambda i : len(res[i])))
#         measured = list(res[idx].keys())
#         csvwriter = csv.DictWriter(stream,measured,restval='-----')
#         res = sort_res(res)
#         csvwriter.writeheader()
#         csvwriter.writerows(res)

# def one_task(kind, functi, **kwargs):
#   bench2csv(kind,functi(**kwargs),kwargs["compute"],kwargs["text"],kwargs["parallel"])

# def all_tasks(*args,**kwargs):
#   gen(**kwargs)
#   for kind in TASK.keys():
#     print(f"Generating {kind} benchmark")
#     one_task(kind,**kwargs)
# # --------------------------------------------------------------------

# TASK = { 
#     "theories" : theories,
#     "lrs" : lrs,
#     "certificates" : certificates,
#     "compilation" : compilation,
#     "validation" : job("Validation"),
#     "diameter" : job("Diameter"),
#     "hirsch" : job("Hirsch"),
#     "exact" : job("Exact")
#   }

# SPECIFIC = {"validation_compute" : job("Validation_Compute")}

# ADDITIONAL = {"clean_coq" : clean_coq, "clean_data" : clean_data, "clean_benchmarks" : clean_benchmarks,  "all" : all_tasks, "gen" : gen}

# def optparser():
#   parser = argp.ArgumentParser(
#     description="Launch the selected benchmark")

#   parser.add_argument(dest="kind", help="The kind of execution required", 
#                       choices=list(TASK.keys()) + list(SPECIFIC.keys()) + list(ADDITIONAL.keys()))
  
#   parser.add_argument("-c", "--compute", dest="compute", help=r"vm_compute is the reduction strategy used by default, this option allows to perform using compute instead.", action="store_const", const="compute", default="vm_compute")
#   parser.add_argument("-t", "--text", dest="text", help=r"Certificates are generated as binary files by default. This option generates plain text .v files instead.", action="store_true")
#   parser.add_argument("-j", "--jobs", dest="parallel", help="The compilation of Coq files by dune is done sequentially. This option calls dune on the folder instead. It is possible to add the number of task that can be simultaneously done.", nargs="?", const=PARALLEL_DFLT, default=None)
#   parser.add_argument("-b", "--megabytes", dest="megabytes", help="Depending on the OS, the memory evaluated by the commands is either in kilobytes or in megabytes. This option divides by 1000 the correpsonding outputs, to deal with megabytes.", action="store_true")
#   parser.add_argument("-p", "--profile", dest="profile", help=r"To deal with a specific subset of polytopes", choices=list(POLYTOPES.keys()), default="default")

#   return parser


# def main():
#   args = optparser().parse_args()
#   kind = args.kind
#   compute = args.compute
#   text = args.text
#   parallel = args.parallel
#   profile = args.profile
#   megabytes = args.megabytes
#   kwargs = {"compute" : compute, "text" : text, "parallel" : parallel, "megabytes" : megabytes, "profile" : profile}
#   if kind in TASK:
#     one_task(kind,TASK[kind],**kwargs)
#   if kind in SPECIFIC:
#     one_task(kind,SPECIFIC[kind],**kwargs)
#   if kind in ADDITIONAL:
#     ADDITIONAL[kind](**kwargs)

# # --------------------------------------------------------------------
# if __name__ == "__main__":
#     main()