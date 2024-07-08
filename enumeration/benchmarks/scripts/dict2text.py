#! /usr/bin/env python3

# --------------------------------------------------------------------
import os

# --------------------------------------------------------------------
DUNE = r'''
(coq.theory
 (name {name})
 (flags -w -ambiguous-paths
        -w -notation-overridden
        -w -redundant-canonical-projection
        -w -projection-no-head-constant))
 (include_subdirs qualified)
'''.lstrip()

IMPORT = r'''
Require Import Uint63 PArray.
From Bignums Require Import BigQ.

(* -------------------------------------------------------------------- *)
Local Open Scope array_scope.
Local Notation int63 := Uint63.int.
'''.lstrip()

# --------------------------------------------------------------------
def printer(stream):
  def output(x):
    print(x,file=stream)
  return output

# --------------------------------------------------------------------
def bigQ2text(a):
  return a.replace('/', '#')

def int632text(a):
  return str(a)

def array2text(elt2text,dflt,scope):
  def job(a):
    return "[| " + "; ".join([elt2text(elt) for elt in a]) + f"|{dflt}|]{scope}"
  return job

def couple2text(elt12text, elt22text):
  def job(a):
    return "(" + elt12text(a[0]) + ", " + elt22text(a[1]) + ")"
  return job

# --------------------------------------------------------------------
default_int_arr = "[|0%uint63|0%uint63|]"
default_bigQ_arr = "[|0%bigQ|0%bigQ|]"
default_bigQ_mx = f"[|{default_bigQ_arr}|{default_bigQ_arr}|]"
default_lbl_lex = f"({default_int_arr},{default_bigQ_mx})"
default_edge_inv = "[|(0,0)|(0,0)|]"
bigQ_scope = "%bigQ"
int63_scope = "%uint63"

TYPE = dict(
    A        = 'array (array bigQ)',
    b         = 'array bigQ',
    l_lex   = 'array (array int63 * array (array bigQ))',
    l_vtx = 'array (array bigQ)',
    g_lex     = 'array (array int63)',
    g_vtx     = 'array (array int63)',
    morph      = 'array int63',
    morph_inv  = 'array int63',
    edge_inv  = 'array (array (int63 * int63))',
    bound_pos  = 'array (array bigQ)',
    bound_neg  = 'array (array bigQ)',
    origin    = 'int63',
    start     = 'int63',
    map_dim   = 'array int63',
    inv_dim   = 'array (array bigQ)',
)

# DESCRIPTORS = dict(
#     A        = '[[Q]]',
#     b       = '[Q]',
#     l_lex   = '[([I],[[Q]])]',
#     l_vtx = '[[Q]]',
#     g_lex     = '[[I]]',
#     g_vtx   = '[[I]]',
#     morph      = '[I]',
#     morph_inv  = '[I]',
#     edge_inv  = '[[(I,I)]]',
#     bound_pos  = '[[Q]]',
#     bound_neg  = '[[Q]]',
#     origin    = 'I',
#     start     = 'I',
#     map_dim   = '[I]',
#     inv_dim   = '[[Q]]',
# )

TEXT = dict(
  A = array2text(array2text(bigQ2text,"0",""),default_bigQ_arr,bigQ_scope),
  b = array2text(bigQ2text,"0",bigQ_scope),
  l_lex = array2text(
    couple2text(
      array2text(int632text, "0",int63_scope), 
      array2text(
        array2text(bigQ2text,"0",""),default_bigQ_arr,bigQ_scope)),default_lbl_lex,""),
  l_vtx = array2text(array2text(bigQ2text,"0",""),default_bigQ_arr,bigQ_scope),
  g_lex = array2text(array2text(int632text,"0",""),default_int_arr,int63_scope),
  g_vtx = array2text(array2text(int632text,"0",""),default_int_arr,int63_scope),
  morph = array2text(int632text,"0",int63_scope),
  morph_inv = array2text(int632text,"0",int63_scope),
  edge_inv = array2text(array2text(couple2text(int632text,int632text),"(0,0)",""),default_edge_inv,int63_scope),
  bound_pos = array2text(array2text(bigQ2text,"0",""),default_bigQ_arr,bigQ_scope),
  bound_neg = array2text(array2text(bigQ2text,"0",""),default_bigQ_arr,bigQ_scope),
  origin = int632text,
  start = int632text,
  map_dim = array2text(int632text,"0",int63_scope),
  inv_dim = array2text(array2text(bigQ2text,"0",""),default_bigQ_arr,bigQ_scope)
)
# --------------------------------------------------------------------

def dict2text(duneName, tgtdir, contents):
  res = {}
  for key, value in contents.items():
    if key not in TYPE.keys():
      print("Error, dictionary contains invalid data")
      exit(1)
    tgtfile = os.path.join(tgtdir, f"{key}.v")
    with open(tgtfile, "w") as stream:
      output = printer(stream)
      stream.write(IMPORT)
      output(f"Definition {key} : {TYPE[key]} := Eval vm_compute in")
      output(TEXT[key](value) + ".")
    res[f"Size of {key}.v"] = float(os.path.getsize(tgtfile))
  with open(os.path.join(tgtdir, "dune"), "w") as stream:
        stream.write(DUNE.format(name = duneName))
  return res