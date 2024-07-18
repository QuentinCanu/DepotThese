import random as rd
from . import farkas as fk
from sympy.polys.domains  import QQ
from sympy.polys.matrices import DomainMatrix
import fractions as fc

def list_of_gmp_matrix(PM):
    p,q = PM.shape
    res = []
    for j in range(q):
        res.append([str(PM[i,j].element) for i in range(p)])
    return res

def make_dim_full(l_vtx, n):
    while True:
        map_lbl = rd.sample(range(len(l_vtx)), n+1)
        map_lbl.sort()
        M = fk.to_gmp_matrix([list(map(fc.Fraction, l_vtx[i])) for i in list(map_lbl)[1:]])
        N = fk.to_gmp_matrix([list(map(fc.Fraction, l_vtx[map_lbl[0]])) for _ in range(n)])
        Q = M - N
        Q_det = Q.det()
        if Q_det != 0:
            Q_inv = Q.inv()
            Q_res = list_of_gmp_matrix(Q_inv)
            return list(map_lbl)[0], list(map_lbl)[1:], Q_res
        
START_BFS = {"poly20dim21" : 394, "poly23dim24" : 7200}

def common2hirsch(name, dict):
  vertices = dict["l_vtx"]
  n = len(dict["A"][0])
  origin, map_dim, inv_dim = make_dim_full(vertices, n)
  start = START_BFS[name]
  dict["origin"] = origin
  dict["map_dim"] = map_dim
  dict["inv_dim"] = inv_dim
  dict["start"] = start
  return dict
