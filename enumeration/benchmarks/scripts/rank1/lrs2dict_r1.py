#! /usr/bin/env python3

import json, os
import fractions as fc
import argparse as argp
import math, fractions, random as rd
from .. import farkas as fk

import sympy as sym
from sympy.polys.domains  import QQ
from sympy.polys.matrices import DomainMatrix

CWD = os.getcwd()
DATA_DIR = os.path.join(CWD,"data")

# Common functions
# -------------------------------------------------------------------
def bigq(x):
    return str(x)

# Extract polyhedron information from lrs files
# -------------------------------------------------------------------
def get_polyhedron_from_lrs(name):
    input = os.path.join(DATA_DIR,name,"lrs",f"{name}.ine")
    with open(input, 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx[mx.index('begin')+2:mx.index('end')]]
        Po = [list(map(fc.Fraction, xs)) for xs in mx]

    Po = [([x for x in line[1:]], -line[0]) for line in Po]
    Po = [(list(map(bigq, p1)), bigq(p2)) for p1,p2 in Po]
    A,b = zip(*Po)
    return A, b

def get_bases_from_lrs(name):
    input = os.path.join(DATA_DIR,name,"lrs",f"{name}.ext")
    with open(input, 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx[mx.index('begin')+2:mx.index('end')]]
        mx = [(x[x.index('facets')+1:x.index('det=')-1], x[x.index('det=')+1]) if x[0]!="1" else x[1:] for x in mx]
        couples = [(mx[i], mx[i+1]) for i in range(0,len(mx),2)]
        couples = [(((list(map((lambda x : int(x) - 1), b))), d) ,v) for (b,d),v in couples]
        bas2vtx = {frozenset(b) : v for ((b,_),v) in couples}
        bas2det = {frozenset(b) : d for ((b,d),_) in couples}
    return sorted([b for (b,_),_ in couples]), bas2vtx, bas2det

#rewrite A and b to be integer matrices
# -------------------------------------------------------------------
def to_gmp_matrix(m):
    M = sym.Matrix(m)
    c = M.shape
    M0 = [[QQ(M[i,j].p, M[i,j].q) for j in range(c[1])] for i in range(c[0])]
    res = DomainMatrix(M0, c, QQ)
    return res

def list_of_gmp_matrix(PM):
    PM = PM.to_Matrix()
    (p,q)=PM.shape
    res = []
    for j in range(q):
        res.append([bigq(fc.Fraction(PM[k,j].p, PM[k,j].q)) for k in range(p)])
    return res    

# Compute the initial basing point from which we compute our vertex certification
# -------------------------------------------------------------------

# def get_idx(bases, bas2det):
#     min = math.inf
#     idx = 0
#     # for i in range(len(bases)):
#     #     bas = bases[i]
#     #     det = fc.Fraction(bas2det[frozenset(bas)])
#     #     if det < min:
#     #         min = det
#     #         idx = i
#     return idx

def get_initial_basing_point(A,b,base):
    A_I = [A[i] for i in base]
    b_I = [b[i] for i in base]
    gmp_A_I, gmp_b_I = to_gmp_matrix(A_I), to_gmp_matrix(b_I)
    x_I = gmp_A_I.lu_solve(gmp_b_I)
    inv = gmp_A_I.inv()
    # det = gmp_A_I.det()
    return (list_of_gmp_matrix(x_I)[0], list_of_gmp_matrix(inv))

# Construct the graph of lex feasible bases + order of construction
# -------------------------------------------------------------------
def get_lex_graph(bases,idx, m, n):
    bases_dic = {frozenset(base) : i for (i,base) in enumerate(bases)}
    graph = [set() for _ in range(len(bases))]
    order = []
    pred = [(0,0,0) for _ in range(len(bases))]
    visited = {i : False for i in bases_dic.keys()}
    visited[frozenset(bases[idx])] = True
    queue = [idx]
    pointer = 0
    while True:
        if pointer >= len(queue):
            break
        idx_base = queue[pointer]
        order.append(idx_base)
        reg = len(graph[idx_base])
        if reg < n:
            base = bases[idx_base]
            base_set = set(base)
            for s in range(len(bases[idx_base])):
                for r in range(m):
                    if r not in base_set:
                        nei_set = frozenset(base_set - {base[s]} | {r})
                        if nei_set in bases_dic:
                            idx_nei = bases_dic[nei_set]
                            graph[idx_base].add(idx_nei)
                            if not visited[nei_set]:
                                visited[nei_set] = True
                                queue.append(idx_nei)
                                pred[idx_nei] = (idx_base,r,s)
        pointer += 1
    return [sorted(elt) for elt in graph], order[1:], pred

# Construct the graph of vertices + certificates related to the image graph
# -------------------------------------------------------------------
def get_unsrt_vtx(bases,bas2vtx):
    vtx_list = [None for _ in bases]
    for i in range(len(bases)):
        bas = bases[i]
        vtx = bas2vtx[frozenset(bas)]
        vtx_list[i] = vtx
    return vtx_list


# Main function, write a json file with one certificate per entry
# -------------------------------------------------------------------
def optparser():
    parser = argp.ArgumentParser(description='Extract json data from polyhedron data')
    parser.add_argument('name', help="the name of the polyhedron to be extracted")
    return parser

# -------------------------------------------------------------------
def lrs2dict(name):

    # Compute everything
    A,b = get_polyhedron_from_lrs(name)
    bases, bas2vtx, bas2det = get_bases_from_lrs(name)
    idx = 0
    x_I, inv = (get_initial_basing_point(A,b,bases[idx]))
    m,n = len(A), len(A[0])
    graph_lex, order, pred = get_lex_graph(bases,idx,m,n)
    # unsrt_vtx = get_unsrt_vtx(bases, bas2vtx)


    # Store in a dictionnary

    tgtjson = {}
    tgtjson['A'] = A
    tgtjson['b'] = b
    tgtjson['bases'] = bases
    tgtjson['idx_r1'] = idx
    tgtjson['x_I_r1'] = x_I
    tgtjson['inv_r1'] = inv
    # tgtjson['det'] = det
    tgtjson['order_r1'] = order
    tgtjson['pred_r1'] = pred
    # tgtjson['unsrt_vtx'] = unsrt_vtx
    return tgtjson