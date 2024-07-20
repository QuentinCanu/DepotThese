#! /usr/bin/env python3

import json, os, time
import fractions as fc
import argparse as argp
import math, fractions, random as rd
import networkx as nx
import tqdm
import random as rd
from . import farkas as fk
from . import core

import sympy as sym
from sympy.polys.domains  import QQ
from sympy.polys.matrices import DomainMatrix

# Common functions
# -------------------------------------------------------------------
def bigq(x):
    return str(x)

# Extract polyhedron information from lrs files
# -------------------------------------------------------------------
def get_polyhedron_from_lrs(name):
    input = core.resource(name,"lrs",f"{name}.ine")
    with open(input, 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx[mx.index('begin')+2:mx.index('end')]]
        Po = [list(map(fc.Fraction, xs)) for xs in mx]

    Po = [([x for x in line[1:]], -line[0]) for line in Po]
    Po = [(list(map(bigq, p1)), bigq(p2)) for p1,p2 in Po]
    A,b = zip(*Po)
    return A, b

def get_bases_from_lrs(name):
    input = core.resource(name,"lrs",f"{name}.ext")
    with open(input, 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx[mx.index('begin')+2:mx.index('end')]]
        mx = [(x[x.index('facets')+1:x.index('det=')-1]) if x[0]!="1" else x[1:] for x in mx]
        couples = [(mx[i], mx[i+1]) for i in range(0,len(mx),2)]
        couples = [((list(map((lambda x : int(x) - 1), b))) ,v) for b,v in couples]
        couples = sorted(couples,key=(lambda x : x[0]))
    return zip(*couples)


# -------------------------------------------------------------------

def list_of_gmp_matrix(PM):
    p,q = PM.shape
    res = []
    for j in range(q):
        res.append([str(PM[i,j].element) for i in range(p)])
    return res

# Construct the graph of lex feasible bases
# -------------------------------------------------------------------

def get_lex_graph(m,n,bases):
    graph = [set() for _ in bases]
    bases_dic = {frozenset(elt) : i for i,elt in enumerate(bases)}
    reg = [0 for _ in bases]
    for kI,I in enumerate(tqdm.tqdm(bases,desc="Computing the graph of the lex-feasible bases : ")):
        I_set = set(I)
        s = 0
        while reg[kI] < n:
            Is = I[s]
            for r in range(m):
                if r not in I_set:
                    J = I_set - {Is} | {r}
                    if frozenset(J) in bases_dic:
                        kJ = bases_dic[frozenset(J)]
                        if kJ not in graph[kI]:
                            graph[kI].add(kJ)
                            graph[kJ].add(kI)
                            reg[kI]+=1
                            reg[kJ]+=1
                            break
            s += 1
    return [sorted(elt) for elt in graph]

# Visit the graph in order to construct the values required by the algorithm in the correct order
# -------------------------------------------------------------------

def get_entering_leaving(I,J):
    I_set, J_set = set(I), set(J)
    IJ = I_set & J_set
    s,r = (I_set - IJ).pop(), (J_set - IJ).pop()
    return (r, s)

def get_initial_inverse(A,I):
    A_I = [A[i] for i in I]
    gmp_A_I = fk.to_gmp_matrix(A_I)
    A_I_inv = gmp_A_I.inv()
    res = [None for _ in A]
    for i in range(len(I)):
        res[I[i]] = fk.gmp_matrix_col(A_I_inv, i)
    return res

def rank_1_update(A,inv,I,J):
    r,s = get_entering_leaving(I,J)
    A_r = fk.to_gmp_matrix([A[r]])
    inv_s = inv[s]
    Ars = ((A_r * inv_s)[0,0])
    res = [None for _ in A]
    for k in J:
        if k != r:
            res[k] = inv[k] - (((A_r * inv[k])[0,0] // Ars) * inv_s)
        else:
            res[r] = inv[s] / Ars
    return res
        
def get_inverses(A,bases,graph,root=0):
    graph_lex = nx.Graph({i:edges for i,edges in enumerate(graph)})
    inverses = [None for _ in bases]
    inverses[root] = get_initial_inverse(A,bases[root])
    for (node,pred) in tqdm.tqdm(nx.bfs_predecessors(graph_lex,root), desc="Computation of the labels of the lex-feasible bases graph : "):
        inverses[node] = rank_1_update(A,inverses[pred],bases[pred],bases[node])
    return [[list_of_gmp_matrix(col)[0] for col in inv if col is not None] for inv in inverses]

# Construct the graph of vertices + certificates related to the image graph
# -------------------------------------------------------------------

def get_lbl_vtx(vertices):
    vtx_list = sorted(set([tuple(map((lambda x : fractions.Fraction(x)), l)) for l in vertices]))
    return [list(map(str,elt)) for elt in vtx_list]

def get_morph(bases, dupl, vertices):
    bas2vtx = {frozenset(base) : vtx for (base,vtx) in zip(bases,dupl)}
    morph, morph_inv = [None for _ in bases], [None for _ in vertices]
    aux = {tuple(v) : i for (i,v) in enumerate(vertices)}
    for i,base in enumerate(bases):
        v = bas2vtx[frozenset(base)]
        j = aux[tuple(v)]
        morph[i] = j
        morph_inv[j] = i
    return morph, morph_inv


def get_graph_vtx(graph_lex, morf, length_vtx):
    graph = [[] for i in range(length_vtx)]
    for i in range(len(graph_lex)):
        tgt_i = morf[i]
        for j in graph_lex[i]:
            tgt_j = morf[j]
            if tgt_i != tgt_j and tgt_j not in graph[tgt_i]:
                graph[tgt_i].append(tgt_j)
    return [sorted(x) for x in graph]

def get_edge_inv(G_lex, G_simpl, morf):
    edge_inv = [[None for j in range(len(G_simpl[i]))] for i in range(len(G_simpl))]
    for i in range(len(G_lex)):
        for j in range(len(G_lex[i])):
            nei = G_lex[i][j]
            if morf[i] != morf[nei]:
                j_ = next(i for i,v in enumerate(G_simpl[morf[i]]) if v == morf[nei])
                edge_inv[morf[i]][j_] = (i,nei)
    return edge_inv

# Get final certificates (Farkas)
# -------------------------------------------------------------------
def get_farkas_cert(A, m, n):
    A = fk.to_gmp_matrix(A).transpose()
    cert_pos, cert_neg = [], []
    for k in range(n):
        cert_pos.append(list(map(bigq,fk.farkas_gen(A, n, m, k))))
        cert_neg.append(list(map(bigq,fk.farkas_gen(-A, n, m, k))))
    return cert_pos, cert_neg


# Main function, write a json file with one certificate per entry
# -------------------------------------------------------------------
def optparser():
    parser = argp.ArgumentParser(description='Extract json data from polyhedron data')
    parser.add_argument('name', help="the name of the polyhedron to be extracted")
    parser.add_argument('--hirsch', help="option adding the certificates in order to disprove Hirsch conjecture", action="store_true")
    return parser

# -------------------------------------------------------------------
def lrs2common(name):

    # Compute everything
    A,b = get_polyhedron_from_lrs(name)
    bases, vertices = get_bases_from_lrs(name)
    g_lex = get_lex_graph(len(A), len(A[0]), bases)
    inverses = get_inverses(A,bases,g_lex)
    print(f"Computation of the certificates of boundedness : ", end="", flush=True)
    st = time.time()
    bound_pos, bound_neg = get_farkas_cert(A,len(A),len(A[0]))
    et = time.time()
    print(f"{et - st:.2f}s")

    tgtdict =   {
                "A"         : A,
                "b"         : b,
                "bases"     : bases,
                "vertices"  : vertices,
                "g_lex"     : g_lex,
                "inverses"  : inverses,
                "bound_pos" : bound_pos,
                "bound_neg" : bound_neg
                }
    # tgtdict["A"] = the matrix corresponding to the polytope
    # tgtdict["b"] = the vector corresponding to the polytope

    # tgtdict["bases"] = the list of the lex-feasible bases of the polytope, sorted in lexicographic order
    # tgtdict["vertices"] = the list of the associated vertices, in the same order as the bases
    # tgtdict["inverses"] = the list of the associated inverses, i.e, A_I^{-1}, in the same order as the bases I

    # tgtdict["g_lex"] = the adjacency list of the lex-graph

    # tgtdict["bound_pos"] = farkas certificate (u) such that u_i^T A = \delta_i 
    # tgtdict["bound_neg"] = farkas certificate (u) such that u_i^T A = - \delta_i 
    return tgtdict