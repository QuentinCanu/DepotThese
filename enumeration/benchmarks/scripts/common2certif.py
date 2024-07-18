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


# -------------------------------------------------------------------
def get_lex_labels(bases,vertices,inverses,m,n):
    res = []
    for base,vertex,inverse in zip(bases,vertices,inverses):
      in_base = set(base)
      pert = [["0" for _ in range(n)]for j in range(m)]
      for k in range(len(base)):
        pert[base[k]] = [str(-fc.Fraction(elt)) for elt in inverse[k]]
      res.append((base,[vertex] + pert))
    return res
        
        
# -------------------------------------------------------------------
def get_morph_and_lbl_vtx(bases, vertices):
    bas2vtx = {frozenset(base) : vtx for (base,vtx) in zip(bases,vertices)}
    undup = set([tuple(elt) for elt in vertices])
    lbl_vtx = sorted(undup, key=lambda x : [fc.Fraction(elt) for elt in x])
    morph, morph_inv = [None for _ in bases], [None for _ in lbl_vtx]
    aux = {tuple(v) : i for (i,v) in enumerate(lbl_vtx)}
    for i,base in enumerate(bases):
        v = bas2vtx[frozenset(base)]
        j = aux[tuple(v)]
        morph[i] = j
        morph_inv[j] = i
    return morph, morph_inv, lbl_vtx

def get_graph_vtx(graph_lex, morph, length_vtx):
    graph = [[] for i in range(length_vtx)]
    for i in range(len(graph_lex)):
        tgt_i = morph[i]
        for j in graph_lex[i]:
            tgt_j = morph[j]
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

# -------------------------------------------------------------------
def common2certif(common):
    res = {}
    res["A"] = common["A"]
    res["b"] = common["b"]
    res["bound_pos"] = common["bound_pos"]
    res["bound_neg"] = common["bound_neg"]
    res["g_lex"] = common["g_lex"]

    m = len(common["A"])
    n = len(common["A"][0])
    bases = common["bases"]
    vertices = common["vertices"]
    inverses = common["inverses"]
    g_lex = common["g_lex"]

    res["lbl_lex"] = get_lex_labels(bases, vertices, inverses, m, n)
    morph, morph_inv, lbl_vtx = get_morph_and_lbl_vtx(bases,vertices)
    g_vtx = get_graph_vtx(g_lex,morph,len(lbl_vtx))
    edge_inv = get_edge_inv(g_lex,g_vtx,morph)
    res["lbl_vtx"] = lbl_vtx
    res["morph"] = morph
    res["morph_inv"] = morph_inv
    res["g_vtx"] = g_vtx
    res["edge_inv"] = edge_inv
    
    return res
    

# -------------------------------------------------------------------