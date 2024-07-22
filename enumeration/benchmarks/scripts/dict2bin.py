#! /usr/bin/env python3

# --------------------------------------------------------------------
import sys, os, json
import tqdm
import struct
import gc

# --------------------------------------------------------------------
sys.path.append(os.path.realpath(os.path.join(
    os.path.dirname(__file__),
    *'../../binreader/scripts'.split('/')
)))

from . import binreader

# --------------------------------------------------------------------
DESCRIPTORS = dict(
    A        = '[[Q]]',
    b       = '[Q]',
    lbl_lex   = '[([I],[[Q]])]',
    lbl_vtx = '[[Q]]',
    g_lex     = '[[I]]',
    g_vtx   = '[[I]]',
    morph      = '[I]',
    morph_inv  = '[I]',
    edge_inv  = '[[(I,I)]]',
    bound_pos  = '[[Q]]',
    bound_neg  = '[[Q]]',
    origin    = 'I',
    start     = 'I',
    map_dim   = '[I]',
    inv_dim   = '[[Q]]',
    bases = '[[I]]',
    vertices = '[[Q]]',
    inverses = '[[[Q]]]',
    idx_r1 = 'I',
    x_I_r1 = '[Q]',
    inv_r1 = '[[Q]]',
    order_r1 = '[I]',
    pred_r1 = '[(I,I,I)]',
    det_r1 = 'Q',
    pred_mx_r1 = '[[[Q]]]',
    pred_vect_r1 =  '[([Q],[Q])]',
    unsrt_vtx_r1 = '[[Q]]',
    heap_lazy = '[Q]',
    init_r1 = '[[Q]]'
)

DESCRIPTORS = {
    k: binreader.descriptor_of_string(v) for k, v in DESCRIPTORS.items()
}

# --------------------------------------------------------------------
def json2dict(name):
    srcdir = os.path.join(os.path.dirname(__file__), '..', 'data', name)

    with open(os.path.join(srcdir, f'{name}.json')) as stream:
        contents = json.load(stream)
    
    return contents

def dict2bin(tgtdir,contents):
    res = {}
    for key in tqdm.tqdm(contents.keys(), desc="Serializing certificates : "):
        if key not in DESCRIPTORS:
            print(f'Ignoring {key}', file = sys.stderr)
            continue
        descr = DESCRIPTORS[key]
        tgtbin = os.path.join(tgtdir, f'{key}.bin')
        with open(tgtbin, 'w+b') as stream:
            descr.descriptor(stream)
            descr.pickle(contents[key], stream)
        res[f"Size of {key}.bin"] = float(os.path.getsize(tgtbin))
    return res

def main(name):
    dict2bin(name,json2dict(name))
# --------------------------------------------------------------------
if __name__ == '__main__':
    if len(sys.argv)-1 != 1:
        print('Usage: convert [file]', file = sys.stderr)
        exit(1)

    name = sys.argv[1]
    main(name)
