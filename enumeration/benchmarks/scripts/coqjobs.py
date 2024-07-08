#! /usr/bin/env python3

# --------------------------------------------------------------------
import json, sys, re, os, argparse as argp
import subprocess as sp, shutil as sh

from . import core

# --------------------------------------------------------------------
DUNE = r'''
(coq.theory
 (name {name})
 (theories {dataname} {algoname})
 (flags -w -ambiguous-paths
        -w -notation-overridden
        -w -redundant-canonical-projection
        -w -projection-no-head-constant))
 (include_subdirs qualified)
'''.lstrip()

# --------------------------------------------------------------------
def coqjob(duneName, duneDataname, duneAlgoname, jobdir, tgtdir):

    for filename in os.listdir(jobdir):
        if os.path.splitext(filename)[1] != '.v':
            continue
        with open(os.path.join(jobdir, filename)) as stream:
            contents = stream.read()
        contents = contents.replace('__DATA__', f'{duneDataname}')
        with open(os.path.join(tgtdir, filename), 'w') as stream:
            stream.write(contents)

    with open(os.path.join(tgtdir, "dune"), "w") as stream:
        stream.write(DUNE.format(name = duneName, dataname = duneDataname, algoname = duneAlgoname))

# --------------------------------------------------------------------
