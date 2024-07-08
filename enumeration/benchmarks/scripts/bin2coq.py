#! /usr/bin/env python3

# --------------------------------------------------------------------------------
import os, sys

# --------------------------------------------------------------------------------
DUNE = r'''
(coq.theory
 (name {name})
 (flags -w -ambiguous-paths
        -w -notation-overridden
        -w -redundant-canonical-projection
        -w -projection-no-head-constant))
 (include_subdirs qualified)
'''.lstrip()
# --------------------------------------------------------------------------------
def usage_and_exit():
    print(f'Usage: {sys.argv[0]} [NAME]')
    exit(1)

def bin2coq(duneName, tgtdir):
    def writer(stream):
        def output(str=''): 
            print(str,file=stream)
        return output
    
    binfiles = os.listdir(tgtdir)

    for binfile in binfiles:
        certname,ext = os.path.splitext(binfile) 
        if ext != ".bin":
            continue
        with open(os.path.join(tgtdir,f"{certname}.v"), "w") as stream:
            output = writer(stream)
            output("From BinReader Require Import BinReader.")
            output()
            output(f'LoadData "{os.path.join(tgtdir,certname)}.bin" As {certname}.')
    
    with open(os.path.join(tgtdir, "dune"), "w") as stream:
        stream.write(DUNE.format(name = duneName))


if __name__ == "__main__":
    if len(sys.argv) != 2:
        usage_and_exit()
    name = sys.argv[1]
    main(name) 


