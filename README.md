# Coq-Polyhedra

Formalizing convex polyhedra in Coq

## Installation



### Installing prerequisites from opam

Starting with opam 2.x, you can install all the needed dependencies
via the opam OCaml packages manager.

        $> opam switch create ocaml-base-compiler.4.14.0 these-Quentin-Canu
        $> opam repo add coq-released https://coq.inria.fr/opam/released
        $> opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
        $> opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
        $> opam pin add -n coq 8.16.0
        $> opam pin add -n coq-bignums 9.0.0+coq8.16
        $> opam pin add -n https://github.com/Coq-Polyhedra/mathcomp.git
        $> opam pin add -n https://github.com/Coq-Polyhedra/finmap.git
        $> opam pin add -n https://github.com/Coq-Polyhedra/coq-binreader.git#main
        $> opam update
        $> opam upgrade
        $> opam install dune coq coq-mathcomp-field coq-mathcomp-finmap coq-binreader

