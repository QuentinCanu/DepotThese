# PhD Repository of Quentin Canu

This repository gathers the work done during my PhD thesis. This is mainly an extension to the [Coq-Polyhedra](https://github.com/Coq-Polyhedra/Coq-Polyhedra) repository.
## Installation

## Prerequisites

Here are the prerequisites for this repository to work, with the versions that I use :

- `zsh 5.8`
- [lrs](http://cgm.cs.mcgill.ca/%7Eavis/C/lrs.html) installed (version `lrslib_v.7.2_2022.3.6` for me)
- `Python 3.8.7`
- Python libraries: 
	- [networkx](https://networkx.org/)
	- [tqdm](https://tqdm.github.io/)
	- [sympy](https://www.sympy.org/en/index.html)
	- [gmpy2](https://gmpy2.readthedocs.io/en/latest/)
- `OCaml 4.14.0`
- `opam 2.1.3`
- `Coq 8.16.0`
- `dune 3.14.2`
- `coq-bignums 9.0.0+coq8.16`
- Pin these versions of [mathcomp](https://github.com/Coq-Polyhedra/mathcomp.git), [finmap](https://github.com/Coq-Polyhedra/finmap.git) and [binreader](https://github.com/Coq-Polyhedra/coq-binreader.git#main)
### Installing prerequisites from opam

Here are some commands to configure an opam switch that contains everything mandatory for the Coq theory.

        $> opam switch create these-Quentin-Canu ocaml-base-compiler.4.14.0
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
## Description of the repository

The original work of Coq-Polyhedra can be found in the `theories` folder.
The additional material mandatory to the graph certification algorithm can be found in the `enumeration` folder.

### Theory

`enumeration/theories` contains the Coq theory :
- the files in `enumeration/theories/common` are mandatory for all implementations of the graph certification algorithm.
- `enumeration/theories/graph_certif` is the first implementation of the graph certification algorithm. The file `low_algo.v` defines the low-level implementation, while `high_algo.v` defines the high-level one. Finally, `proof_equiv.v` contains the equivalence proof between both implementations
- `enumeration/theories/improved_graph_certif` contains a low-level implementation of an improved version of the vertex verification step from the graph certification algorithm.
- `enumeration/theories/Rank1` contains five low-level implementations of improved vertex verification steps from the graph certification algorithm.
	1. `rank_1_update.v` implementation explores the lex-graph using rank-1 updates.
	2. `rank_1_update_pivot.v` implementation does the same exploration, but also makes use of integral pivoting.
	3. `rank_1_update_matrix.v` implementation explores the lex-graph, by using an additional certificate containing the rank-1 difference between two adjacent points $X^I$ and $X^J$.
	4. `rank_1_update_vector.v` implementation does the same, but the rank-1 difference is retrieved from the multiplication of a column vector and a row vector.
	5. `rank_1_update_lazy.v` implementation explores the lex-graph, by imitating lazy evaluations of numerical values, i.e., an additional certificate contains in order all numerical values as they are needed by the algorithm.

### Benchmarks

The `enumeration/benchmarks` folder contains scripts to execute the different low-level implementations defined.
- The `scripts` and `jobs` folders contain materials mandatory for using the main script, `benchmarks.py`.
- The `data` folder contains the certificates and the benchmark files for different polytopes.
-  
To perform, your current directory must be `enumeration/benchmarks`. First, you must type

	>$./benchmarks.py clean

in order to reset everything and to build the coq theory first. Then, if you type

	>$./benchmarks.py create cube 3

You will generate the benchmark for the 3-dimensional cube, as it can be found in `data/cube_3/benchmarks_cube_3.json`. The available parameters are
	
	>$./benchmarks.py create [--text] [--compute] {cube,cross,cyclic,permutohedron} dim

The benchmarks for the two counter-examples to the Hirsch are slightly different, you can generate them by typing

	>$./benchmarks.py hirsch poly20dim21
	
or

	>$./benchmarks.py hirsch poly23dim24

There is also a file `benchmark.sh` for predefined parameters.

Once the benchmarks for all the polytopes you want are generated, you can type the following command to generate a csv file

	>$./benchmarks.py csv