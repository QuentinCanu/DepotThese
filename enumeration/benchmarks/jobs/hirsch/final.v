Require Import Uint63.
From mathcomp Require Import all_ssreflect finmap.
From Polyhedra Require Import poly_base.
From PolyhedraHirsch Require Import extra_int extra_simplex high_graph.
From PolyhedraHirschVerif Require Import low_algo proof_equiv.
From __DATA__ Require Import A b.
Require Import struct_consistent_r vertex_consistent_r img_lex_graph_r format_r.
Require Import bounded_Po_test_r dim_full_test_r diameter_check_r diameter_exact_r.


Local Notation m' := (Com.m A).-1.
Local Notation n' := (Com.n A).-1.
Local Notation high_poly := (spec_poly m' n' (A, b)).
Local Notation P := (poly_of_syst high_poly).

Lemma Hirsch_Disproved : 
  ((diameter (poly_graph P)) > #|`facets P| - (\pdim P).-1)%nat.
Proof.
apply: disprove_Hirsch.
- exact: poly_format_ok.
- exact: lex_graph_format_ok.
- exact: vtx_graph_format_ok.
- exact: bound_pos_format_ok.
- exact: bound_neg_format_ok.
- exact: vertex_consistent_ok.
- exact: struct_consistent_ok.
- exact: img_lex_graph_ok.
- exact: bounded_Po_test_ok.
- exact: graph_n0_ok.
- exact: inv_format_ok.
- exact: dim_full_test_ok.
- exact: diameter_check_ok.
Qed.

(* Lemma Exact_Diameter : diameter (poly_graph (poly_of_syst high_poly)) = __VALUE__%nat.
Proof.
apply: diameter_of___NAME__.
- exact: poly_format_ok.
- exact: lex_graph_format_ok.
- exact: vtx_graph_format_ok.
- exact: bound_pos_format_ok.
- exact: bound_neg_format_ok.
- exact: vertex_consistent_ok.
- exact: struct_consistent_ok.
- exact: img_lex_graph_ok.
- exact: bounded_Po_test_ok.
- exact: graph_n0_ok.
- exact: diameter_exact_ok.
Qed. *)