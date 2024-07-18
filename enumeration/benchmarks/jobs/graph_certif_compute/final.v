From mathcomp Require Import all_ssreflect.
From PolyhedraHirschVerif Require Import proof_equiv.
Require Import struct_consistent_r vertex_consistent_r img_lex_graph_r format_r.
Require Import bounded_Po_test_r.

Definition validation :=
  Validation poly_format_ok lex_graph_format_ok
    vtx_graph_format_ok bound_pos_format_ok
    bound_neg_format_ok vertex_consistent_ok
    struct_consistent_ok img_lex_graph_ok 
    bounded_Po_test_ok graph_n0_ok.

Check validation.
