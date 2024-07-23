From mathcomp Require Import all_ssreflect.
From PolyhedraHirschVerif Require Import low_algo.
From __DATA__ Require Import A b g_lex lbl_lex. 

Lemma vertex_consistent_ok : vertex_consistent A b g_lex lbl_lex.
Proof.
by rewrite -vertex_consistentE; vm_cast_no_check (erefl true).
Qed.

Check vertex_consistent_ok.
