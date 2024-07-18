From mathcomp Require Import all_ssreflect.
From PolyhedraHirschVerif Require Import low_algo.
From __DATA__ Require Import A g_lex lbl_lex. 

Lemma struct_consistent_ok : struct_consistent A g_lex lbl_lex.
Proof.
by rewrite -struct_consistentE; vm_cast_no_check (erefl true).
Qed.

Check struct_consistent_ok.
