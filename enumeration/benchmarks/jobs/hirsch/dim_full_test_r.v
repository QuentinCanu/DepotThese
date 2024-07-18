From mathcomp Require Import all_ssreflect.
From PolyhedraHirschVerif Require Import low_algo. 
From __DATA__ Require Import A lbl_vtx map_dim origin inv_dim.

Lemma dim_full_test_ok : @dim_full_test A lbl_vtx map_dim origin inv_dim.
Proof.
by rewrite -dim_full_testE; vm_cast_no_check (erefl true).
Qed.

Check dim_full_test_ok.