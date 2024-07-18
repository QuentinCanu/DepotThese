From mathcomp Require Import all_ssreflect.
From PolyhedraHirschVerif Require Import low_algo. 
From __DATA__ Require Import A g_vtx start.

Lemma diameter_check_ok : @diameter_check A g_vtx start.
Proof.
by rewrite -diameter_checkE; vm_cast_no_check (erefl true).
Qed.

Check diameter_check_ok.