From mathcomp Require Import all_ssreflect.
From PolyhedraHirschVerif Require Import low_algo. 
From __DATA__ Require Import A b bound_pos bound_neg.

Lemma bounded_Po_test_ok : @bounded_Po_test A bound_pos bound_neg.
Proof.
by rewrite -bounded_Po_testE; vm_cast_no_check (erefl true).
Qed.

Check bounded_Po_test_ok.