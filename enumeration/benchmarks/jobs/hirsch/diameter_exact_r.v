Require Import UInt63.
From mathcomp Require Import all_ssreflect.
From PolyhedraHirschVerif Require Import low_algo. 
From __DATA__ Require Import g_vtx.

Lemma diameter_exact_ok : diameter_exact g_vtx (__VALUE__)%uint63.
Proof.
by rewrite -diameter_exactE; vm_cast_no_check (erefl true).
Qed.

Check diameter_exact_ok.