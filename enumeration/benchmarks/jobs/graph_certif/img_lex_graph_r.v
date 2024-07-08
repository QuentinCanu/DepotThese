From mathcomp Require Import all_ssreflect.
From PolyhedraHirschVerif Require Import low_algo.
From __DATA__ Require Import g_lex g_vtx l_lex l_vtx morph morph_inv edge_inv.

Lemma img_lex_graph_ok : img_lex_graph morph morph_inv edge_inv g_lex l_lex g_vtx l_vtx.
Proof.
by rewrite -img_lex_graphE; vm_cast_no_check (erefl true).
Qed.

Check img_lex_graph_ok.
