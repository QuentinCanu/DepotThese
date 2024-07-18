From mathcomp Require Import all_ssreflect.
From PolyhedraHirschVerif Require Import low_algo. 
From __DATA__ Require Import A b g_lex lbl_lex g_vtx lbl_vtx bound_pos bound_neg.

Lemma poly_format_ok : poly_format A b.
Proof. by rewrite -poly_formatE; exact_no_check (erefl true). Qed.

Lemma lex_graph_format_ok : lex_graph_format A g_lex lbl_lex.
Proof. by rewrite -lex_graph_formatE; exact_no_check (erefl true). Qed.

Lemma vtx_graph_format_ok : vtx_graph_format A g_vtx lbl_vtx.
Proof. by rewrite -vert_graph_formatE; exact_no_check (erefl true). Qed.

Lemma bound_pos_format_ok : bound_format A bound_pos.
Proof. by rewrite -bound_formatE; exact_no_check (erefl true). Qed.

Lemma bound_neg_format_ok : bound_format A bound_neg.
Proof. by rewrite -bound_formatE; exact_no_check (erefl true). Qed.

Lemma graph_n0_ok : lex_graph_n0 g_lex.
Proof. by rewrite -lex_graph_n0E; exact_no_check (erefl true). Qed.