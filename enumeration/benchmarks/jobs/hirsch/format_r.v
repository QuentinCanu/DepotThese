From mathcomp Require Import all_ssreflect.
From PolyhedraHirschVerif Require Import low_algo. 
From __DATA__ Require Import A b g_lex lbl_lex g_vtx lbl_vtx bound_pos bound_neg inv_dim.

Lemma poly_format_ok : poly_format A b.
Proof. by rewrite -poly_formatE; vm_cast_no_check (erefl true). Qed.

Lemma lex_graph_format_ok : lex_graph_format A g_lex l_lex.
Proof. by rewrite -lex_graph_formatE; vm_cast_no_check (erefl true). Qed.

Lemma vtx_graph_format_ok : vtx_graph_format A g_vtx l_vtx.
Proof. by rewrite -vert_graph_formatE; vm_cast_no_check (erefl true). Qed.

Lemma bound_pos_format_ok : bound_format A bound_pos.
Proof. by rewrite -bound_formatE; vm_cast_no_check (erefl true). Qed.

Lemma bound_neg_format_ok : bound_format A bound_neg.
Proof. by rewrite -bound_formatE; vm_cast_no_check (erefl true). Qed.

Lemma graph_n0_ok : lex_graph_n0 g_lex.
Proof. by rewrite -lex_graph_n0E; vm_cast_no_check (erefl true). Qed.

Lemma inv_format_ok : inv_format A inv_dim.
Proof. by rewrite -inv_formatE; vm_cast_no_check (erefl true). Qed.