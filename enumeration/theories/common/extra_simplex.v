From mathcomp Require Import all_ssreflect all_algebra finmap.
From Polyhedra Require Import extra_misc inner_product extra_matrix vector_order affine row_submx.
From Polyhedra Require Import lrel polyhedron poly_base.
From Polyhedra Require Import simplex fsetmin.
Require Import high_graph. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

Open Scope ring_scope.
Open Scope polyh_scope.


Section Simplex.

Context (R : realFieldType) (n m : nat).
Context (A : 'M[R]_(m,n)) (b : 'cV[R]_m) (c : 'cV[R]_n).
Context (bas0 : Simplex.lex_feasible_basis A b).
Hypothesis (bnd_c : Simplex.bounded A b c).

Lemma unpt_pt_is_feas (bas1 : Simplex.lex_feasible_basis A b):
  Simplex.point_of_basis b bas1 \in Simplex.polyhedron A b.
Proof.
rewrite inE Simplex.rel_points_of_basis -col_mul.
move: (Simplex.feasible_basis_is_feasible bas1).
rewrite /Simplex.is_feasible inE.
move/forallP=> lex_feas_bas1; apply/forallP => i.
move/lex_ord0: (lex_feas_bas1 i).
by rewrite !mxE /=; case: splitP => //= j; rewrite (ord1_eq0 j).
Qed.
  

Lemma feas_bas0 : Simplex.feasible A b.
Proof.
apply/Simplex.feasibleP.
exists (Simplex.point_of_basis b bas0).
exact: unpt_pt_is_feas.
Qed.

Definition simplex_lex_exec := Simplex.phase2_exec c bas0.

Definition set_adjacence := fun I I' : {set 'I_m} =>  #|I :&: I'| == n.-1.

Lemma simplex_lex_exec_adj: 
  path (fun I J : Simplex.lex_feasible_basis A b => set_adjacence I J) bas0 simplex_lex_exec.
Proof. exact:Simplex.phase2_exec_adj. Qed.

Lemma simplex_lex_exec_lexopt: 
  path (fun I J : Simplex.lex_feasible_basis A b => (c^T *m Simplex.point_of_basis (Simplex.b_pert b) J) <lex (c^T *m Simplex.point_of_basis (Simplex.b_pert b) I)) bas0 simplex_lex_exec.
Proof. exact:Simplex.phase2_exec_lexopt. Qed.

Lemma simplex_lex_exec_opt:
  path (fun I J : Simplex.lex_feasible_basis A b => '[c, Simplex.point_of_basis b J] <= '[c, Simplex.point_of_basis b I]) bas0 simplex_lex_exec.
Proof. exact:Simplex.phase2_exec_opt. Qed.

Definition simplex_lex_basis := last bas0 simplex_lex_exec.
Definition simplex_lex_point := Simplex.point_of_basis b simplex_lex_basis.
Definition simplex_lex_ppoint := Simplex.point_of_basis (Simplex.b_pert b) simplex_lex_basis.

Lemma simplex_bas0 : Simplex.phase2 c bas0 = Simplex.Phase2_res_optimal_basis (Simplex.phase2_res c bas0).
Proof.
move: (@Simplex.phase2_resP _ _ _ _ _ c bas0).
case: (Simplex.phase2P c bas0).
- move=> bas1 i [red_cost_lt0 i_feas].
  suff: False by case.
  case/(Simplex.boundedP_lower_bound _ feas_bas0) : bnd_c => K K_opt.
  case: (Simplex.unbounded_cert_on_basis K i_feas red_cost_lt0 (unpt_pt_is_feas bas1)).
  move=> x [x_feas].
  by rewrite real_ltNge ?num_real // (K_opt _ x_feas).
- move=> bas1 _ h.
  by rewrite (h (Simplex.Phase2_res_optimal_basis bas1)).
Qed.

Lemma simplex_lex_reduced_cost : (Simplex.reduced_cost_of_basis c simplex_lex_basis) >=m 0.
Proof.
rewrite /simplex_lex_basis; move: simplex_bas0.
case: (Simplex.phase2P c bas0 ) => // bas h []. 
by rewrite /Simplex.phase2_res /simplex_lex_exec => <-.
Qed.

Lemma simplex_lex_feas : simplex_lex_ppoint \in Simplex.lex_polyhedron A (Simplex.b_pert b).
Proof. exact: Simplex.feasible_basis_is_feasible. Qed.

Lemma simplex_feas : simplex_lex_point \in Simplex.polyhedron A b.
Proof. exact: unpt_pt_is_feas. Qed.

Lemma simplex_lex_opt x : x \in Simplex.lex_polyhedron A (Simplex.b_pert b) ->
  (c^T *m simplex_lex_ppoint) <=lex (c^T *m x).
Proof.
move: simplex_lex_reduced_cost.
rewrite /Simplex.reduced_cost_of_basis.
rewrite /Simplex.point_of_basis /= inE.
set I := Simplex.set_of_prebasis _.
set A_I := row_submx.row_submx A _.
set A_I_inv := qinvmx _ _.
move=> red_cost_ge0 /forallP x_inP.
have -> : (c^T *m x) = (c^T *m (A_I_inv *m A_I) *m x).
- rewrite qmulVmx ?mulmx1 //.
  move: (Simplex.basis_trmx_row_free simplex_lex_basis).
  by rewrite -!row_leq_rank mxrank_tr {2}Simplex.prebasis_card.
rewrite !mulmxA -[c^T *m A_I_inv]trmxK trmx_mul trmxK -mulmxA.
apply/lev_mul_lex; rewrite ?trmxK //.
by move=> i; rewrite row_mul !row_submx.row_submx_row -row_mul x_inP.
Qed.

Lemma simplex_opt x : x \in Simplex.polyhedron A b ->
  '[c, simplex_lex_point] <= '[c, x].
Proof.
move=> x_feas.
pose X := row_mx x 0 : 'M_(n, 1 + m).
have/simplex_lex_opt: X \in Simplex.lex_polyhedron A (Simplex.b_pert b).
- rewrite inE; apply/forallP=> i.
  apply/lex_lev=> j; rewrite row_mul -matrix_vdot row_id !mxE.
  case: splitP'.
  + move=> k; rewrite (ord1_eq0 k)=> ->; rewrite colKl col_id.
    move: x_feas; rewrite inE=> /forallP /(_ i).
    by rewrite -matrix_vdot col_id.
  + move=> k ->; rewrite colKr col0 vdot0r !mxE.
    by case: (i == k); rewrite /= ?mulr1n ?mulr0n ?lerN10 ?oppr0.
move/lex_ord0; rewrite -!matrix_vdot row_id trmxK -Simplex.rel_points_of_basis.
suff ->: col 0 X = x by [].
apply/matrixP=> i j; rewrite !mxE (ord1_eq0 j).
by case: splitP=> // k _; rewrite (ord1_eq0 k).
Qed.

End Simplex.

Section PolyOfSyst.
Context (R : realFieldType) (n' m' : nat).
Local Notation m := (m'.+1).
Local Notation n := (n'.+1).
Context (A : 'M[R]_(m,n)) (b : 'cV[R]_m).

Definition base_of_syst (C : 'M[R]_(m,n) * 'cV[R]_m) := 
  [fset [<(row i C.1)^T, C.2 i 0>] | i : 'I_m].
Definition poly_of_syst C:= 'P(base_of_syst C).

Local Notation P := (poly_of_syst (A,b)).

(* Hypothesis P_compact: forall c, Simplex.bounded A b c.
Hypothesis P_feasible: Simplex.feasible A b. *)

Lemma in_feasE x : (x \in P) = (x \in Simplex.polyhedron A b).
Proof.
apply/idP/idP.
- move/in_poly_of_baseP=> x_poly. 
  rewrite inE; apply/forallP=> /= i; rewrite -row_vdot -in_hs.
  by apply/x_poly/imfsetP; exists i.
- rewrite inE; move/forallP=> /= x_poly.
  apply/in_poly_of_baseP=> e.
  case/imfsetP=> /= i _ ->; rewrite in_hs /=.
  rewrite row_vdot; exact: x_poly.
Qed.

Lemma feasE : (P `>` [poly0]) = (Simplex.feasible A b).
Proof.
apply/idP/idP.
- case/proper0P=> x; rewrite in_feasE=> ?.
  by apply/Simplex.feasibleP; exists x.
- case/Simplex.feasibleP=> x; rewrite -in_feasE=> ?.
  by apply/proper0P; exists x.
Qed.

Lemma boundedE c : bounded P c = Simplex.bounded A b c.
Proof.
apply/idP/idP.
- case/boundedP=> x /[dup] x_feas; rewrite in_feasE=> x_splx_feas.
  move/poly_subset_hsP=> Pbase_bnd.
  apply/Simplex.boundedP_lower_bound; first by (apply/Simplex.feasibleP; exists x).
  by exists '[c,x]; move=> y; rewrite -in_feasE=> /Pbase_bnd /=.
- case/Simplex.boundedP=> -[x [+ <-]].
  rewrite -in_feasE=> x_feas poly_bnd.
  apply/boundedP; exists x=> //; apply/poly_subset_hsP=> y.
  by rewrite in_feasE=> /poly_bnd.
Qed.

Lemma pointedE : P `>` [poly0] -> pointed P = Simplex.pointed A.
Proof.
case/proper0P=> y yP.
apply/idP/idP; apply/contraTT.
- case/Simplex.pointedPn=> d /= [dn0 d_feas nd_feas].
  apply/pointedPn; exists y; exists d=> //.
  apply/poly_leP=> x; rewrite affE=> /in_lineP [mu ->].
  rewrite in_feasE; apply/forallP=> i.
  rewrite mulmxDr -scalemxAr.
  suff ->: A *m d = 0.
  + rewrite scaler0 addr0; move: yP; rewrite in_feasE.
    by move/forallP=> /(_ i).
  apply: lev_antisym; rewrite d_feas andbT.
  by rewrite -oppv_ge0 -mulmxN.
- case/pointedPn=> x [d] dn0 /poly_leP line_sub.
  apply/Simplex.pointedPn; exists d=> /=.
  have: x \in P by
    apply/line_sub; rewrite affE; apply/in_lineP; exists 0; rewrite scale0r addr0.
  rewrite in_feasE inE -subv_ge0=> /gev0P x_feas.
  suff Ad0: (A *m d) = 0 by rewrite mulmxN Ad0 oppr0 lev_refl dn0.
  apply/eqP/contraT; case/matrix0Pn=> i [j]; rewrite (ord1_eq0 j).
  set S := (A *m x - b) i 0.
  set D := (A *m d) i 0.
  case: ltrgt0P=> // /[dup] Ad0 + _.
  + set mu := - (S / D) - 1.
    have: x + mu *: d \in P by apply/line_sub; rewrite affE; apply/in_lineP; exists mu.
    rewrite in_feasE inE -subv_ge0 mulmxDr addrAC -scalemxAr.
    move/gev0P/(_ i); rewrite mxE -/S mxE -/D /mu mulrDl mulNr -mulrA mulVr ?(unitf_gt0 Ad0) //.
    rewrite mulr1 addrA subrr add0r mulNr mul1r oppr_ge0.
    by case: ltrgt0P.
  + set mu := - (S / D) + 1.
    have: x + mu *: d \in P by apply/line_sub; rewrite affE; apply/in_lineP; exists mu.
    rewrite in_feasE inE -subv_ge0 mulmxDr addrAC -scalemxAr.
    move/gev0P/(_ i); rewrite mxE -/S mxE -/D /mu mulrDl mulNr -mulrA mulVr ?(unitf_lt0 Ad0) //.
    rewrite mulr1 addrA subrr add0r mul1r.
    by case: ltrgt0P.
Qed.

(* Lemma compactE : compact P.
Proof.
apply/compactP; last (move=> c; rewrite boundedE; exact/P_compact). 
apply/proper0P; case/Simplex.feasibleP: P_feasible=> x.
by rewrite -feasE=> ?; exists x.
Qed. *)

Lemma feas_to_lexfeas x :
  x \in Simplex.polyhedron A b ->
  row_mx x 0 \in Simplex.lex_polyhedron A (Simplex.b_pert b).
Proof.
rewrite !inE; move/forallP=> /= x_poly.
apply/forallP=> /= i; rewrite row_row_mx row_mul.
apply/lex_lev=> j. rewrite -matrix_vdot row_id.
case: (splitP' j)=> k ->.
- rewrite row_mxEl colKl col_id (ord1_eq0 k) mxE row_vdot.
  exact: x_poly.
- rewrite row_mxEr colKr col0 vdot0r !mxE.
  by case: (i == k); rewrite ?mulr1n ?mulr0n ?lerN10 ?oppr_le0.
Qed.

Lemma lexfeas_to_feas x :
  x \in Simplex.lex_polyhedron A (Simplex.b_pert b) ->
  col 0 x \in Simplex.polyhedron A b.
Proof.
rewrite !inE; move/forallP=> /= x_feaslex.
apply/forallP=> i; rewrite -col_mul mxE.
move/(_ i): x_feaslex=> /lex_ord0; rewrite /Simplex.b_pert 2!mxE.
by case: splitP=> //= j _; rewrite (ord1_eq0 j) !mxE.
Qed.

Lemma Pbase_prop0 (I : Simplex.lex_feasible_basis A b): P `>` [poly0].
Proof. 
apply/proper0P; exists (Simplex.point_of_basis b I). 
by rewrite in_feasE unpt_pt_is_feas. 
Qed.

Lemma unpt_pt_is_eq (bas1 : Simplex.lex_feasible_basis A b):
  forall k, k \in bas1 -> row k A *m Simplex.point_of_basis b bas1 = row k b.
Proof.
move=> k; rewrite Simplex.active_ineq_pert_exact inE=> /eqP.
move/(congr1 (col 0)); rewrite Simplex.rel_points_of_basis.
rewrite -!col_mul -row_mul=> ->.
apply/matrixP=> p q; rewrite (ord1_eq0 p) (ord1_eq0 q) !mxE.
by case: splitP=> // j _; rewrite (ord1_eq0 j).
Qed.
End PolyOfSyst.

Section LexGraph.

Context (R : realFieldType) (n' m' : nat).
Local Notation n := n'.+1.
Local Notation m := m'.+1.
Context (A : 'M[R]_(m,n)) (b : 'cV[R]_m).

Definition lex_graph := mk_graph [fset x | x : Simplex.lex_feasible_basis A b] (fun I J : Simplex.lex_feasible_basis A b =>  set_adjacence n I J).

Section LexGraphProofs.

Lemma splx_adj_sym I J: (@set_adjacence n m I J) -> (@set_adjacence n m J I).
Proof. by rewrite /set_adjacence setIC. Qed.

Lemma splx_adj_xx (I : Simplex.lex_feasible_basis A b): ~~ (@set_adjacence n m I I).
Proof.
rewrite /set_adjacence setIid Simplex.prebasis_card.
by elim: n'.
Qed.

Lemma splx_adj_neq (I J : Simplex.lex_feasible_basis A b):
  (J != I) && (@set_adjacence n m I J) = (@set_adjacence n m I J).
Proof.
rewrite andb_idl //.
move=> adj_IJ; apply: contraT; rewrite negbK=> /eqP IJ.
by move: adj_IJ; rewrite IJ (negPf (splx_adj_xx I)).
Qed.

Section LexGraphConnected.

Section MkPath.

Context (I J : Simplex.lex_feasible_basis A b).

Definition obj_conn := \sum_(i < #|J|) (row i (row_submx A J)).

Lemma obj_connE: 
  obj_conn *m Simplex.point_of_basis (Simplex.b_pert b) J =
  \sum_(i < #|J|) (row i (row_submx (Simplex.b_pert b) J)).
Proof.
rewrite mulmx_suml /=; apply/eq_big=> //= i _.
by rewrite -row_mul Simplex.row_submx_point_of_basis.
Qed.

Lemma obj_conn_opt:
  forall K : Simplex.lex_feasible_basis A b, K != J ->
  (obj_conn *m Simplex.point_of_basis (Simplex.b_pert b) J) <lex
  (obj_conn *m Simplex.point_of_basis (Simplex.b_pert b) K).
Proof.
move=> K K_n_J; rewrite obj_connE mulmx_suml /=.
apply/ltrlex_sum.
- move=> i; move: (Simplex.feasible_basis_is_feasible K).
  by rewrite !row_submx_row -row_mul /Simplex.is_feasible inE=> /forallP /(_ (enum_val i)).
- have: (J != K :> {set _}) by rewrite eq_sym.
  rewrite eqEcard [X in (X <= _)%N]Simplex.prebasis_card [X in (_ <= X)%N]Simplex.prebasis_card leqnn andbT.
  case/subsetPn=> j jJ j_n_K; exists (enum_rank_in jJ j); rewrite !row_submx_row -row_mul enum_rankK_in //.
  rewrite /ltrlex; move: (Simplex.feasible_basis_is_feasible K).
  rewrite /Simplex.is_feasible inE=> /forallP /(_ j) ->; rewrite andbT.
  by move: j_n_K; rewrite Simplex.active_ineq_pert_exact inE eq_sym.
Qed.

Lemma bound_obj_conn : Simplex.bounded A b (obj_conn^T).
Proof.
apply/Simplex.boundedP_lower_bound.
- apply/Simplex.feasibleP; exists (Simplex.point_of_basis b I).
  exact: Simplex.lex_feasible_basis_is_feasible.
- exists '[obj_conn^T, Simplex.point_of_basis b J].
  move=> x; rewrite /Simplex.polyhedron inE.
  move/(row_submx_lev J).
  rewrite -(Simplex.row_submx_point_of_basis) /= row_submx_mul => h.
  rewrite -[obj_conn^T]mulmx1 -!vdot_mulmx.
  apply:vdot_lev; first by (apply/gev0P=> i; rewrite mxE (ord1_eq0 i) ler01).
  rewrite !mulmx_suml; apply/lev_sum=> i _.
  rewrite -!row_mul -!row_submx_mul !row_submx_row.
  move: h; rewrite -!row_submx_mul=> /row_submx_levP.
  move=> /(_ (enum_val i) (enum_valP _)) h.
  apply/forallP=> j; rewrite (ord1_eq0 j).
  by move: h; rewrite !mxE.
Qed.

Lemma opt_is_J : simplex_lex_basis (obj_conn^T) I = J.
Proof.
apply/eqP/contraT=> /obj_conn_opt; rewrite lex_ltrNge.
rewrite -/simplex_lex_ppoint.
have ->: Simplex.point_of_basis (Simplex.b_pert b) (simplex_lex_basis obj_conn^T I) = simplex_lex_ppoint (obj_conn^T) I by [].
have h_J: Simplex.point_of_basis (Simplex.b_pert b) J \in Simplex.lex_polyhedron A (Simplex.b_pert b) by
  exact/(Simplex.feasible_basis_is_feasible J).
rewrite -{-2}[obj_conn]trmxK simplex_lex_opt //.
exact: bound_obj_conn.
Qed.

Lemma path_to_J: path (edges lex_graph) I (simplex_lex_exec obj_conn^T I).
Proof.
under eq_path => [x y] do rewrite edge_mk_graph ?inE // splx_adj_neq.
exact:simplex_lex_exec_adj.
Qed.

Program Definition conn_lex_gpath := @GPath _ lex_graph I J (simplex_lex_exec (obj_conn^T) I) _ _ _.
Next Obligation. by rewrite vtx_mk_graph in_fsetE. Qed.
Next Obligation. exact:path_to_J. Qed.
Next Obligation. exact/eqP/opt_is_J. Qed.

End MkPath.

Lemma lex_graph_connected : connected lex_graph.
Proof. by move=> I J _ _; exists (conn_lex_gpath I J). Qed.

End LexGraphConnected.

Section LexGraphRegular.

Section MkNeigh.

Context (I : Simplex.lex_feasible_basis A b).
Hypothesis (P_compact : forall c, Simplex.bounded A b c).


Lemma P_feasible : Simplex.feasible A b.
Proof.
apply/Simplex.feasibleP.
exists (Simplex.point_of_basis b I).
exact: (Simplex.lex_feasible_basis_is_feasible I).
Qed.

Section NeighDef.

Context (i : 'I_#|I|).

Lemma reg_infeas_dir : ~~ Simplex.feasible_dir A (Simplex.direction i).
Proof.
apply/contraT; rewrite negbK.
move/Simplex.feasibleP: P_feasible=> [x_0].
move/Simplex.unbounded_certificate=> /[apply] /(_ (- (Simplex.direction i))).
rewrite vdotNl oppr_lt0 vnorm_gt0 Simplex.direction_neq0.
move: P_compact=> /(_ (- (Simplex.direction i))) /(Simplex.boundedP_lower_bound _ P_feasible).
case=> K=> + /(_ K isT) [x [x_P x_K]].
by move=> /(_ x x_P); rewrite leNgt x_K.
Qed.

Definition neigh_reg := Simplex.lex_rule_fbasis reg_infeas_dir.

Lemma neigh_regE : exists2 j, j \notin I & neigh_reg = j |: (I :\ enum_val i) :> {set _}.
Proof.
rewrite /neigh_reg /Simplex.lex_rule_fbasis //=.
set j := Simplex.argmin_gap _ _ _; exists j=> //.
exact/Simplex.lex_ent_var_not_in_basis.
Qed.

Lemma neigh_reg_adj : (@set_adjacence n m I neigh_reg).
Proof.
rewrite /set_adjacence; case: neigh_regE=> j j_n_I ->.
rewrite setIUr setIDA setIid disjoint_setI0 1?disjoint_sym ?disjoints1 //.
rewrite set0U cardsD (elimT setIidPr) ?sub1set ?enum_valP //.
by rewrite Simplex.prebasis_card cards1 subn1.
Qed.

End NeighDef.

Section NeighInj.

Lemma neigh_reg_inj: injective neigh_reg.
Proof.
move=> i j reg_eq.
have: neigh_reg i = neigh_reg j :> {set _} by rewrite reg_eq.
case: (neigh_regE i)=> i' i'_nI ->.
case: (neigh_regE j)=> j' j'_nI -> reg_eq_val.
have ij': i' = j'.
- move/setP/(_ j'): reg_eq_val.
  by rewrite !inE (negPf j'_nI) !andbF !orbF eqxx eq_sym=> /eqP.
move/setP/(_ (enum_val i)): reg_eq_val.
rewrite ij' !inE eqxx ?enum_valP /= ?orbF ?andbT.
have/negPf -> /=: (enum_val i != j') by
  apply/contraT; rewrite negbK=> /eqP; move: j'_nI=> /[swap] <-; rewrite enum_valP.
by move/esym/negbFE/eqP/enum_val_inj.
Qed.

End NeighInj.
Section NeighSurj.

Lemma splx_adj_witness (J : Simplex.lex_feasible_basis A b):
  (@set_adjacence n m I J) -> exists i j,
  [/\ i \in I, j \notin I & (J  = j |: (I :\ i) :> {set _})].
Proof.
move/eqP=> adjIJ.
have/properP [_]: I :&: J \proper I by
  rewrite properEcard subsetIl Simplex.prebasis_card adjIJ /=.
have/properP [_]: I :&: J \proper J by
  rewrite properEcard subsetIr Simplex.prebasis_card adjIJ /=.
case=> j jJ j_nIJ [i iI i_nIJ].
have I_eq: i |: (I :&: J) = I:> {set _}.
- apply/eqP; rewrite eqEcard Simplex.prebasis_card.
  rewrite inE iI /= in i_nIJ.
  rewrite cardsU1 adjIJ inE iI i_nIJ leqnn andbT.
  by rewrite subUset subsetIl sub1set iI.
have J_eq: j |: (I :&: J) = J:> {set _}.
- apply/eqP; rewrite eqEcard Simplex.prebasis_card.
  rewrite inE jJ /= in j_nIJ.
  rewrite cardsU1 adjIJ inE jJ j_nIJ leqnn andbT.
  by rewrite subUset subsetIr sub1set jJ.
have i_n_j: i != j.
- apply/contraT; rewrite negbK=> /eqP h.
  by move: i_nIJ; rewrite inE iI h jJ.
exists i; exists j; split; rewrite ?inE ?eqxx // ?jJ ?andbT.
  by move: j_nIJ; rewrite inE jJ andbT.
by rewrite -J_eq; congr setU; rewrite -[in RHS]I_eq setU1K.
Qed.

Definition neigh_reg_fset := [fset neigh_reg i | i in 'I_#|I|].

Lemma neigh_reg_surj (J : Simplex.lex_feasible_basis A b): (@set_adjacence n m I J) -> exists i, J = neigh_reg i.
Proof.
case/splx_adj_witness=> i' [j] [i'I j_nI J_eq].
set i := (enum_rank_in i'I i'); exists i.
have J_eq_val: J = j |: (I :\ enum_val i) :> {set _} by
  rewrite enum_rankK_in.
rewrite (Simplex.edge_lex_ruleE j_nI J_eq_val (reg_infeas_dir i)) //.
Qed.


Lemma succ_reg :
  successors lex_graph I = neigh_reg_fset.
Proof.
apply/fsetP=> J; rewrite ?succ_mk_graph ?in_fsetE !inE //=.
apply/idP/idP; rewrite splx_adj_neq.
- case/neigh_reg_surj=> i ->; exact/in_imfset.
- case/imfsetP=> /= i _ ->; exact/neigh_reg_adj.
Qed.
End NeighSurj.
End MkNeigh.

Lemma lex_graph_regular : (forall c, Simplex.bounded A b c) -> 
  regular lex_graph n.
Proof.
move=> P_bounded.
move=> I _. rewrite succ_reg card_imfset ?size_enum_ord ?Simplex.prebasis_card //.
exact: neigh_reg_inj.
Qed.

End LexGraphRegular.

End LexGraphProofs.

End LexGraph.

Section PolyGraph.

Definition poly_graph {k : nat} {K : realFieldType}
  (P : 'poly[K]_k):= 
  mk_graph (vertex_set P) (adj P).

End PolyGraph.