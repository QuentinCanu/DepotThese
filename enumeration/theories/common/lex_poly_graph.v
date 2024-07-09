From mathcomp Require Import all_ssreflect all_algebra finmap.
From Polyhedra Require Import extra_misc inner_product extra_matrix vector_order affine row_submx.
From Polyhedra Require Import lrel polyhedron poly_base.
From Polyhedra Require Import simplex fsetmin.
From PolyhedraHirsch Require Import high_graph extra_simplex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

Open Scope ring_scope.
Open Scope polyh_scope.

Section VertexVerification.

Context (R : realFieldType) (n' m' : nat).
Local Notation m := (m'.+1).
Local Notation n := (n'.+1).
Context (A : 'M[R]_(m,n)) (b : 'cV[R]_m).
Local Notation P := (poly_of_syst (A,b)).

Hypothesis P_compact : compact P.


Section Vertices.

Section LexBasisToVertex.

Definition fset_active (bas : {set 'I_m}) :=
  [fset [<(row i A)^T, b i 0>] | i : 'I_m in bas].

Lemma fset_active_sub (bas : Simplex.prebasis m n) :
  (fset_active bas `<=` base_of_syst (A,b))%fset.
Proof.
apply/fsubsetP=> e /imfsetP /= [i i_bas ->].
by rewrite in_imfset.
Qed.

Lemma fset_active_befst (bas : Simplex.basis A) :
  (befst @` (fset_active bas)) = [fset (row i A)^T | i in bas].
Proof.
apply/fsetP=> x; apply/idP/idP.
- case/imfsetP=> /= e /imfsetP [/= i i_bas ->] ->.
  rewrite lfunE /=; exact/in_imfset.
- case/imfsetP=> /= i i_bas ->.
  apply/imfsetP; exists [<(row i A)^T, b i 0>]; rewrite ?lfunE //=.
  exact/in_imfset.
Qed.

Lemma fset_active_free (bas : Simplex.basis A) :
  free (befst @`fset_active bas).
Proof.
rewrite fset_active_befst.
move: (Simplex.basis_is_basis bas); rewrite /Simplex.is_basis row_free_free_submx.
rewrite -free_tr_rV; set S := [seq _ | _ in _].
move=> free_S.
rewrite (perm_free (Y:=S)) //; apply/uniq_perm; rewrite ?fset_uniq ?free_uniq //.
move=> x; apply/idP/idP.
- case/imfsetP=> /= i i_bas ->; exact/image_f.
- case/imageP=> /= i i_bas ->; exact/in_imfset.
Qed.

Lemma A_inj_bas (bas : Simplex.basis A) : {in bas &, injective (fun i=> row i A)}.
Proof.
move=> i j i_bas j_bas; move: (Simplex.basis_is_basis bas).
rewrite /Simplex.is_basis /= row_free_free_submx /image_mem=> /free_uniq /uniq_map_inj.
by apply; rewrite mem_enum.
Qed.

Lemma fset_active_card_befst (bas:Simplex.basis A) :
  #|` befst @` (fset_active bas)| = n.
Proof.
rewrite fset_active_befst card_in_imfset -?cardE ?Simplex.prebasis_card //.
move=> i j i_bas j_bas /trmx_inj; exact/(@A_inj_bas bas).
Qed.

Lemma fset_active_befst_inj (bas: Simplex.basis A):
  {in fset_active bas &, injective befst}.
Proof.
move=> x y /imfsetP [/= i i_bas ->] /imfsetP [/= j j_bas ->].
by rewrite !lfunE=> /= /trmx_inj /(@A_inj_bas bas) ->.
Qed.

Lemma fset_active_feas (bas : Simplex.lex_feasible_basis A b) :
  [pt Simplex.point_of_basis b bas]%:PH =
  'P^=(base_of_syst (A,b); fset_active bas).
Proof.
apply/poly_eqP=> x.
rewrite in_pt in_polyEq in_feasE /=.
apply/idP/idP.
- move/eqP=> ->; rewrite unpt_pt_is_feas andbT.
  apply/forallP=> e; rewrite in_hp.
  case/imfsetP: (fsvalP e)=> /= i i_bas -> /=.
  move: (Simplex.row_submx_point_of_basis b bas); rewrite -row_submx_mul.
  move/row_submx_row_matrixP=> /(_ _ i_bas).
  rewrite row_mul.
  move/matrixP/(_ ord0 ord0); rewrite -matrix_vdot row_id col_id mxE.
  by move=> ->.
- case/andP=> /forallP bas_active x_feas; apply/eqP/Simplex.basis_subset_active_ineq_eq/subsetP.
  move=> i; rewrite inE /= => i_bas; apply/eqP/matrixP=> p q; rewrite (ord1_eq0 p) (ord1_eq0 q).
  have ei_active: [< (row i A)^T , b i 0 >] \in (fset_active bas) by rewrite /fset_active; exact/in_imfset.
  by move: (bas_active [`ei_active]); rewrite in_hp /==> /eqP; rewrite row_vdot !mxE.
Qed.

Lemma lex_basis_to_vtx:
  {subset 
  [fset Simplex.point_of_basis b (Simplex.basis_of_feasible_basis x0)
    | x0 in Simplex.lex_feasible_basis A b] <= vertex_set P}.
Proof.
move=> x.
case/imfsetP=> /= bas _ ->; rewrite in_vertex_setP.
apply/face_active_free_fset; rewrite ?pt_proper0 //.
exists (fset_active bas); split; rewrite ?fset_active_sub ?fset_active_free //.
- exact: fset_active_feas.
- by rewrite fset_active_card_befst dim_pt subSS subn0.
Qed.

End LexBasisToVertex.

Section VertexToLexBasis.

Lemma vtx_to_lex_basis:
  {subset vertex_set P <=
  [fset Simplex.point_of_basis b (Simplex.basis_of_feasible_basis x0)
    | x0 in Simplex.lex_feasible_basis A b]
  }.
Proof.
move=> x.
move/[dup]/vertex_set_subset; rewrite in_feasE=> x_feas. 
rewrite in_vertex_setP=> /face_argmin /(_ (pt_proper0 _)).
case=> c bnd_c x_opt_c.
apply/imfsetP.
move/compact_pointed: P_compact; rewrite pointedE;
  last by (apply/proper0P; exists x; rewrite in_feasE).
move/Simplex.build_lex_feasible_basis=> /(_ _ _ x_feas) => bas0.
exists (simplex_lex_basis c bas0)=> //=.
suff: simplex_lex_point c bas0 \in argmin P c.
- by rewrite -x_opt_c in_pt=> /eqP <-.
apply/(argmin_mem (x:=x)); rewrite ?simplex_opt ?in_feasE ?simplex_feas //.
- by rewrite -x_opt_c in_pt.
- by rewrite -boundedE.
Qed.

End VertexToLexBasis.

Lemma vertex_img_set :
  vertex_set P =
  [fset Simplex.point_of_basis b (Simplex.basis_of_feasible_basis x) |
    x : Simplex.lex_feasible_basis A b].
Proof.
apply/fsetP=> x; apply/idP/idP.
+ exact:vtx_to_lex_basis.
+ exact:lex_basis_to_vtx.
Qed.

Lemma lexbas_vtx (bas : Simplex.lex_feasible_basis A b) :
  Simplex.point_of_basis b bas \in vertex_set P.
Proof. by rewrite vertex_img_set; apply/imfsetP; exists bas. Qed.

End Vertices.

Section Edges.

Lemma fset_active_edge_sub_base (I J: Simplex.prebasis m n) :
  (fset_active I `&` fset_active J `<=` base_of_syst (A,b))%fset.
Proof. exact/(fsubset_trans (fsubsetIl _ _))/fset_active_sub. Qed.

Definition fset_active_edge_free (I J : Simplex.basis A) :
  free (befst @` (fset_active I `&` fset_active J))%fset.
Proof.
apply: (@free_subset _ _ _ (befst @` fset_active I)).
- move=> x /imfsetP [/= e e_IJ] ->; apply/in_imfset.
  move: e e_IJ; exact/fsubsetP/fsubsetIl.
- exact:fset_active_free.
- exact: fset_uniq.
Qed.

Section EdgeActive.

Context (I J : Simplex.lex_feasible_basis A b).
Hypothesis edge_IJ: (@set_adjacence n m I J).
Local Definition x := Simplex.point_of_basis b I.
Local Definition y := Simplex.point_of_basis b J.
Hypothesis x_n_y: x != y.

Lemma active_inj_edge i j:
  i \in I -> j \in J -> row i A = row j A -> b i 0 = b j 0 ->
  i = j.
Proof.
case: (splx_adj_witness edge_IJ)=> p [q] [pI qnI J_eq].
have I_eq: I = p |: J :\ q :> {set _}.
- rewrite J_eq; apply/setP=> x; rewrite !inE.
  case/boolP: (x == p)=> [/eqP ->|_] //=; rewrite ?pI.
  by case/boolP: (x == q)=> [/eqP ->|_] //=; rewrite (negPf qnI).
rewrite I_eq !inE=> /orP [/eqP ->|/andP [_] /(@A_inj_bas J) /[apply]/[apply] //].
rewrite J_eq !inE=> /orP [/eqP ->|/andP [_] /(A_inj_bas pI) /[apply] //].
move=> row_pq b_pq.
suff/eqP: x = y by rewrite (negPf x_n_y).
rewrite /y; apply/Simplex.is_point_of_basis_pert_active.
move=> k; move/setP: (J_eq)=> ->; rewrite !inE; case/orP.
- move/eqP=> ->; rewrite /x row_mul -row_pq.
  move/unpt_pt_is_eq: (pI)=> ->; apply/matrixP=> ? y; rewrite !mxE.
  by rewrite (ord1_eq0 y).
- by case/andP=> _ /unpt_pt_is_eq; rewrite row_mul.
Qed.

Lemma fset_active_edge_eq : 
  (fset_active I `&` fset_active J)%fset = fset_active (I :&: J).
Proof.
apply/fsetP=> e; apply/idP/idP.
- rewrite inE=> /andP [] /imfsetP [/= i iI ->].
  case/imfsetP=> /= j jJ [/trmx_inj].
  move/active_inj_edge=> /(_ iI jJ) /[apply] ij_eq.
  by apply/imfsetP; exists i=> //=; rewrite !inE iI ij_eq jJ.
- case/imfsetP=> /= i; rewrite inE => /andP [iI iJ ->].
  by rewrite inE; apply/andP; split; apply/imfsetP; exists i.
Qed.

Lemma fset_active_edge_card_befst:
  #|` befst @` (fset_active I `&` fset_active J)|%fset = n.-1.
Proof.
rewrite fset_active_edge_eq card_in_imfset /=.
- rewrite card_in_imfset /= -?cardE; first by move/eqP: edge_IJ.
  move=> i j; rewrite !inE=> /andP [iI _] /andP [jI _]. 
  by case=> /trmx_inj /(A_inj_bas iI jI).
- move=> e f /imfsetP /= [i + ->] /imfsetP /= [j + ->].
  rewrite !inE=> /andP [iI _] /andP [jI _].
  by rewrite !lfunE /= => /trmx_inj /(A_inj_bas iI jI) ->.
Qed.

Lemma A_IJ_rank : \rank (row_submx A (I :&: J)) = n.-1.
Proof.
apply/anti_leq; move/eqP: edge_IJ=> <-.
rewrite rank_leq_row row_leq_rank /=.
rewrite row_free_free_submx -free_tr.
rewrite (perm_free (Y:=(befst @` (fset_active I `&` fset_active J))%fset)) ?fset_active_edge_free //.
rewrite fset_active_edge_eq; apply/uniq_perm; rewrite ?fset_uniq //.
- rewrite map_inj_in_uniq ?enum_uniq //.
  move=> i j; rewrite !mem_enum !inE=> /andP [iI _] /andP [jI _].
  by move/trmx_inj/(A_inj_bas iI jI).
- move=> x; apply/idP/idP.
  + case/imageP=> /= i iIJ ->; apply/imfsetP.
    exists [<(row i A)^T, b i 0>]; rewrite ?lfunE //.
    by apply/imfsetP; exists i.
  + case/imfsetP=> /= [e /imfsetP [/= i iIJ ->] ->].
    by rewrite lfunE /=; apply/imageP; exists i.
Qed.

Lemma A_IJ_xy z: z \in [fset x; y] ->
  (row_submx A (I :&: J)) *m z = row_submx b (I :&: J).
Proof.
move=> z_xy; rewrite -row_submx_mul.
apply/row_submx_row_matrixP=> i iIJ; rewrite row_mul.
move: (iIJ); rewrite !inE=> /andP [iI iJ].
move/subsetP: (Simplex.basis_subset_of_active_ineq b I)=> /(_ _ iI).
move/subsetP: (Simplex.basis_subset_of_active_ineq b J)=> /(_ _ iJ).
rewrite !inE !row_mul => /eqP + /eqP.
by move: z_xy; rewrite !inE=> /orP [] /eqP ->.
Qed.

Lemma A_I_y: (row_submx A I) *m y != row_submx b I.
Proof.
move: x_n_y; apply/contra=> h; rewrite eq_sym; apply/eqP/Simplex.basis_subset_active_ineq_eq.
apply/subsetP=> i iI; rewrite inE.
by move/eqP: h; rewrite -row_submx_mul=> /row_submx_row_matrixP /(_ _ iI) ->.
Qed.

Lemma A_J_x: (row_submx A J) *m x != row_submx b J.
Proof.
move: x_n_y; apply/contra=> h; apply/eqP/Simplex.basis_subset_active_ineq_eq.
apply/subsetP=> i iI; rewrite inE.
by move/eqP: h; rewrite -row_submx_mul=> /row_submx_row_matrixP /(_ _ iI) ->.
Qed.

Lemma x_eq_base: exists2 i, ((row i A) *m x) 0 0 = b i 0 & ((row i A) *m y) 0 0 > b i 0.
Proof.
case: (splx_adj_witness edge_IJ)=> i [j] [iI jnI J_eq].
exists i.
- move/subsetP: (Simplex.basis_subset_of_active_ineq b I)=> /(_ _ iI).
  by rewrite inE row_mul=> /eqP ->; rewrite mxE.
- move: (A_IJ_xy (fset22 _ _)) A_I_y.
  rewrite -row_submx_mul=> /row_submx_row_matrixP h.
  apply/contraR; rewrite -leNgt -row_submx_mul -row_mul mxE => Aiy_le_b.
  apply/eqP/row_submx_row_matrixP=> k kI.
  case/boolP: (k \in J).
  + move=> kJ; move: (h k); rewrite inE kI kJ; exact.
  + rewrite J_eq !inE kI andbT negb_or negbK=> /andP [_ /eqP ->].
    apply/matrixP=> p q; rewrite (ord1_eq0 p) (ord1_eq0 q) mxE [RHS]mxE.
    apply/le_anti; rewrite Aiy_le_b /=.
    move: (Simplex.lex_feasible_basis_is_feasible J); rewrite inE.
    by move/forallP=> /(_ i).
Qed.

Lemma y_eq_base: exists2 j, ((row j A) *m y) 0 0 = b j 0 & ((row j A) *m x) 0 0 > b j 0.
Proof.
case: (splx_adj_witness (splx_adj_sym edge_IJ))=> j [i] [jJ inJ I_eq].
exists j.
- move/subsetP: (Simplex.basis_subset_of_active_ineq b J)=> /(_ _ jJ).
  by rewrite inE row_mul=> /eqP ->; rewrite mxE.
- move: (A_IJ_xy (fset21 _ _)) A_J_x.
  rewrite -row_submx_mul=> /row_submx_row_matrixP h.
  apply/contraR; rewrite -leNgt -row_submx_mul -row_mul mxE => Ajx_le_b.
  apply/eqP/row_submx_row_matrixP=> k kI.
  case/boolP: (k \in I).
  + move=> kJ; move: (h k); rewrite inE kI kJ; exact.
  + rewrite I_eq !inE kI andbT negb_or negbK=> /andP [_ /eqP ->].
    apply/matrixP=> p q; rewrite (ord1_eq0 p) (ord1_eq0 q) mxE [RHS]mxE.
    apply/le_anti; rewrite Ajx_le_b /=.
    move: (Simplex.lex_feasible_basis_is_feasible I); rewrite inE.
    by move/forallP=> /(_ j).
Qed.
 
  
Lemma fset_active_edge_to_lambda z:
  z \in 'P^=(base_of_syst (A,b); fset_active I `&` fset_active J) -> 
  exists lambda, z = lambda *: x + (1 - lambda) *: y.
Proof.
case/in_polyEqP=> eq_IJ z_feas.
have A_IJ_z: row_submx A (I :&: J) *m z = row_submx b (I :&: J).
- apply/matrixP=> i j.
  rewrite (ord1_eq0 j) -row_vdot row_submx_mxE row_submx_row.
  apply/eqP.
  move: (eq_IJ ([<(row (enum_val i) A)^T, b (enum_val i) 0>])).
  rewrite fset_active_edge_eq in_hp /= row_vdot; apply.
  apply/imfsetP; exists (enum_val i)=> //=; exact: enum_valP.
have A_IJ_x := (A_IJ_xy (fset21 _ _)).
have A_IJ_y := (A_IJ_xy (fset22 _ _)).
move: (f_equal2 (@GRing.add _) A_IJ_x (f_equal (@GRing.opp _) A_IJ_y)).
move: (f_equal2 (@GRing.add _) A_IJ_x (f_equal (@GRing.opp _) A_IJ_z)).
rewrite subrr -!mulmxBr => /(congr1 trmx) + /(congr1 trmx).
rewrite trmx0 !trmx_mul=> /rank1_ker /[apply].
rewrite corank1_kermx // ?A_IJ_rank // => /(_ (erefl _)).
case=> [/eqP|]; rewrite ?trmx_eq0 ?subr_eq0; [move=> h|].
  by move: x_n_y; rewrite h.
case=> lambda /(congr1 trmx); rewrite trmxK trmx_mul trmxK.
rewrite mulmx_sum_col big_ord1 col_id mxE.
move/(congr1 (@GRing.opp _))/eqP; rewrite opprB subr_eq.
move/eqP=> ->; exists (1 - lambda 0 0).
rewrite !scalerBl !scalerBr !scale1r addrC -[in RHS]addrA. 
congr (_ + _); rewrite opprB opprD opprK; congr (_ + _).
by rewrite addrC -addrA addNr addr0.
Qed.
    


Lemma fset_active_edge_to_segm z:
  z \in 'P^=(base_of_syst(A,b); fset_active I `&` fset_active J) -> 
  z \in [segm x & y].
Proof.
move=> /[dup] /fset_active_edge_to_lambda [lambda ->].
move/in_polyEqP=> [in_hp_z z_base].
apply/in_segmP; exists (1 - lambda); 
  last by (congr (_ + _); congr (_ *: _); rewrite opprB addrC -addrA addNr addr0).
move: z_base; rewrite in_feasE inE mulmxDr -!scalemxAr=> /forallP h.
case: (x_eq_base)=> i Aix Aiy; case: (y_eq_base)=> j Ajy Ajx.
rewrite subr_ge0 ler_subl_addl ler_addr; apply/andP; split.
- move: (h i); rewrite 2!mxE [X in _ + X]mxE.
  move: Aix; rewrite -row_mul mxE=> ->; rewrite -ler_subl_addl.
  rewrite -{1}[b i 0]mul1r -mulrBl -subr_ge0 -mulrBr.
  rewrite pmulr_lge0 ?subr_ge0 // subr_gt0; move: Aiy.
  by rewrite -row_mul mxE.
- move: (h j); rewrite 2!mxE [X in _ + X]mxE.
  move: Ajy; rewrite -row_mul mxE=> ->; rewrite -ler_subl_addr.
  rewrite -{1}[b j 0]mul1r -mulrBl opprB addrCA addrN addr0.
  rewrite -subr_ge0 -mulrBr pmulr_lge0 //; move: Ajx.
  by rewrite -row_mul mxE subr_gt0.
Qed.

Lemma fset_active_edge_feas:
  [segm x & y] =
  'P^=(base_of_syst (A,b); fset_active I `&` fset_active J).
Proof.
apply/poly_eqP=> z; apply/idP/idP.
- case/in_segmP=> mu /andP [mu0 mu1] ->.
  apply/in_polyEqP; split.
  + move=> e; rewrite fset_active_edge_eq=> /imfsetP [/= i iIJ ->].
    rewrite in_hp /= vdotDr !vdotZr !row_vdot.
    move: (A_IJ_xy (fset21 _ _)) (A_IJ_xy (fset22 _ _)).
    rewrite -!row_submx_mul=> /row_submx_matrixP /(_ _ iIJ 0) ->.
    move/row_submx_matrixP/(_ _ iIJ 0)=> ->.
    by rewrite -mulrDl -addrA addNr addr0 mul1r.
  + rewrite in_feasE inE; apply/forallP=> i.
    rewrite mulmxDr -!scalemxAr 2!mxE [X in _ + X]mxE.
    move: (Simplex.lex_feasible_basis_is_feasible J); rewrite inE=> /forallP /(_ i).
    move: (Simplex.lex_feasible_basis_is_feasible I); rewrite inE=> /forallP /(_ i).
    move: mu1; rewrite -subr_ge0=> mu1.
    move=> /(ler_wpmul2l mu1) + /(ler_wpmul2l mu0); move=> /ler_add /[apply].
    by rewrite -mulrDl -addrA addNr addr0 mul1r.
- exact: fset_active_edge_to_segm. 
Qed.

Lemma lex_basis_to_adj_vtx: adj P x y.
Proof.
rewrite /adj /= x_n_y /=.
apply/face_active_free_fset; rewrite ?segm_prop0 //.
exists (fset_active I `&` fset_active J)%fset; split.
- exact: fset_active_edge_sub_base.
- exact: fset_active_edge_feas.
- by rewrite fset_active_edge_card_befst dim_segm x_n_y /= !subSS subn0.
- exact: fset_active_edge_free.
Qed.

End EdgeActive.

Section EdgeSimplexExec.

Context (x y : 'cV[R]_n) (I : Simplex.lex_feasible_basis A b).
Hypothesis edge_xy : adj P x y.
Hypothesis bas_I_x : Simplex.point_of_basis b I = x.

Lemma poly0P : P `>` [poly0].
Proof.
apply/proper0P; exists (Simplex.point_of_basis b I).
rewrite in_feasE.
exact: Simplex.lex_feasible_basis_is_feasible.
Qed.

Lemma c_def : exists c, [segm x & y] == argmin P c.
Proof.
case/andP: edge_xy=> _ /face_argmin.
by case/(_ (segm_prop0 _ _))=> c _ ->; exists c.
Qed.

Lemma c'_def : exists c', [pt y]%:PH == argmin P c'.
Proof.
move/adj_vtxr: edge_xy; rewrite in_vertex_setP.
by case/face_argmin/(_ (pt_proper0 _))=> c' _ ->; exists c'.
Qed.

Definition c := xchoose c_def.
Definition c' := xchoose c'_def.
Definition obj_func (epsilon : R) : 'cV_n := c + epsilon *: c'.
Definition exec_adj (epsilon : R) := simplex_lex_exec (obj_func epsilon) I.

Definition gap z := '[c, x - z] / '[c', z - x]. 
Definition fset_gap := [fset gap z | z in vertex_set P & ('[c', z - x] < 0) && (z != y)].
Definition min_epsilon := (fset_min 1%R fset_gap) / 2%:R.

Lemma fset_gap_gt0 G: G \in fset_gap -> 0 < G.
Proof.
case/imfsetP=> /= z; rewrite inE=> /andP [z_vtx /andP [c'_xz zny] ->].
rewrite /gap.
rewrite ltr_ndivl_mulr // mul0r vdotDr vdotNr subr_lt0.
apply/(argmin_sep (P:=P)).
- move/compactP: P_compact; apply.
  exact: poly0P.
- by move/eqP: (xchooseP c_def)=> <-; rewrite in_segml.
- move: zny; apply/contra.
  move/compactP: P_compact=> /(_ poly0P c) /argmin_in_face_set. 
  move/(vertex_set_of_face z_vtx)=> /[apply].
  move/eqP: (xchooseP c_def)=> <-; rewrite vertex_set_segm !inE. 
  by case/orP=> // /eqP zx; move: c'_xz; rewrite zx subrr vdot0r ltxx.
- exact: vertex_set_subset.
Qed.

Lemma min_epsilon_gt0: min_epsilon > 0.
Proof.
rewrite /min_epsilon; case/boolP: (fset_gap == fset0).
- move/eqP=> ->; rewrite fset_min0 ?divr_gt0 ?ltr01 ?ltr0Sn //.
- by case/(fset_minP 1)=> /fset_gap_gt0 ? _; rewrite divr_gt0 ?ltr0Sn.
Qed.

Lemma min_epsilon_ltgap z: z \in vertex_set P ->
  '[c', z - x] < 0 -> z != y ->
  min_epsilon < '[c, x - z] / '[c', z - x].
Proof.
move=> z_vtx c'_xz zny; rewrite /min_epsilon.
have fset_gap_n0: fset_gap != fset0 by
  apply/fset0Pn; exists (gap z); apply/in_imfset=> /=; rewrite !inE z_vtx c'_xz zny.
move/(fset_minP 1): fset_gap_n0; move: min_epsilon_gt0; rewrite /min_epsilon.
set F := fset_min _ _.
rewrite ltr_pdivl_mulr ?ltr0Sn // mul0r => F_gt0.
case=> F_in /(_ (gap z)); rewrite in_imfset ?inE ?z_vtx ?c'_xz ?zny //.
move/(_ isT); rewrite -ltr_pdivl_mulr ?invr_gt0 ?ltr0Sn // invrK.
move/le_lt_trans; apply; rewrite ltr_pmulr ?fset_gap_gt0 ?in_imfset ?inE ?z_vtx ?c'_xz ?zny //.
by rewrite ltr1n.
Qed.

Lemma obj_func_min_xy: '[obj_func (min_epsilon), y] < '[obj_func (min_epsilon), x].
Proof.
rewrite /obj_func !vdotDl !vdotZl; apply/ler_lt_add.
- apply/(argmin_lower_bound (P:=P)); last exact/vertex_set_subset/(adj_vtxl edge_xy).
  move/eqP: (xchooseP c_def)=> <-; exact: in_segmr.
- rewrite (ltr_pmul2l min_epsilon_gt0).
  apply/(argmin_sep (P:=P)).
  + by move/(compactP poly0P): P_compact.
  + by move/eqP: (xchooseP c'_def)=> <-; rewrite in_pt.
  + by move/eqP: (xchooseP c'_def)=> <-; rewrite in_pt; case/andP: edge_xy.
  + exact/vertex_set_subset/(adj_vtxl edge_xy).
Qed.

Lemma obj_func_min_out z: z \in vertex_set P -> z \notin [fset x; y] ->
  '[obj_func (min_epsilon), x] < '[obj_func (min_epsilon), z].
Proof.
move=> z_vtx; rewrite !inE negb_or=> /andP [znx zny].
rewrite /obj_func !vdotDl !vdotZl.
rewrite -ltr_subr_addr -addrA -mulrBr -ltr_subl_addl.
rewrite -!vdotBr; case: (ger0P '[c', z - x]).
- rewrite -(pmulr_rge0 _ min_epsilon_gt0)=> /lt_le_trans; apply.
  rewrite vdotBr subr_lt0; apply/(argmin_sep (P:=P)).
  + by move/(compactP poly0P): P_compact.
  + move/eqP: (xchooseP c_def)=> <-; exact: in_segml.
  + case/andP: edge_xy=> _ /(vertex_set_of_face z_vtx) h.
    apply/contraT; rewrite negbK.
    move/eqP: (xchooseP c_def)=> <- /h.
    by rewrite vertex_set_segm !inE (negbTE znx) (negbTE zny).
  + exact/vertex_set_subset.
  (*TODO:same proof as in fset_gap_gt0*)
- move=> c'_zx; rewrite -ltr_ndivl_mulr //.
  exact/min_epsilon_ltgap.
Qed.

Lemma exec_adj_xy J: J \in (exec_adj min_epsilon) -> 
  Simplex.point_of_basis b J \in [fset x; y]. 
Proof.
rewrite /exec_adj.
move: (simplex_lex_exec_opt (obj_func min_epsilon) I).
elim: (simplex_lex_exec _ _) J=> //= h t IH. 
move=> J /andP [hI path_ht]; rewrite inE; case/orP.
- move/eqP=> ->; move: hI; rewrite bas_I_x.
  exact/contra_leT/obj_func_min_out/lexbas_vtx.
- apply/IH; move: path_ht hI.
  elim: t {IH}=> //= h' t' IH' /andP [hh' ??].
  apply/andP; split=> //; exact/(le_trans hh').
Qed.

Lemma exec_adj_last: simplex_lex_point (obj_func min_epsilon) I = y.
Proof.
apply/eqP/contraT=> splx_pt_Iy.
have splx_pt_Ix: simplex_lex_point (obj_func min_epsilon) I = x.
- move: (mem_last I (exec_adj min_epsilon)); rewrite inE.
  rewrite /exec_adj /simplex_lex_point /simplex_lex_basis.
  case/orP=> [/eqP -> //|/exec_adj_xy]; rewrite !inE (negPf splx_pt_Iy) orbF.
  by move/eqP=> ->.
have := (simplex_opt I) => /(_ (obj_func min_epsilon)).
move/(compactP poly0P): P_compact=> /(_ (obj_func min_epsilon)). 
rewrite boundedE=> /[swap] /[apply].
move/(_ y); rewrite -in_feasE vertex_set_subset ?(adj_vtxr edge_xy) //.
by move/(_ isT); rewrite splx_pt_Ix leNgt obj_func_min_xy.
Qed.

Lemma adj_I_to_J: exists P Q: Simplex.lex_feasible_basis A b,
  [/\ (@set_adjacence n m P Q), Simplex.point_of_basis b P = x
    & Simplex.point_of_basis b Q = y].
Proof.
have:=path_biprop_edge=> /(_ _ _ _ _ I (exec_adj min_epsilon)).
move=> /(_ (@set_adjacence n m)) /(_ (fun K=> Simplex.point_of_basis b K = x)).
move=> /(_ (fun K=> Simplex.point_of_basis b K = y)).
case.
- exact/simplex_lex_exec_adj.
- by move=> K /exec_adj_xy; rewrite !inE=> /orP [] /eqP ->; [left|right].
- exact: bas_I_x.
- exact: exec_adj_last.
- move: exec_adj_last; rewrite /simplex_lex_point /exec_adj /simplex_lex_basis.
  rewrite /exec_adj; case: (simplex_lex_exec _ _)=> //=.
  rewrite bas_I_x; apply/contra_eqT=> _.
  by case/andP: edge_xy.
- move=> P [Q] [_ _ ? <- <-]; exists P, Q; split=> //.
Qed.

End EdgeSimplexExec. 

Lemma vtx_to_adj_lex_basis x y: adj P x y -> exists I J : Simplex.lex_feasible_basis A b,
  [/\ (@set_adjacence n m I J), Simplex.point_of_basis b I = x & 
  Simplex.point_of_basis b J = y].
Proof.
move=> edge_xy; have:= adj_vtxl edge_xy.
rewrite vertex_img_set=> /imfsetP [/= K _ /esym bas_K_x].
exact/(adj_I_to_J _ bas_K_x).
Qed.

End Edges.

Lemma img_lex_graph_poly_graph :
  poly_graph P = ((Simplex.point_of_basis b) @/ (lex_graph A b)).
Proof.
apply/gisof_idE/gisofE; split => //=; rewrite !vtx_mk_graph.
- rewrite vertex_img_set /=; apply/fsetP=> x.
  rewrite !inE /=; apply/idP/idP=> /imfsetP [x' /= _ ->]; apply/in_imfset=> //.
  exact/in_imfset.
- move=> x y x_vtx y_vtx; apply/idP/idP.
  + rewrite edge_mk_graph=> // /andP [?] /[dup] edge_xy.
    move/vtx_to_adj_lex_basis=> [I] [J] [splx_adj_IJ splx_pt_Ix splx_pt_Jy].
    apply/edge_img_graph; split=> //.
    exists I, J; split=> //.
    rewrite edge_mk_graph ?splx_adj_neq //; exact/in_imfset.
  + case/edge_img_graph=> yx [I] [J] [splx_pt_Ix splx_pt_Jy].
    rewrite edge_mk_graph ?in_imfset // splx_adj_neq.
    move/lex_basis_to_adj_vtx=> /=. rewrite /VertexVerification.x /VertexVerification.y splx_pt_Ix splx_pt_Jy.
    rewrite eq_sym; move/(_ yx)=> ? //; rewrite edge_mk_graph // yx /=.
    by rewrite eq_sym.
Qed.

End VertexVerification.
