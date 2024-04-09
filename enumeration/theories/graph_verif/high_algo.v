From mathcomp Require Import all_ssreflect all_algebra finmap.
From Coq Require Import Uint63 PArray.
From Polyhedra Require Import extra_misc inner_product extra_matrix vector_order affine row_submx barycenter.
From Polyhedra Require Import lrel polyhedron poly_base simplex.
From PolyhedraHirsch Require Import graph high_graph img_graph extra_array extra_int rat_bigQ diameter refinement extra_simplex lex_poly_graph.
(* Require Import low_algo high_proof proof_equiv. *)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory Num.Theory.

(* Local Notation "a .[ i ]" := (PArray.get a i). *)

Section LexCorrectness.

Context (m' n' : nat).
Local Notation m := m'.+1. 
Local Notation n := n'.+1.

Context (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).
Local Notation b_pert := (Simplex.b_pert b).

(* Context (G : graph (enum_type m' n')). *)

(* Hypothesis enum_h_r : high_enum_algo A b G. *)
Hypothesis P_compact : forall c, Simplex.bounded A b c.
(* Hypothesis G_prop0 : G != (graph0 (enum_type m' n')). *)

(* Lemma enum_h :
  [forall e : vertices G,
    [&& card_verification (fsval e),
        feas_verification A b (fsval e),
        bas_verification A b (fsval e),
        reg_verification G (fsval e) &
        [forall e' : successors G (fsval e), inter_verification (fsval e) (fsval e')]
    ]
  ].
Proof. by move: enum_h_r; rewrite high_enum_algoE. Qed. *)

Section Def.

Definition set_Im : choiceType := [choiceType of {set 'I_m}].
Definition M_n := [choiceType of 'M[rat]_(n,1+m)].
Definition enum_type := [choiceType of (set_Im * M_n)%type].
 
Context (G : graph enum_type).

Definition card_verification (e : enum_type) := #|e.1| == n.
Definition feas_verification (e : enum_type) := e.2 \in Simplex.lex_polyhedron A b_pert.
Definition bas_verification (e : enum_type):= ((row_submx A e.1) *m e.2)%R == row_submx b_pert e.1.
Definition vertex_verification (e : enum_type) := [&& card_verification e, feas_verification e & bas_verification e].

Definition inter_verification (e e': enum_type) := (#|e.1 :&: e'.1| == n').
Definition reg_verification (e : enum_type) := #|` successors G e| == n.
Definition struct_verification (e : enum_type) := reg_verification e && all (inter_verification e) (successors G e).

Definition high_enum_algo := 
  all vertex_verification (vertices G) &&
  all struct_verification (vertices G).

End Def.

Section ConstructFeasbas.

Context (e : enum_type).
Hypothesis vertex_e: vertex_verification e. 
(* Hypothesis IxG : e \in (vertices G). *)

Local Notation I := e.1.
Local Notation X := e.2.

Lemma I_prebasis : #|I|==n.
Proof.
by case/and3P: vertex_e.
Qed.

Definition prebasis_I := Simplex.Prebasis I_prebasis.
Definition X_inv := (-1 *: (row_submx (col' ord0 X)^T I)^T)%R.

Lemma I_basis : Simplex.is_basis A prebasis_I.
Proof.
case/and3P: vertex_e=> _ _; rewrite /bas_verification /= => /eqP A_Ix.
rewrite /Simplex.is_basis /=; apply/row_freeP.
exists X_inv; rewrite /X_inv -scalemxAr -[X in (X *m _)%R]trmxK -trmx_mul tr_col'.
apply/matrixP=> p q; rewrite !mxE.
under eq_bigr => [k _] do rewrite !mxE. 
move: A_Ix=> /matrixP /(_ p (lift ord0 (enum_val q))); rewrite mxE.
under eq_bigr=> [k _] do rewrite mxE GRing.mulrC; move=> ->.
rewrite !mxE; case: splitP.
- move=> j /=; rewrite (ord1_eq0 j) /= => /esym /eqP.
  by rewrite (negPf (neq_bump _ _)).
- move=> k; rewrite lift0 [RHS]add1n => /succn_inj /val_inj <-.
  rewrite !mxE -GRing.mulNrn GRing.Theory.mulrnAr GRing.mulrN1 GRing.opprK.
  congr GRing.natmul; congr nat_of_bool.
  by apply/idP/idP=> [/eqP /enum_val_inj ->|/eqP ->].
Qed.

Definition basis_I := Simplex.Basis I_basis.

Lemma X_point_of_I : X = Simplex.point_of_basis b_pert basis_I.
Proof. 
rewrite -(@Simplex.basis_subset_active_ineq_eq _ _ _ _ _ _ _ X) //=.
apply/subsetP=> i iI; rewrite inE row_mul.
case/and3P: vertex_e=> _ _ /eqP I_bas.
by rewrite -[i](enum_rankK_in iI) // -!row_submx_row -I_bas row_mul.
Qed.

Lemma I_feasible : Simplex.is_feasible b_pert basis_I.
Proof.
case/and3P: vertex_e=> _ + _; rewrite /feas_verification /=.
by rewrite X_point_of_I /Simplex.is_feasible.
Qed.

Definition lexbasis_I := Simplex.FeasibleBasis I_feasible.

End ConstructFeasbas.

Section SubGraph.
Context (G_lex : graph enum_type).
Hypothesis G_lex_n0 : G_lex != graph0 _.
Hypothesis G_lex_vtx : all (vertex_verification) (vertices G_lex).
Hypothesis G_lex_edge : 
  all (fun e=> all (inter_verification e) (successors G_lex e)) (vertices G_lex).

Lemma e0_def : exists e, e \in vertices G_lex.
Proof. by move/graph0Pn: G_lex_n0. Qed. 

Definition e0 := (xchoose e0_def).
Lemma G_lex_lex_feas : {in (vertices G_lex), forall e, vertex_verification e}.
Proof. by move/allP: (G_lex_vtx). Qed.

Definition I0 := lexbasis_I (G_lex_lex_feas (xchooseP e0_def)).

Definition to_feas_bas (e : enum_type):=
  if @idP (e \in vertices G_lex) is ReflectT h then
  lexbasis_I (G_lex_lex_feas h) else I0.

Lemma to_feas_bas_edges :
  forall x y, edges G_lex x y -> 
  edges (lex_graph A b) (to_feas_bas x) (to_feas_bas y).
Proof.
move=> x y /[dup] /edge_vtxlr [xG yG]. 
rewrite edge_mk_graph ?inE // -in_succE => yx.
rewrite splx_adj_neq /set_adjacence /=.
move/allP: G_lex_edge=> /(_ x xG) /allP /(_ y yx); rewrite /inter_verification.
by rewrite /to_feas_bas; case: {-}_/idP=> // p; case: {-}_/idP.
Qed.

End SubGraph.

Section RegGraph.

Context (G_lex : graph (enum_type)).
Hypothesis G_lex_n0 : G_lex != graph0 _.
Hypothesis G_lex_vtx : all (vertex_verification) (vertices G_lex).
Hypothesis G_lex_edge : 
  all (fun e=> all (inter_verification e) (successors G_lex e)) (vertices G_lex).
Hypothesis G_lex_reg : all (reg_verification G_lex) (vertices G_lex).

Local Notation to_feas_bas := (to_feas_bas G_lex_n0 G_lex_vtx).

Lemma to_feas_bas_inj : {in vertices G_lex &, injective to_feas_bas}.
Proof.
move=> e e' eG e'G; rewrite /to_feas_bas.
case: {-}_/idP=> // p; case: {-}_/idP=> // p'.
move=> bas_I_eq; rewrite [e]surjective_pairing [e']surjective_pairing.
apply/pair_equal_spec; split.
+ by move: bas_I_eq; do 3! move/(congr1 val).
+ set vtx_e := (G_lex_lex_feas G_lex_vtx p).
  set vtx_e' := (G_lex_lex_feas G_lex_vtx p').
  rewrite (X_point_of_I vtx_e) (X_point_of_I vtx_e').
  by move/(congr1 val): bas_I_eq=> /= ->.
Qed.

Lemma G_lex_succ: {in (vertices G_lex), forall e,
  to_feas_bas @` (successors G_lex e) = successors (lex_graph A b) (to_feas_bas e)}.
Proof.
move=> x xG; apply/eqP; rewrite eqEfcard; apply/andP; split.
+ apply/fsubsetP=> y' /imfsetP [/= y].
  rewrite in_succE=> /[dup] /edge_vtxr yG /(to_feas_bas_edges G_lex_n0 G_lex_vtx G_lex_edge).
  by rewrite -in_succE => /[swap] ->.
+ rewrite lex_graph_regular ?vtx_mk_graph ?inE // ?card_in_imfset /=.
  * move/allP: G_lex_reg=> /(_ x xG). 
    by rewrite /reg_verification=> /eqP ->.
  * move=> p q /(fsubsetP (sub_succ _ _)) + /(fsubsetP (sub_succ _ _)).
    exact:to_feas_bas_inj.
  (* * apply/Simplex.feasibleP. 
    exists (Simplex.point_of_basis b (I0 G_lex_n0 G_lex_vtx)).
    exact: Simplex.lex_feasible_basis_is_feasible. *)
Qed.

End RegGraph.

Section LexCertif.

Context (G_lex : graph (enum_type)).
Hypothesis G_lex_n0 : G_lex != graph0 _.
Hypothesis G_lex_verif : high_enum_algo G_lex.

Lemma G_lex_vtx : all (vertex_verification) (vertices G_lex).
Proof. by case/andP: G_lex_verif. Qed.

Lemma G_lex_edge : all 
  (fun e=> all (inter_verification e) (successors G_lex e)) 
  (vertices G_lex).
Proof. 
case/andP: G_lex_verif=> _ /allP struct_h.
by apply/allP=> x xG; case/andP: (struct_h x xG).
Qed.

Lemma G_lex_reg : all (reg_verification G_lex) (vertices G_lex).
Proof.
case/andP: G_lex_verif=> _ /allP struct_h.
by apply/allP=> x xG; case/andP: (struct_h x xG).
Qed.

Local Notation to_feas_bas := (to_feas_bas G_lex_n0 G_lex_vtx).

Lemma repr_lex_graph: gisof G_lex (lex_graph A b) to_feas_bas.
Proof.
apply/sub_gisof=> //.
- exact: to_feas_bas_inj.
- by apply/fsubsetP=> x; rewrite vtx_mk_graph inE /=.
- exact/to_feas_bas_edges/G_lex_edge. 
- exact:lex_graph_connected.
- apply/G_lex_succ; [exact:G_lex_edge|exact:G_lex_reg].
Qed.

End LexCertif.

End LexCorrectness.

(* --------------------------------------------------------------- *)

Section ImgGraph.

Context (m' n' : nat).
Local Notation m := m'.+1.
Local Notation n := n'.+1.

Context (G_lex : graph (enum_type m' n')) (G_vert : graph [choiceType of 'cV[rat]_n]).

Context (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).

Local Notation P := (poly_of_syst (A,b)).

Hypothesis P_compact : compact P.
Hypothesis G_lex_verif : high_enum_algo A b G_lex.
Hypothesis G_lex_n0 : G_lex != graph0 _.

Definition phi (e : enum_type m' n') := col 0 e.2.

(* Hypothesis G_vert_img : G_vert = ((@phi m' n') @/ G_lex). *)


Lemma P_feas : P `>` [poly0].
Proof. 
rewrite feasE.
exact/feas_bas0/(I0 G_lex_n0 (G_lex_vtx G_lex_verif)). 
Qed.

Lemma high_img : poly_graph P = 
  ((fun I => Simplex.point_of_basis b I) @/ (lex_graph A b)).
Proof. by exact/(img_lex_graph_poly_graph P_compact). Qed.

Lemma G_lex_repr : gisof G_lex (lex_graph A b) (to_feas_bas G_lex_n0 (G_lex_vtx G_lex_verif)).
Proof.
apply/repr_lex_graph=> c; rewrite -boundedE.
move/(compactP P_feas): P_compact; exact.
Qed.

Lemma repr_poly_graph : poly_graph P = (phi @/ G_lex).
Proof.
apply/esym/(gisof_diagram _ G_lex_repr _ high_img); [|exact:erefl].
move=> x xG_lex /=; rewrite Simplex.rel_points_of_basis.
rewrite /to_feas_bas; case: {-}_/idP=> // ?.
by rewrite -X_point_of_I.
Qed.

End ImgGraph.

(* --------------------------------------------------------------- *)

Section BoundPoly.

Context (m' n' : nat).
Local Notation m := m'.+1.
Local Notation n := n'.+1.

Context (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).
Context (bound_pos bound_neg : 'M[rat]_(n,m)).

Definition high_certif_func x i r :=
  (r *m A == row i (x%:M)) && (0) <=m (r^T).

Definition high_certif_fold Y x:=
  [forall i : 'I_n, high_certif_func x i (row i Y)]. 

Definition high_poly_bounded:= 
  high_certif_fold bound_pos 1%R && high_certif_fold bound_neg (-1)%R.

Local Notation P := (poly_of_syst (A,b)).

Hypothesis P_feas : P `>` [poly0].
Hypothesis bound_h : high_poly_bounded.

Definition max_bound_i (i : 'I_n):= 
  (Order.max '[-(row i bound_pos)^T, b] '[-(row i bound_neg)^T,b]).
Definition max_bound := \big[Order.max/0%R]_(i < n) max_bound_i i.

Lemma max_boundP (i : 'I_n):
  max_bound_i i <= max_bound.
Proof.
rewrite /max_bound.
have: i \in index_enum (ordinal_finType n) by rewrite mem_index_enum.
elim: (index_enum _)=> // h t IH.
rewrite in_cons big_cons le_maxr; case/orP.
- by move/eqP=> ->; rewrite lexx.
- by move/IH=> ->; rewrite orbT.
Qed.

Lemma high_poly_boundedP: compact P.
Proof.
- apply/compactP_Linfty; exists max_bound=> x.
  rewrite in_feasE inE => x_Ab i.
  case/andP: bound_h=> /forallP /(_ i) + /forallP /(_ i).
  case/andP=> /eqP Y_pos_A Y_pos_pos.
  case/andP=> /eqP Y_neg_A Y_neg_pos.
  move: (vdot_lev Y_pos_pos x_Ab) (vdot_lev Y_neg_pos x_Ab).
  rewrite !vdot_mulmx -!trmx_mul Y_pos_A Y_neg_A.
  rewrite [X in _ <= X]row_vdot mul_scalar_mx GRing.scale1r.
  move=> x_i_ge; rewrite [X in _ <= X]row_vdot mul_scalar_mx GRing.scaleN1r mxE.
  move=> x_i_le; apply/(le_trans _ (max_boundP i)).
  rewrite ler_norml; apply/andP; split.
  + rewrite ler_oppl le_maxr; apply/orP; left.
    by rewrite vdotNl ler_oppl GRing.opprK.
  + rewrite le_maxr; apply/orP; right.
    by rewrite vdotNl ler_oppr.
Qed.

End BoundPoly.

(* --------------------------------------------------------------- *)

Section FullDim.

Context (m' n' : nat).
Local Notation m := m'.+1.
Local Notation n := n'.+1.

Context (x0 : 'cV[rat]_n) (M W : 'M[rat]_n).
Context (S : {fset 'cV[rat]_n}).

Definition high_dim_full :=
  [&& x0 \in S,
    [forall i, col i M \in S] &
    let X := \matrix_(i < n) ((col i M)^T - (x0)^T) in X *m W == 1%:M
  ].

Hypothesis full_h : high_dim_full. 

Lemma high_dim_fullP: \pdim (conv S) = n.+1.
Proof.
apply/anti_leq/andP; split; first exact:adim_leSn.
case/and3P: full_h=> x0_vtx M_vtx full_M.
set M_seq := [seq col i M|i : 'I_n].
apply/leq_trans; [|apply/(dim_sub_affine (x0:=x0) (X:=M_seq))].
- rewrite adimN0_eq /= ?mk_affine_proper0 // dir_mk_affine.
  set X := \matrix_i ((col i M)^T - x0^T).
  set span_M := span _.
  suff ->: \dim span_M = \rank X.
  + rewrite ltnS row_leq_rank; apply/row_freeP.
    exists W; exact/eqP/full_M.
  rewrite /span_M.
  rewrite -[X in span X]in_tupleE span_matrix_cV.
  rewrite -[LHS]mxrank_tr -(rank_castmx (m':=n)) ?size_map -?enumT ?size_enum_ord //.
  move=> ?; congr mxrank; apply/matrixP=> p q.
  rewrite castmxE !mxE (tnth_nth 0) /= (nth_map 0) ?size_map -?enumT ?size_enum_ord //. 
  rewrite (nth_map 0) ?size_enum_ord // nth_ord_enum !mxE.
  by rewrite cast_ord_id.
- exact/in_conv.
- move=> x /mapP [i _ ->].
  move/forallP: M_vtx=> /(_ i).
  exact:in_conv.
Qed.

End FullDim.

(* --------------------------------------------------------------- *)

Section HighHirsch.

Context (m' n' : nat).
Local Notation m := m'.+1.
Local Notation n := n'.+1.

Context (A : 'M[rat]_(m,n)) (b : 'cV[rat]_m).

Context (G_lex : graph (enum_type m' n')) (G_vert : graph [choiceType of 'cV[rat]_n]).
Context (Y_pos Y_neg : 'M[rat]_(n,m)).
Context (x0 : 'cV[rat]_n) (M W : 'M[rat]_n).

Local Notation P := (poly_of_syst (A,b)).

Hypothesis enum_h : high_enum_algo A b G_lex.
Hypothesis img_h : G_vert = ((@phi m' n') @/ G_lex).
Hypothesis poly_bound : high_poly_bounded A Y_pos Y_neg.
Hypothesis G_lex_prop0 : G_lex != graph0 _.
Hypothesis poly_dim : high_dim_full x0 M W (vertex_set P).

Hypothesis G_vert_BFS : (diameter G_vert > m - n)%nat.

Lemma poly_facets: (#|` facets P| <= m)%nat.
Proof.
apply/(leq_trans (@facets_le _ _ (base_of_syst (A, b))))/(leq_trans (leq_imfset_card _ _ _)).
by rewrite size_enum_ord leqnn.
Qed.

Theorem high_algo_Hirsch :
  (diameter (poly_graph P) > 
    #|`facets P| - 
      (\pdim P).-1)%nat.
Proof.
have P_compact : compact P by exact/high_poly_boundedP/poly_bound.
have G_vert_poly: poly_graph P = G_vert.
- rewrite img_h; apply: repr_poly_graph.
  + exact: P_compact.
  + exact: enum_h.
  + exact: G_lex_prop0.
rewrite {2}(conv_vertex_set P_compact) (high_dim_fullP poly_dim) /=. 
apply/(leq_ltn_trans (n:=m - n))=> //;first 
  apply/leq_sub2r/poly_facets.
by rewrite G_vert_poly.
Qed.

End HighHirsch.

(* --------------------------------------------------------------- *)
