Require Import Setoid PArray Uint63.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import PArith.BinPos PArith.BinPosDef.
Require Import NArith.BinNat NArith.BinNatDef.
From Bignums Require Import BigQ.
From Polyhedra Require Import extra_misc inner_product vector_order.
From PolyhedraHirsch Require Import low_graph extra_array extra_int array_set rat_bigQ img_graph refinement diameter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

(* Open Scope ring_scope. *)

Local Notation int63 := Uint63.int.

(* --------------------------------------------------------------------------------------------------- *)

Module Common.

Definition vector := array bigQ.
Definition matrix := array vector.
Definition m (A : matrix) := length A.
Definition n (A : matrix) := length A.[0%uint63].

(* lex_point is the type of perturbed "points" of the lex-graph*) 
(* It is a matrix represented by columns *)
Definition lex_point := matrix.
Definition lex_label := ((array int63) * lex_point)%type.
Definition lex_mapping := array lex_label.

Definition bas (lbl : lex_mapping) (i : int63)  := lbl.[i].1.
Definition point (lbl : lex_mapping) (i : int63) := lbl.[i].2.

Definition vtx_point := vector.
Definition vtx_label := vtx_point.
Definition vtx_mapping := array vtx_label.

Definition compute_test (G : graph) := IFold.iall^~ (length G).

End Common.

Module Com := Common.

Section CommonEquiv.
Context (G : graph).

Definition compute_test := iall^~ (length G).

Lemma compute_testP f: compute_test f -> forall i, mem_vertex G i -> f i.
Proof.
move/allP=> compu i ig; apply/compu.
by rewrite mem_irangeE le0x.
Qed.

End CommonEquiv.

(* --------------------------------------------------------------------------------------------------- *)

Module FormatComputation.

(* Performs all format computation, i.e. correct length of arrays ... *)

Definition poly_format (A : Com.matrix) (b : Com.vector):=
  [&& (0 <? Com.m A)%uint63, (0 <? Com.n A)%uint63,
      PC.pre_length_computation b (Com.m A) &
      PC.pre_mx_computation A (Com.m A) (Com.n A)]. 

Definition basis_format (A : Com.matrix) (x : array int63):=
  PC.pre_arr_set_computation (fun a b=> (a <? b)%uint63)
    (fun i=> (i <? Com.m A)%uint63) x.

Definition point_format (A : Com.matrix) (x : array (array bigQ)):=
  PC.pre_mx_computation x (Uint63.succ (Com.m A)) (Com.n A). 
    
Definition lex_vert_format (A : Com.matrix) (x : Com.lex_label):=
  basis_format A x.1 && point_format A x.2.

Definition lex_graph_format (A : Com.matrix) (g : graph) (l : Com.lex_mapping):=
  PC.pre_graph_computation (fun x y=> PArrayUtils.lt_array_int x.1 y.1)
  (fun x=> lex_vert_format A x) g l.

Definition lex_graph_n0 (g : graph):= (0 <? length g)%uint63.

Definition vtx_graph_format (A : Com.matrix) 
  (g : graph) (l : Com.vtx_mapping):=
  PC.pre_graph_computation BigQUtils.BQltx_order 
    (fun x=> (length x =? Com.n A)%uint63) g l.

Definition bound_format (A : Com.matrix) (a : array (array bigQ)):=
  PC.pre_mx_computation a (Com.n A) (Com.m A).

Definition inv_format (A : Com.matrix) (a : array (array bigQ)):=
  PC.pre_mx_computation a (Com.n A) (Com.n A).

End FormatComputation.

Module FC := FormatComputation.

Section FormatEquiv.

Definition poly_format (A : Com.matrix) (b : Com.vector):=
  [&& (0 < Com.m A)%O, (0 < Com.n A)%O,
    pre_length_computation b (Com.m A) &
    pre_mx_computation A (Com.m A) (Com.n A)].

Definition basis_format (A : Com.matrix) (x : array int63):=
  pre_arr_set_computation (fun a b=> (a < b)%O)
    (fun i=> (i < Com.m A)%O) x.

Definition point_format (A : Com.matrix) (x : array (array bigQ)):=
  pre_mx_computation x (Uint63.succ (Com.m A)) (Com.n A). 
    
Definition lex_vert_format (A : Com.matrix) (x : Com.lex_label):=
  basis_format A x.1 && point_format A x.2.

Definition lex_graph_format (A : Com.matrix) (g : graph) (l : Com.lex_mapping):=
  pre_graph_computation (fun x y=> lt_array_int x.1 y.1)
  (fun x=> lex_vert_format A x) g l.

Definition lex_graph_n0 (g : graph) := (0 < length g)%O.

Definition vtx_graph_format (A : Com.matrix) 
  (g : graph) (l : Com.vtx_mapping):=
  pre_graph_computation BQltx_order 
    (fun x=> (length x == Com.n A)) g l.

Definition bound_format (A : Com.matrix) (a : array (array bigQ)):=
  pre_mx_computation a (Com.n A) (Com.m A).

Definition inv_format (A : Com.matrix) (a : array (array bigQ)):=
  pre_mx_computation a (Com.n A) (Com.n A).

Lemma poly_formatE A b: FC.poly_format A b = poly_format A b.
Proof. by rewrite /FC.poly_format -!ltEint pre_length_computationE pre_mx_computationE.
Qed.

Lemma lex_graph_formatE A g l:
  FC.lex_graph_format A g l = lex_graph_format A g l.
Proof.
rewrite /FC.lex_graph_format pre_graph_computationE; repeat congr andb.
- by rewrite !rel_sortedP; apply/(sorted_rel_equiv)=> //;
  [move => ??; apply/erefl|move=> ???? -> ->; rewrite lt_array_intE].
- apply/eq_all=> ?; congr andb.
  + by rewrite /FC.basis_format pre_arr_set_computationE.
  + by rewrite /FC.point_format pre_mx_computationE.
Qed.

Lemma lex_graph_n0E g:
  FC.lex_graph_n0 g = lex_graph_n0 g.
Proof. by rewrite /FC.lex_graph_n0 -ltEint. Qed.

Lemma vert_graph_formatE A g l:
  FC.vtx_graph_format A g l = vtx_graph_format A g l.
Proof.
rewrite /FC.vtx_graph_format pre_graph_computationE; repeat congr andb.
- by rewrite !rel_sortedP; apply/(sorted_rel_equiv)=> //;
    [move=> ??; apply/erefl|move=> ???? -> ->; rewrite BQltx_orderE].
- by apply/eq_all=> ?; rewrite eqEint.
Qed.

Lemma bound_formatE Po y:
  FC.bound_format Po y = bound_format Po y.
Proof. by rewrite /FC.bound_format pre_mx_computationE. Qed.

Lemma inv_formatE Po y:
  FC.inv_format Po y = inv_format Po y.
Proof. by rewrite /FC.inv_format pre_mx_computationE. Qed.

End FormatEquiv.

(* --------------------------------------------------------------------------------------------------- *)

Module PolyBoundedComputation.

(* bounded_Po_test checks that every coordinate is bounded        *)
(* To do so, let y_pos y_neg : array (array bigQ), such that:  *)
(* -> forall i < n, y_pos.[i] *m A = (j == i)_(j < n)                   *)
(* -> forall i < n, y_neg.[i] *m A = - (j == i)_(j < n)                 *)
(* -> forall i < n, y.[i].1 and y.[i].2 are nonnegative               *)


Definition bound_certif_fold
  (A: Com.matrix) (y : array (array bigQ)) (x : bigQ):=
  IFold.iall (fun i=>
    BigQUtils.eq_array_bigQ 
          (BigQUtils.weighted_lines y.[i] A)
          (BigQUtils.delta_line (Com.n A) i x)
    && PArrayUtils.all BigQUtils.bigQ_ge0 y.[i]
  ) (length y).


Definition bounded_Po_test (A : Com.matrix) (y_pos : array (array bigQ)) 
  (y_neg : array (array bigQ)) :=
    bound_certif_fold A y_pos 1%bigQ &&
    bound_certif_fold A y_neg (-1)%bigQ.

End PolyBoundedComputation.

Module PBC := PolyBoundedComputation.

Section PolyBoundedEquiv.

Context {A : Com.matrix}.

Definition bound_certif_fold (y : array (array bigQ)) (x : bigQ):=
  iall (fun i=>
    eq_array_bigQ 
      (weighted_lines y.[i] A)
      (BigQUtils.delta_line (Com.n A) i x)
    && arr_all BigQUtils.bigQ_ge0 y.[i]
  ) (length y).


Definition bounded_Po_test (y_pos y_neg : array (array bigQ)):=
  bound_certif_fold y_pos 1%bigQ && bound_certif_fold y_neg (-1)%bigQ.

Lemma bound_certif_foldE y x:
  PBC.bound_certif_fold A y x = bound_certif_fold y x.
Proof.
rewrite /PBC.bound_certif_fold iallE; apply/eq_all=> i.
by rewrite eq_array_bigQE weighted_linesE arr_allE.
Qed.

Lemma bounded_Po_testE y_pos y_neg:
  PBC.bounded_Po_test A y_pos y_neg = bounded_Po_test y_pos y_neg.
Proof. by congr andb; rewrite bound_certif_foldE. Qed.

End PolyBoundedEquiv.

(* --------------------------------------------------------------------------------------------------- *)

Module LexCertifComputation.

(* 
  Verfify that a given graph g_lex : graph.graph and its labeling l_lex : Com.lex_mapping
  is the graph of lexicographic bases of a polyhedron Po : Com.polyType
*)

Section Defs.

Definition sat_ineq (m i : int63) (a : array bigQ) (b : bigQ) (x : Com.lex_point):=
  if (PArrayUtils.fold_pair
      (fun bv xv acc=> if acc is Eq then (bv ?= (BigQUtils.bigQ_dot a xv))%bigQ else acc)
    (BigQUtils.perturbed_line m i b (-1)%bigQ) x Eq) is Gt 
  then false else true. 

Definition sat_eq (m i : int63) (a : array bigQ) (b : bigQ) (x : Com.lex_point):=
  BigQUtils.eq_array_bigQ (BigQUtils.bigQ_mul_row_mx a x) 
    (BigQUtils.perturbed_line m i b (-1)%bigQ).

Definition sat_Po (A : Com.matrix) (b : Com.vector) (x : Com.lex_point) :=
  IFold.iall (fun i => sat_ineq (Com.m A) i A.[i] b.[i] x) (Com.m A).

Definition mask_eq (A : Com.matrix) (b : Com.vector) (m : array int63) (x : Com.lex_point):=
  IFold.iall (fun i=> sat_eq (Com.m A) m.[i] A.[m.[i]] b.[m.[i]] x) (length m).

End Defs.

Section Body.
Context (A : Com.matrix) (b : Com.vector) (G : graph) (lbl : Com.lex_mapping).

(* We test validity of each vertex label*)
Definition sat_test (i : int63) := sat_Po A b (Com.point lbl i).
Definition bas_eq_test (i : int63) := mask_eq A b (Com.bas lbl i) (Com.point lbl i).
Definition card_bas_test (i : int63) := (length (Com.bas lbl i) =? (Com.n A))%uint63.
Definition vertex_test (i : int63) := [&& (card_bas_test i), (sat_test i) & (bas_eq_test i)].

Definition vertex_consistent := Com.compute_test G vertex_test.

(* We test the graph structure*)
Definition regularity_test (i : int63) := (GraphUtils.nb_neighbours G i =? (Com.n A))%uint63.
Definition basI_test (i : int63) := GraphUtils.neighbour_all 
  (fun j => 
    ((AIC.array_inter 
      (fun i j=> (i <? j)%uint63) (Com.bas lbl i) (Com.bas lbl j)) =? Uint63.pred (Com.n A))%uint63)
    G i.

Definition struct_test i :=
    regularity_test i && basI_test i.

Definition struct_consistent :=
  Com.compute_test G struct_test.

(* Definition lex_certif_algo := vertex_consistent && struct_consistent. *)

End Body.
End LexCertifComputation.

Module LCA := LexCertifComputation.

Section LexCertifEquiv.
Section Def.

Definition sat_ineq (m i : int63) (a : array bigQ) (b : bigQ) (x : Com.lex_point):=
  let pert_b := BigQUtils.perturbed_line m i b (-1)%bigQ in 
  let res := arr_fold_pair
    (fun bv xv acc=> if acc is Eq then (bv ?= (BigQUtils.bigQ_dot a xv))%bigQ else acc)
  pert_b x Eq in
  if res is Gt then false else true. 

Definition sat_eq (m i : int63) (a : array bigQ) (b : bigQ) (x : Com.lex_point):=
  let pert_b := BigQUtils.perturbed_line m i b (-1)%bigQ in 
  eq_array_bigQ (bigQ_mul_row_mx a x) pert_b.

Definition sat_Po (A : Com.matrix) (b : Com.vector) (x : Com.lex_point) :=
  iall (fun i => sat_ineq (Com.m A) i A.[i] b.[i] x) (Com.m A).

Definition mask_eq (A : Com.matrix) (b : Com.vector) (m : array int63) (x : Com.lex_point):=
  iall (fun i=> sat_eq (Com.m A) m.[i] A.[m.[i]] b.[m.[i]] x) (length m).

Context (A : Com.matrix) (b : Com.vector) (G : graph) (lbl : Com.lex_mapping).

Definition sat_test (i : int63) := sat_Po A b (Com.point lbl i).
Definition bas_eq_test (i : int63) := mask_eq A b (Com.bas lbl i) (Com.point lbl i).
Definition card_bas_test (i : int63) := (length (Com.bas lbl i) == (Com.n A)).

Definition vertex_test (i : int63) := [&& (card_bas_test i), (sat_test i) & (bas_eq_test i)].

Definition vertex_consistent := compute_test G vertex_test.

Definition regularity_test (i : int63) := (nb_neighbours G i == (Com.n A)).
Definition basI_test (i : int63) := neighbour_all 
  (fun j => 
    ((array_inter 
      (fun i j=> (i < j)%O) (Com.bas lbl i) (Com.bas lbl j)) == Uint63.pred (Com.n A)))
    G i.

Definition struct_test i :=
  regularity_test i && basI_test i.
  
Definition struct_consistent :=
  (compute_test G struct_test).

(* Definition lex_certif_algo := vertex_consistent && struct_consistent. *)

End Def.
Section Equiv.

Lemma vertex_consistentE A b g lbl:
  LCA.vertex_consistent A b g lbl = vertex_consistent A b g lbl.
Proof.
rewrite /LCA.vertex_consistent /Com.compute_test iallE.
apply/eq_all=> i; congr andb; rewrite /LCA.card_bas_test ?eqEint //.
congr andb.
- rewrite /LCA.sat_test /LCA.sat_Po.
  rewrite iallE; apply/eq_all=> k. 
  rewrite /LCA.sat_ineq arr_fold_pairE.
  rewrite /sat_ineq /arr_fold_pair /Com.point.
  by elim: zip Eq.
- rewrite /LCA.bas_eq_test /LCA.mask_eq.
  rewrite iallE; apply/eq_all=> k.
  rewrite /LCA.sat_eq.
  by rewrite eq_array_bigQE; congr andb; rewrite ?bigQ_mul_row_mxE.
Qed.

Lemma struct_consistentE A g lbl:
  LCA.struct_consistent A g lbl = struct_consistent A g lbl.
Proof.
rewrite /LCA.struct_consistent /Com.compute_test iallE; apply/eq_all=> i.
congr andb; first by rewrite /LCA.regularity_test eqEint.
rewrite /LCA.basI_test neighbour_allE; apply/eq_all=> j.
by rewrite array_interE eqEint.
Qed.

(* Lemma lex_certif_algoE A b g lbl: 
  LCA.lex_certif_algo A b g lbl = lex_certif_algo A b g lbl.
Proof. by congr andb; rewrite ?vertex_consistentE ?struct_consistentE //. Qed. *)

End Equiv.
End LexCertifEquiv.

Section LexCertifProofs.

Lemma sat_ineqP (m i : int63) (a : array bigQ) (b : bigQ) (u : Com.lex_point) :
  length u = Uint63.succ m ->
  sat_ineq m i a b u = 
  BQlex_order (BigQUtils.perturbed_line m i b (-1)%bigQ)
    (bigQ_mul_row_mx a u).
Proof.
move=> len_u.
rewrite /BQlex_order /bigQ_mul_row_mx.
rewrite /lex_array_rel /lex_array_rel_ /arr_fold_pair.
rewrite length_arr_map !length_set length_make -len_u leb_length eqxx /=.
rewrite rAS_map /sat_ineq /arr_fold_pair.
set F := (foldl _ _ _); set F' := (foldl _ _ _).
suff ->: F = F' by [].
rewrite /F /F'.
move/(congr1 int_to_nat): (len_u). 
set pert_b := BigQUtils.perturbed_line _ _ _ _.
rewrite -(size_arr_to_seq u).
have <-: size (arr_to_seq pert_b) = Uint63.succ m by
  rewrite size_arr_to_seq !length_set !length_make -len_u leb_length.
elim/last_ind: (arr_to_seq pert_b) (arr_to_seq u)=> [|t h IH]; elim/last_ind=> [|t' h' _] //.
- by rewrite size_rcons.
- by rewrite size_rcons.
- rewrite !size_rcons => /succn_inj size_tt'.
  rewrite map_rcons !zip_rcons ?size_map // !foldl_rcons /=.
  by move: (IH t' size_tt')=> ->; rewrite !bigQ_dotE.
Qed.

Context {A : Com.matrix} {b : Com.vector} {g : graph} {lbl : Com.lex_mapping}.

Lemma lex_card_bas i: card_bas_test A lbl i-> length (Com.bas lbl i) = (Com.n A).
Proof. by move=> /eqP ->. Qed.


Lemma lex_basI i j: 
  mem_vertex g i -> mem_vertex g j ->
  mem_edge g i j ->
  basI_test A g lbl i ->
  array_inter (fun i j=> (i < j)%O) 
    (Com.bas lbl i) (Com.bas lbl j) = Uint63.pred (Com.n A).
Proof.
move=> ig jg ij_g /neighbour_allP.
move/(_ ig); move/neighboursP: ij_g=> /(_ ig jg) [k k_nei j_eq] /(_ k k_nei).
by rewrite j_eq /= => /(_ jg) /eqP ->.
Qed.

Lemma lex_regularity i: regularity_test A g i -> nb_neighbours g i = (Com.n A).
Proof. by move=> /eqP. Qed.

Lemma lex_sat_Po k i: (k < Com.m A)%O ->
  sat_test A b lbl i ->
  sat_ineq (Com.m A) k A.[k] b.[k] (Com.point lbl i).
Proof. by move=> k_Po /allP; apply; rewrite mem_irangeE le0x k_Po. Qed.

Lemma lex_mask_eq i j: (j < length (Com.bas lbl i))%O -> 
  bas_eq_test A b lbl i ->
  sat_eq (Com.m A) (Com.bas lbl i).[j]
    A.[(Com.bas lbl i).[j]] b.[(Com.bas lbl i).[j]]
    (Com.point lbl i).
Proof. by move=> j_bas /allP /(_ j); apply; rewrite mem_irangeE le0x j_bas. Qed.
  

End LexCertifProofs.

(* --------------------------------------------------------------- *)

(* Definition BQlex_label := Com.lex_label.
Definition BQlex_mapping := Com.lex_mapping.

Definition BQvert_label := (array bigQ)%type.
Definition BQvert_mapping := array (BQvert_label). *)

Module ImgGraphLexComputation.

(* 
  Given two graphs g_lex and g_vert associated with their labels
  l_lex and l_simpl, img_lex_graph verifies the g_vert is the image graph
  of g_lex. It makes uses of three certificates
  (morph morph' : array int) (edge_inv : array (array (int * int))) 
*)

Definition img_lex_graph morph morph' edge_inv 
  g_lex lbl_lex g_vert lbl_vtx := 
  ILGC.img_label_graph (fun x : Com.lex_label => x.2.[0%uint63]) BigQUtils.eq_array_bigQ
  morph morph' edge_inv (g_lex, lbl_lex) (g_vert, lbl_vtx).

End ImgGraphLexComputation.

Module IGLexC := ImgGraphLexComputation.

Section ImgGraphLexEquiv.

Definition img_lex_graph morph morph' edge_inv 
  g_lex lbl_lex g_vert lbl_vtx := 
  img_label_graph (fun x : Com.lex_label => x.2.[0%uint63]) eq_array_bigQ
  morph morph' edge_inv (g_lex,lbl_lex) (g_vert,lbl_vtx).

Lemma img_lex_graphE morph morph' edge_inv g_lex lbl_lex g_vert lbl_vtx:
  IGLexC.img_lex_graph morph morph' edge_inv g_lex lbl_lex g_vert lbl_vtx =
  img_lex_graph morph morph' edge_inv g_lex lbl_lex g_vert lbl_vtx.
Proof. 
rewrite /IGLexC.img_lex_graph img_label_graphE; congr andb. 
by rewrite /img_label; apply/eq_all=> i /=; rewrite eq_array_bigQE. 
Qed.

End ImgGraphLexEquiv.

(* -------------------------------------------------------------------- *)

Module DimensionFullComputation.

(* Given an array (lbl : BQvert_mapping) of Q^n points, dim_full_test
  verifies that given n points x_k and one origin x_0,
  the matrix \matrix_k (x_k - x_0)^T is invertible *)

Definition inverse_line_i (lbl : Com.vtx_mapping) 
  (map_ : array int63) (origin : int63) 
  (inv : array (array bigQ)) n i:=
  let: rV_i:= 
    BigQUtils.bigQ_add_rV (lbl.[map_.[i]]) (BigQUtils.bigQ_scal_rV (-1)%bigQ lbl.[origin]) in
  BigQUtils.eq_array_bigQ (BigQUtils.bigQ_mul_row_mx rV_i inv) (BigQUtils.delta_line n i 1%bigQ).

Definition dim_full_test (A : Com.matrix) (lbl : Com.vtx_mapping)
  (map_ : array int63) (origin : int63) (inv : array (array bigQ)):=
    [&& 
      (length map_ =? Com.n A)%uint63,
      PArrayUtils.all (fun x=> (x <? length lbl)%uint63) map_,
      (origin <? length lbl)%uint63 &
      IFold.iall
        (fun i=> inverse_line_i lbl map_ origin inv (Com.n A) i) 
      (length map_)
    ].


End DimensionFullComputation.

Module DFC := DimensionFullComputation.

Section DimensionFullEquiv.

Definition inverse_line_i (lbl : Com.vtx_mapping) 
  (map_ : array int63) (origin : int63) 
  (inv : array (array bigQ)) n i:=
  let: rV_i:= 
    bigQ_add_rV (lbl.[map_.[i]]) (bigQ_scal_rV (-1)%bigQ lbl.[origin]) in
  eq_array_bigQ (bigQ_mul_row_mx rV_i inv) (BigQUtils.delta_line n i 1%bigQ).

(* Definition inv_format_test (inv : array (array bigQ))
  (Po : Com.polyType):=
  (length inv == (Com.n Po)) &&
  arr_all (fun line=> (length line == (Com.n Po))) inv.

Definition map_test (lbl : BQvert_mapping) (map_ : array int63) (Po : Com.polyType):=
  [&& (length map_ == (Uint63.succ (Com.n Po))),
      arr_all (fun x=> (x < length lbl)%O) map_ &
      is_lti_sorted map_]. *)

Definition dim_full_test (A : Com.matrix) (lbl : Com.vtx_mapping)
  (map_ : array int63) (origin : int63) (inv : array (array bigQ)):=
  [&&
    (length map_ == Com.n A), 
    arr_all (fun x=> (x < length lbl)%O) map_,
    (origin < length lbl)%O &
    iall
      (fun i=> inverse_line_i lbl map_ origin inv (Com.n A) i)
    (length map_)
  ].

Lemma dim_full_testE lbl map_ origin inv Po: 
  DFC.dim_full_test lbl map_ origin inv Po = 
  dim_full_test lbl map_ origin inv Po.
Proof.
repeat congr andb; rewrite ?eqEint //.
- by rewrite arr_allE; apply/eq_all=> ?; rewrite ltEint.
- rewrite /DFC.dim_full_test iallE; apply/eq_all=> i.
  rewrite /DFC.inverse_line_i /= eq_array_bigQE. 
  by rewrite bigQ_mul_row_mxE bigQ_add_rVE bigQ_scal_rVE.
Qed.

End DimensionFullEquiv.

(* --------------------------------------------------------------- *)

Module HirschUtils.

(*
  Given a correct witness vertex, 
  this function performs a BFS from this point
  to prove there is a path bigger than 
  the bound defined by the Hirsch Conjecture
*)

Definition diameter_check (A : Com.matrix) g x :=
  [&& ((Com.n A) <? (Com.m A))%uint63, GraphUtils.mem_vertex g x &
      ((Com.m A) - (Com.n A) <? nat_to_int (DC.BFS g x))%uint63].

Definition diameter_exact g k :=
  (nat_to_int (DC.diameter_BFS g) =? k)%uint63.

End HirschUtils.

Section Hirsch.

Definition diameter_check (A : Com.matrix) g x :=
  [&& 
    ((Com.n A) < (Com.m A))%O, mem_vertex g x &
    (((Com.m A) - (Com.n A))%uint63 < nat_to_int (BFS g x))%O
  ].

Definition diameter_exact g k :=
  (nat_to_int (diameter_BFS g) == k).

Section Equiv.

Lemma diameter_checkE (A : Com.matrix) g x:
  HirschUtils.diameter_check A g x = diameter_check A g x.
Proof. by rewrite /HirschUtils.diameter_check BFSE mem_vertexE -!ltEint. Qed.

Lemma diameter_exactE g k:
  HirschUtils.diameter_exact g k = diameter_exact g k.
Proof. by rewrite /HirschUtils.diameter_exact eqEint low_diameterE. Qed.

End Equiv.

End Hirsch.
