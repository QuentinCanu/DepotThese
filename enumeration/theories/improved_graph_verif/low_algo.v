From mathcomp Require Import all_ssreflect.
From Coq Require Import PArray Uint63.
From Bignums Require Import BigQ.
From Polyhedra Require Import extra_misc.
From PolyhedraHirsch Require Import extra_int extra_array rat_bigQ graph.
(* From PolyhedraHirschVerif Require Import low_algo. *)


Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Order.Theory.
Local Notation int63 := Uint63.int.

Module ImprovedVerif.

Definition vector := array bigQ.
Definition matrix := array vector.

(* 
  x is the vertex to be considered, while X is the matrix A^-1.
  the corresponding basis is given by I.
*)

Definition cmp_sat (A : matrix) (b : vector) 
  (I : array int63)
  (x : array bigQ) (X : array (array bigQ)) 
  (l : int63):=
  let Al := A.[l] in
  ILex.lex_func2_rel_ (Uint63.succ (length A))
  BigQ.compare 0%uint63 true
  (fun k i=> 
    if (i =? 0)%uint63 then (BigQUtils.bigQ_dot Al x,k) else
    if (Uint63.pred i =? I.[k])%uint63 then 
      (BigQUtils.bigQ_dot Al X.[k],Uint63.succ k)
    else (0%bigQ,k)
  )
  (fun k i=> 
    if (i =? 0)%uint63 then (b.[l],true) else
    if (Uint63.pred i =? l)%uint63 then ((-1)%bigQ,true) else
    (0%bigQ,true)
  ).
  
Definition cmp_vect (A : matrix) (b : vector) (I : array int63) (x : array bigQ) (X : array (array bigQ)) :=
  let cmp := PArrayUtils.mk_fun 
    (fun l=> cmp_sat A b I x X l)
    (length A) Eq
  in 
  (IFold.ifold (fun i '(acc,k)=>
  match cmp.[i] with
  |Lt => (false,k)
  |Gt => (true,k)
  |Eq => ((i =? I.[k])%uint63, Uint63.succ k)
  end) (length cmp) (true,0%uint63)).1.

Section Body.
Context (A : matrix) (b : vector) (G : graph).
Context (lbl_bas : array (array int63)).
Context (lbl_pt : array (array bigQ)).
Context (lbl_inv : array (array (array bigQ))).

(* We test validity of each vertex label*)

Definition sat_test (i : int63) :=
  let I := lbl_bas.[i] in
  let x := lbl_pt.[i] in
  let X := lbl_inv.[i] in
  cmp_vect A b I x X.

Definition n := length A.[0%uint63].
Definition card_bas_test (i : int63) := (length (lbl_bas.[i]) =? n)%uint63.
Definition vertex_test (i : int63) := (card_bas_test i) && (sat_test i).
  
Definition vertex_consistent := IFold.iall (fun i=> vertex_test i) (length G).
End Body.
End ImprovedVerif.