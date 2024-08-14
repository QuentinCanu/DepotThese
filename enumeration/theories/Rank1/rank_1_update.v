Require Import PArray Uint63.
From Bignums Require Import BigQ.
From mathcomp Require Import all_ssreflect all_algebra.
From Polyhedra Require Import extra_misc inner_product vector_order.
From PolyhedraHirsch Require Import low_graph extra_array extra_int array_set rat_bigQ diameter img_graph refinement.
From ReductionEffect Require Import PrintingEffect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

(* ---------------------------------------------------------------------------- *)

Local Notation int63 := Uint63.int.

(* ---------------------------------------------------------------------------- *)

Module Rank1Certif.

(* ------------------------------------------------------------------ *)


(* Given the reduced slack matrix $M^I$, sat_lex checks that the lex-basis I is lex-feasible*)
Definition sat_lex (m : Uint63.int) (M : array (array bigQ)) (I : array int63):=
  let '(test, _, _) := (IFold.ifold (fun i '(acc, kI, kM)=>
    if acc then
      if (i =? I.[kI])%uint63 then
        (acc,Uint63.succ kI, kM)
      else
        let '(cmp, _) := IFold.ifold (fun j '(cmp, kI2)=>
          if (j =? 0)%uint63 then
            if cmp is Eq then ((M.[0].[kM] ?= 0)%bigQ, kI2) else (cmp, kI2)
          else
            if (j =? I.[kI2])%uint63 then
              if cmp is Eq then ((M.[Uint63.succ kI2].[kM] ?= 0)%bigQ, Uint63.succ kI2) else (cmp, Uint63.succ kI2)
            else
              (cmp, kI2)
        ) (Uint63.succ i) (Eq, 0%uint63)
        in
        let acc := if cmp is Lt then false else true in
        (acc, kI, Uint63.succ kM)
    else
      (acc, kI, kM)
  ) m (true,0%uint63,0%uint63)) in test.

(* ------------------------------------------------------------------ *)

(* update constructs the reduced slack matrix $M^J$ from $M^I$, r and s such that J = I \ {s} U {r} *)
Definition update
  (m n : Uint63.int)
  (I : array Uint63.int) (r s : Uint63.int)
  (M : array (array bigQ)) (r_k : Uint63.int):=
  let Is := I.[s] in
  let Ms := M.[Uint63.succ s] in
  let Mrs := Ms.[r_k] in
  let N := PArrayUtils.mk_fun (fun _ => make (m - n)%uint63 0%bigQ) (Uint63.succ n) (make 1%uint63 0%bigQ) in
  let M0 := M.[0%uint63] in
  let Mr0 := M0.[r_k] in
  let '(_, _, _, C) := IFold.ifold (fun i '(kI,kM,kC,C)=>
    if (i =? I.[kI])%uint63 then
      if (i =? Is)%uint63 then
        let c := BigQ.red (Mr0 / Mrs)%bigQ in
        (Uint63.succ kI, kM, Uint63.succ kC, C.[kC <- c])
      else
        (Uint63.succ kI, kM, kC, C)
    else
      if (i =? r)%uint63 then
        (kI, Uint63.succ kM, kC, C)
      else
        let c := BigQ.red (M0.[kM] - (Mr0 / Mrs) * Ms.[kM])%bigQ in
        (kI, Uint63.succ kM, Uint63.succ kC, C.[kC <- c])
    ) m (0%uint63, 0%uint63, 0%uint63, make (m-n)%uint63 0%bigQ)
  in let N := N.[0 <- C] in
  let '(_, _, N) := IFold.ifold 
    (fun j '(kI, kN, N)=>
      if (j =? I.[kI])%uint63 then
        if (j =? Is)%uint63 then
          (Uint63.succ kI, kN, N)
        else
          let '(_, _, _, C) := IFold.ifold (fun i '(kIl,kM,kC,C)=>
            if (i =? I.[kIl])%uint63 then
              if (i =? Is)%uint63 then
                let c := BigQ.red (M.[Uint63.succ kI].[r_k] / Mrs)%bigQ in
                (Uint63.succ kIl, kM, Uint63.succ kC, C.[kC <- c])
            else
              (Uint63.succ kIl, kM, kC, C)
          else
            if (i =? r)%uint63 then
              (kIl, Uint63.succ kM, kC, C)
            else
              let c := BigQ.red (M.[Uint63.succ kI].[kM] - (M.[Uint63.succ kI].[r_k] * Ms.[kM]) / Mrs)%bigQ in
            (kIl, Uint63.succ kM, Uint63.succ kC, C.[kC <- c])
        )
          m (0%uint63, 0%uint63, 0%uint63, make (m-n)%uint63 0%bigQ)
        in (Uint63.succ kI, Uint63.succ kN, N.[Uint63.succ kN <- C])
    else
      if (j =? r)%uint63 then
        let '(_, _, _, C) := IFold.ifold (fun i '(kIl,kM,kC,C)=>
          if (i =? I.[kIl])%uint63 then
            if (i =? Is)%uint63 then
              let c := BigQ.red (1 / Mrs) in
              (Uint63.succ kIl, kM, Uint63.succ kC, C.[kC <- c])
            else
              (Uint63.succ kIl, kM, kC, C)
          else
            if (i =? r)%uint63 then
              (kIl, Uint63.succ kM, kC, C)
            else
              let c := BigQ.red (- Ms.[kM] / Mrs)%bigQ in
              (kIl, Uint63.succ kM, Uint63.succ kC, C.[kC <- c])
    )
      m (0%uint63, 0%uint63, 0%uint63, make (m-n)%uint63 0%bigQ)
      in (kI, Uint63.succ kN, N.[Uint63.succ kN <- C])
      else
        (kI, kN, N)
        ) m (0%uint63, 0%uint63, N) in N.

Definition explore
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (main : array (option ((array (array bigQ)))))
  (order : array int63):=
  let m := length A in
  let n := length A.[0] in
  IFold.ifold
    (fun i main=>
      let (idx,rs) := certif_pred.[order.[i]] in
      let (r,s) := rs in
        let I := certif_bases.[idx] in
        if main.[idx] is Some M then
          let Is := I.[s] in
          let Ms := M.[Uint63.succ s] in
          let '(_, r_k) := IFold.ifold (fun i '(kI,r_k)=>
            if (i=?I.[kI])%uint63 then
              (Uint63.succ kI, r_k)
            else if (i=?r)%uint63 then
              (kI, r_k) else (kI, Uint63.succ r_k) 
            ) (Uint63.succ r) (0%uint63,0%uint63) in
          let Mrs := Ms.[r_k] in
          if (Mrs ?= 0)%bigQ is Eq then main else
            let M' := update m n I r s M r_k in
            if sat_lex m M' certif_bases.[order.[i]] then 
              main.[order.[i] <- Some M'] 
            else main
          else main) 
    (length order) main.

(* initial constructs the reduced slack matrix of the root idx *)
Definition initial
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)) :=
  let I := certif_bases.[idx] in
  let m := length A in
  let n := length A.[0] in
  let M := PArrayUtils.mk_fun (fun _ => make (m-n)%uint63 0%bigQ) (Uint63.succ n) (make 1%uint63 0%bigQ) in
  let '(_,_,C) := IFold.ifold 
    (fun i '(kI,kC,C)=>
      if (i=?I.[kI])%uint63 then
        (Uint63.succ kI, kC, C)
      else
        let c := ((BigQUtils.bigQ_dot A.[i] x) - b.[i])%bigQ in
        (kI, Uint63.succ kC, C.[kC <- c])
    ) m (0%uint63,0%uint63,make (m-n)%uint63 0%bigQ) in
  let M := M.[0%uint63 <- C] in
  let M := (IFold.ifold (fun j M=>
    let k := I.[j] in
    let '(_,_,C) := IFold.ifold 
      (fun i '(kI,kC,C)=>
        if (i=?I.[kI])%uint63 then
          (Uint63.succ kI, kC, C)
        else
          let c := (-(BigQUtils.bigQ_dot A.[i] inv.[j]))%bigQ in
          (kI, Uint63.succ kC, C.[kC <- c])
      ) m (0%uint63,0%uint63,make (m-n)%uint63 0%bigQ)
    in M.[Uint63.succ j <- C]
  ) n M) in M.

Definition initial_main
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)):
  array (option ((array (array bigQ)))) :=
  let main := make (length certif_bases) None in
  let M := initial A b certif_bases idx x inv in
  if sat_lex (length A) M (certif_bases.[idx]) then main.[idx <- Some M] else main.

(* explore_from_initial construct the array main containing all the reduced slack matrices *)
Definition explore_from_initial
  A b certif_bases certif_pred idx x inv order:=
  explore A b certif_bases certif_pred (initial_main A b certif_bases idx x inv) order.

Definition vertex_certif
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ))
  (order : array int63):=
  let main := explore_from_initial A b certif_bases certif_pred idx x inv order in
  PArrayUtils.all (fun x => isSome x) main.

End Rank1Certif.

Module R1 := Rank1Certif.