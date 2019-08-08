From mathcomp Require Import all_ssreflect.

Require Import BinNat.

Require Import codegen.codegen.

Open Scope N_scope.

Definition len : nat := 634.
Definition m : nat := 397.
Definition r := 31.
Definition u := 11.
Definition s := 7.
Definition t := 15.
Definition l := 18.
Definition a := 2567483615.
Definition b := 2636928640.
Definition c := 4022730752.

Definition upper_mask := 2147483648.
Definition whole_mask := upper_mask * 2 - 1.
Definition lower_mask := upper_mask - 1.

Record random_state := {i : nat; x : seq N}.

Fixpoint generate (rest : nat) (acc : seq N) : seq N :=
  match rest with
  | 0%nat => acc
  | 1%nat => acc
  | S m => generate m ((N.land (1812433253 * (N.lxor (head 0 acc) (N.shiftr (head 0 acc) 30)) + N.of_nat(len - rest) + 1) whole_mask) :: acc)
  end.

Definition initialize (seed : N) : random_state :=
  {|
    i := 0;
    x := rev (generate len  (N.land seed whole_mask :: nil));
  |}.

Definition next (rand : random_state) : (N * random_state) :=
  let data := x rand in
  let ind := i rand in
  let next_ind := Nat.modulo (ind +  1%nat) len in
  let far_ind := Nat.modulo (ind + m) len in
  let z := N.lor (N.land (nth 0 data ind) upper_mask) (N.land (nth 0 data next_ind) lower_mask) in
  let xi := N.lxor (N.lxor (nth 0 data far_ind) (N.shiftr z 1)) (if N.eqb (N.land z 1) 0 then 0 else a) in
  let y1 := N.lxor xi (N.shiftr xi u) in
  let y2 := N.lxor y1 (N.land (N.shiftl y1 s) b) in
  let y3 := N.lxor y2 (N.land (N.shiftl y2 t) c) in
  let y4 := N.lxor y3 (N.shiftl y3 l) in
  let next_rand := {|
        i := next_ind;
        x := set_nth 0 data ind xi;
      |} in
  (y4, next_rand).

CodeGen Terminate Monomorphization N.land.
CodeGen Terminate Monomorphization N.lor.
CodeGen Terminate Monomorphization N.lxor.
CodeGen Terminate Monomorphization N.shiftl.
CodeGen Terminate Monomorphization N.shiftr.
CodeGen Monomorphization initialize.
CodeGen Monomorphization next.
Print _initialize.
Print _generate.
Print _next.

CodeGen GenCFile "mt_generated.c" _generate _initialize.
