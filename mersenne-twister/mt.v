(* Implementation of MT19937 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import BinNat.
From codegen Require Import codegen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N_scope.

Definition len : nat := 624.
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

Record random_state := {index : nat; state_vector : seq N}.

Fixpoint generate_state_vector (rest : nat) (acc : seq N) : seq N :=
  match rest with
  | 0%nat => acc
  | 1%nat => acc
  | S m => generate_state_vector m ((N.land (1812433253 * (N.lxor (head 0 acc) (N.shiftr (head 0 acc) 30)) + N.of_nat(len - rest) + 1) whole_mask) :: acc)
  end.

Definition initialize_random_state (seed : N) : random_state :=
  {|
    index := 0;
    state_vector := rev (generate_state_vector len  (N.land seed whole_mask :: nil));
  |}.

Definition next_random_state (rand : random_state) : (N * random_state) :=
  let state_vec := state_vector rand in
  let ind := index rand in
  let current := nth 0 state_vec ind in
  let next_ind := Nat.modulo (ind +  1%nat) len in
  let next := nth 0 state_vec next_ind in
  let far_ind := Nat.modulo (ind + m) len in
  let far := nth 0 state_vec far_ind in
  let z := N.lor (N.land current upper_mask)
                 (N.land next lower_mask) in
  let xi := N.lxor (N.lxor far
                           (N.shiftr z 1))
                   (if N.eqb (N.land z 1) 0 then 0 else a) in
  let y1 := N.lxor xi (N.shiftr xi u) in
  let y2 := N.lxor y1 (N.land (N.shiftl y1 s) b) in
  let y3 := N.lxor y2 (N.land (N.shiftl y2 t) c) in
  let y4 := N.lxor y3 (N.shiftr y3 l) in
  let next_rand := {|
        index := next_ind;
        state_vector := set_nth 0 state_vec ind xi;
      |} in
  (y4, next_rand).

Fixpoint nth_random_value_with_random_state (nth : nat) (rand : random_state) : N :=
  let (r, next_rand) := next_random_state rand in
  match nth with
  | 0%nat => r
  | S m => nth_random_value_with_random_state m next_rand
  end.

Definition nth_random_value (nth : nat) (seed : N) :=
  let rand := initialize_random_state seed in
  nth_random_value_with_random_state nth rand.

CodeGen Terminate Monomorphization N.land.
CodeGen Terminate Monomorphization N.lor.
CodeGen Terminate Monomorphization N.lxor.
CodeGen Terminate Monomorphization N.shiftl.
CodeGen Terminate Monomorphization N.shiftr.
CodeGen Monomorphization initialize_random_state.
CodeGen Monomorphization next_random_state.
Print _initialize_random_state.
Print _generate_state_vector.
Print _next_random_state.

CodeGen GenCFile "mt_generated.c"
        _generate_state_vector
        _initialize_random_state
        _next_random_state.
        
