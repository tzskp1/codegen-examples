From mathcomp Require Import all_ssreflect.

From seplog Require Import machine_int.

(* Require Import BinNat.*)

Require Import codegen.codegen.

Set Implicit Arguments.
Unset Strict Implicit.

Import MachineInt.

Open Scope machine_int_scope.

Definition int32 := int 32.

Definition z2u32 z := `( z )_ 32.
Definition nat2u32 n := z2u32 (Z.of_nat n).

Definition len : nat := 624.
Definition m : nat := 397.
Definition r : nat := 31.
Definition u : nat:= 11.
Definition s : nat  := 7.
Definition t : nat := 15.
Definition l : nat := 18.
Definition a : int32 := z2u32 2567483615.
Definition b : int32 := z2u32 2636928640.
Definition c : int32 := z2u32 4022730752.

Definition upper_mask_z := 2147483648.
Definition upper_mask : int32 := z2u32 upper_mask_z.
Definition whole_mask : int32 := z2u32 (upper_mask_z * 2 - 1).
Definition lower_mask : int32 := z2u32 (upper_mask_z - 1).

Record random_state := {index : nat; state_vector : seq int32}.

Definition zero : int32 := z2u32 0.
Definition one : int32 := z2u32 1.

Fixpoint generate_state_vector (acc : seq int32) (rest : nat) : seq int32 :=
  match rest with
  | 0%nat => acc
  | S m =>
    let i := minus len rest in (* 次の生成ははi番目 *)
    let head_element := (head zero acc) in (* 先頭はi-1番目に生成された元 *)
    let tmp1 := head_element `(+) (head_element `>> 30) in
    let tmp2 := mul (z2u32 1812433253) tmp1 in
    let tmp3 := tmp2 `+ nat2u32 i `+ one in 
    let new_element := tmp3 `& whole_mask in
    generate_state_vector (new_element :: acc) m 
  end.

Definition initialize_state_vector (seed : int32)  : seq int32 :=
  rev (generate_state_vector (seed `& whole_mask :: nil)  (minus len 1%nat)).

Definition initialize_random_state (seed : int32) : random_state :=
  {|
    index := 0;
    state_vector := initialize_state_vector seed;
  |}.

Definition nth_word state_vector index := nth zero state_vector index.
Definition set_nth_word state_vector index word := set_nth zero state_vector index word.


Definition next_random_state (rand : random_state) : (int32 * random_state) :=
  let state_vec := state_vector rand in
  let ind := index rand in
  let current := nth_word state_vec ind in
  let next_ind := Nat.modulo (ind + 1%nat) len in
  let next := nth_word state_vec next_ind in
  let far_ind := Nat.modulo (ind + m) len in
  let far := nth_word state_vec far_ind in
  let z := (current `& upper_mask) `|` (next `& lower_mask) in
  let xi := far `(+) (z `>> 1) `(+) (if (z `& one) == zero then zero else a) in
  let y1 := xi `(+) (xi `>> u) in
  let y2 := y1 `(+) ((y1 `<< s) `& b) in
  let y3 := y2 `(+) ((y2 `<< t) `& c) in
  let y4 := y3 `(+) (y3 `>> l) in
  let next_rand := {|
        index := next_ind;
        state_vector := set_nth_word state_vec ind xi;
      |} in
  (y4, next_rand).

Fixpoint nth_rand (n : nat) (rand : random_state) : int32 :=
  let (r, next_state) := next_random_state rand in
  match n with
  | 0%nat => r
  | S m => nth_rand m next_state
  end.

Definition nth_rand_with_seed (n : nat) (seed : int32) : int32 :=
  let rand := initialize_random_state seed in
  nth_rand n rand.

Definition seed := z2u32 20150919.

Compute initialize_random_state seed.

Compute nth_rand_with_seed 0 seed.
Compute nth_rand_with_seed 1 seed.
Compute nth_rand_with_seed 2 seed.

CodeGen Terminate Monomorphization N.land.
CodeGen Terminate Monomorphization N.lor.
CodeGen Terminate Monomorphization N.lxor.
CodeGen Terminate Monomorphization N.shiftl.
CodeGen Terminate Monomorphization N.shiftr.
CodeGen Monomorphization initialize_random_state.
CodeGen Monomorphization next_random_state.
CodeGen Monomorphization nth_rand.
CodeGen Monomorphization nth_rand_with_seed.
Print _initialize_random_state.
Print _generate_state_vector.
Print _next_random_state.
Print _nth_rand.
Print _nth_rand_with_seed.

CodeGen GenCFile "mt_generated.c"
        _generate_state_vector
        _initialize_random_state
        _next_random_state
        _nth_rand
        _nth_rand_with_seed.
        
