From mathcomp Require Import all_ssreflect.

From seplog Require Import machine_int.

Require Import codegen.codegen.

Set Implicit Arguments.
Unset Strict Implicit.

Import MachineInt.

Open Scope machine_int_scope.

Definition int32 := int 32.

Definition z2u32 z := `( z )_ 32. (* `( z )c_ 32 の方がいいだろうか？ *)
Definition nat2u32 n := z2u32 (Z.of_nat n).

Definition int32_and (a : int32) (b : int32) : int32 := int_and a b.
Definition int32_or (a : int32) (b : int32) : int32 := int_or a b.
Definition int32_xor (a : int32) (b : int32) : int32 := int_xor a b.
Definition int32_shrl (a : int32) (i : nat) : int32 := a `>> i.
Definition int32_shl (a : int32) (i : nat) : int32 := a `<< i.
Definition int32_add (a : int32) (b : int32) : int32 := add a b.
Definition int32_mul (a : int32) (b : int32) : int32 := mul a b.

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

Definition generate_constant : int32 := z2u32 1812433253.

Fixpoint generate_state_vector (acc : seq int32) (rest : nat) : seq int32 :=
  match rest with
  | 0%nat => acc
  | S m =>
    let i := minus len rest in (* 次の生成ははi番目 *)
    let head_element := (head zero acc) in (* 先頭はi-1番目に生成された元 *)
    let tmp1 := int32_xor head_element (int32_shrl head_element 30) in
    let tmp2 := mul generate_constant tmp1 in
    let tmp3 := int32_add (int32_add tmp2 (nat2u32 i)) one in 
    let new_element := int32_and tmp3 whole_mask in
    generate_state_vector (new_element :: acc) m 
  end.

Definition initialize_state_vector (seed : int32)  : seq int32 :=
  rev (generate_state_vector (int32_and seed  whole_mask :: nil)  (minus len 1%nat)).

Definition initialize_random_state (seed : int32) : random_state :=
  {|
    index := 0;
    state_vector := initialize_state_vector seed;
  |}.

Definition nth_word state_vector index := nth zero state_vector index.
Definition set_nth_word state_vector index word := set_nth zero state_vector index word.

Definition tempering (x : int32) : int32 :=
  let y1 := int32_xor x (int32_shrl x u) in
  let y2 := int32_xor y1 (int32_and (int32_shl y1 s) b) in
  let y3 := int32_xor y2 (int32_and (int32_shl y2 t) c) in
  let y4 := int32_xor y3 (int32_shrl y3 l) in
  y4.

Definition next_random_state (rand : random_state) : (int32 * random_state) :=
  let state_vec := state_vector rand in
  let ind := index rand in
  let current := nth_word state_vec ind in
  let next_ind := Nat.modulo (ind + 1%nat) len in
  let next := nth_word state_vec next_ind in
  let far_ind := Nat.modulo (ind + m) len in
  let far := nth_word state_vec far_ind in
  let z := int32_or (int32_and current upper_mask) (int32_and next lower_mask) in
  let xi := int32_xor far
                      (int32_xor (int32_shrl z 1)
                                 (if (int32_and z one) == zero then zero else a)) in
  let next_rand := {|
        index := next_ind;
        state_vector := set_nth_word state_vec ind xi;
      |} in
  (xi, next_rand).


Definition mersenne_twister (rand : random_state) : (int32 * random_state) :=
  let (x, next_state) := next_random_state rand in
  (tempering x, next_state).

Fixpoint nth_rand (n : nat) (rand : random_state) : int32 :=
  let (r, next_state) := mersenne_twister rand in
  match n with
  | 0%nat => r
  | S m => nth_rand m next_state
  end.

Definition nth_rand_with_seed (n : nat) (seed : int32) : int32 :=
  let rand := initialize_random_state seed in
  nth_rand n rand.

Definition seed := z2u32 20150919.

(* Eval vm_compute in initialize_random_state seed. *)

(* Compute nth_rand_with_seed 0 seed. *)
(* Compute nth_rand_with_seed 1 seed. *)
(* Compute nth_rand_with_seed 2 seed. *)

CodeGen Monomorphization int32.
CodeGen Terminate Monomorphization z2u32.
CodeGen Terminate Monomorphization nat2u32.
CodeGen Terminate Monomorphization int32_and.
CodeGen Terminate Monomorphization int32_or.
CodeGen Terminate Monomorphization int32_xor.
CodeGen Terminate Monomorphization int32_shrl.
CodeGen Terminate Monomorphization int32_shl.
CodeGen Terminate Monomorphization int32_add.
CodeGen Terminate Monomorphization int32_mul.
CodeGen Terminate Monomorphization generate_constant.
CodeGen Monomorphization initialize_state_vector.
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
        
