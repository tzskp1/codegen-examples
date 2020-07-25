From mathcomp Require Import all_ssreflect all_algebra.
Require Import codegen.codegen primitivity nat_word BinNat.
Require mt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N_scope.

Definition len := 624. (* 'n' in tgfsr3.pdf, p.4 is 623*)
Definition m := 397. (* 'm' in  tgfsr3.pdf, p.4 *)
Definition w := 32.
Definition r := 31.
Definition u := 11.
Definition s := 7.
Definition t := 15.
Definition l := 18.
Definition a := 2567483615.
Definition b := 2636928640.
Definition c := 4022730752.

Definition upper_mask := Eval compute in @mt.upper_mask r w erefl.
Definition lower_mask := Eval compute in @mt.lower_mask r w erefl.
Definition next_random_state (rand : mt.random_state) :=
let state_vec := mt.state_vector rand in
let ind := mt.index rand in
let current := nth 0 state_vec ind in
let next_ind := N.succ ind mod len in
let next := nth 0 state_vec next_ind in
let far_ind := (ind + m) mod len in
let far := nth 0 state_vec (len - far_ind) in
let z :=
  N.lor (N.land current upper_mask) (N.land next lower_mask) in
let xi := N.lxor (N.lxor far (N.shiftr z 1)) (if N.testbit z 0 then a else 0)
  in
let next_rand :=
  {| mt.index := next_ind; mt.state_vector := set_nth 0 state_vec ind xi |} in
(xi, next_rand).

Local Notation tempering := (tempering u s t l b c).
Definition whole_mask :=
  Eval compute in N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))).

Fixpoint generate_state_vector (rest : nat) (acc : seq N) : seq N :=
  match rest with
  | 0%nat | 1%nat => acc
  | S rest' =>
    generate_state_vector rest'
    ((N.land (1812433253 * (N.lxor (head 0 acc) (N.shiftr (head 0 acc) 30)) + N.of_nat(len - rest) + 1) whole_mask) :: acc)
  end.

Definition initialize_random_state (seed : N) : random_state :=
{|
  index := 0;
  state_vector := rev (generate_state_vector len (N.land seed whole_mask :: nil));
|}.

Fixpoint nth_random_value_with_random_state (nth : nat) (rand : random_state) : N :=
  let (r, next_rand) := nrs rand in
  match nth with
  | 0%nat => tempering r
  | S nth' => nth_random_value_with_random_state nth' next_rand
  end.

Definition nth_random_value (seed : N) (nth : nat) :=
  let rand := initialize_random_state seed in
  nth_random_value_with_random_state nth rand.

CodeGen Inductive Type bool => "bool".
CodeGen Inductive Match bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

CodeGen Snippet "
#include <stdbool.h> /* for bool, true and false */
".

CodeGen Function nat_of_bin.
CodeGen Function initialize_random_state.
Print nrs.
Eval unfold nrs, upper_mask in nrs.
Goal False.
  move: nrs.
CodeGen Gen nrs.
Print nrs.
CodeGen GenerateFile "./mt19937_proved.c".
