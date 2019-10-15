(* Algebraic Implementation of MT19937 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_field.
From infotheo Require Import f2 ssralg_ext.
Require BinNat.
Require mt.
Require Import mt_vec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Definition len : nat := 624. (* 'n' in tgfsr3.pdf, p.4 is 623*)
Definition m : nat := 397. (* 'm' in  tgfsr3.pdf, p.4 *)
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
*)

Local Notation word := 'rV['F_2]_32.
Local Notation op := 'M['F_2]_(32, 32).
Local Notation state := (seq word). (* x_n :: x_(n-1) :: x_(n-2) :: ... *)

Section tgfsr_next_state.
Local Open Scope ring_scope.
Variable A : op.

(* x_(l+n) = x_(l+m) + x_l *m A, n -> len *)
(* indexの対応: l+n -> 0, l+m -> len - m, l -> len *)
Definition tgfsr_next_word (rand : state) := 
  nth 0 rand (len - m) + (nth 0 rand len) *m A.

Definition tgfsr_next_state (rand : state) : state :=
  (tgfsr_next_word rand) :: rand.
End tgfsr_next_state.

Section mt_next_state.
Local Open Scope ring_scope.

Section parameter_A.
Import BinNat.
Local Open Scope N_scope.
Definition a := word_of_N 32 2567483615.
End parameter_A.

Section matrix.
Local Open Scope nat_scope.
Definition r : nat := 31.

Definition I_r : op :=
  \matrix_(i < 32, j < 32) ((i == j) && (i >= r) : 'F_2).

Definition I_wr : op :=
  \matrix_(i < 32, j < 32) ((i == j) && (i < r) : 'F_2).

(* A is the companion matrix of the bit sequence a
   (coerced to a polynomial) *)
Definition A : op :=
  \matrix_(i < 32, j < 32)
   ((i + 1 == j) || ((i == 31 :> nat) && (bool_of_F2 (a ord0 j))) : 'F_2).

Definition B : op := I_r *m A.
Definition C : op := I_wr *m A.

End matrix.

(* x_(n+p) =  x_(l+q) + x_(n+1) *m B + x_n *m C *)
Definition mt_next_word (rand : state) :=
  nth 0 rand (len - m) + (nth 0 rand (len - 1)) *m B + (nth 0 rand len) *m C.

Definition mt_next_state (rand : state) : state :=
  (mt_next_word rand) :: rand.
End mt_next_state.

Section characteristic.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Variable M : 'M['F_2]_(19937, 19937).

Definition phi_M := char_poly M.

Check phi_M.

Check prime_idealr .

Definition I := fun r : {poly 'F_2} => gcdp phi_M r == phi_M.

Lemma phi_M_primitive : prime_idealr I.
Admitted.

Let kI := keyed_pred phi_M_primitive.
Variable i : kI.
Check {ideal_quot i}.

(* phi_M is primitive
   <-> (phi_M) is prime
   <-> {poly 'F_2} / (phi_M) is a field
   <-> {1, t^2, t^3, t^4, .. , t^(2^p - 1)} is a cyclic group *)

End characteristic.

Import BinNat.

Variable seed : state.
Hypothesis Size_Seed : size seed > len.



Definition next_random_state (rand: state) : N * state.
Abort.

(*
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
*)
