(* Implementation of MT19937 *)
From mathcomp Require Import all_ssreflect.

Require Import BinNat nat_word.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N_scope.

Section Implementation.
Variables len m r a w : N.
Variables u s t l b c : N.
Hypothesis rw : (r <= w)%nat.

Notation upper_mask := (N_of_word (make_upper_mask rw)).
Notation lower_mask := (N_of_word (make_lower_mask rw)).

Record random_state := {index : N; state_vector : seq N}.

Definition tempering xi :=
  (* (2.2) to (2.5) in p.6 *)
  let y1 := N.lxor xi (N.shiftr xi u) in
  let y2 := N.lxor y1 (N.land (N.shiftl y1 s) b) in
  let y3 := N.lxor y2 (N.land (N.shiftl y2 t) c) in
  let y4 := N.lxor y3 (N.shiftr y3 l) in
  y4.

Definition next_random_state (rand : random_state) : (N * random_state) :=
  let state_vec := state_vector rand in
  let ind := index rand in
  let current := nth 0 state_vec ind in
  let next_ind := N.modulo (N.succ ind) len in
  let next := nth 0 state_vec next_ind in
  let far_ind := N.modulo (ind + m) len in
  (* x_{k+m} in (2.1), p.5 *)
  let far := nth 0 state_vec (len - far_ind) in
  (* (x^u_k | x^l_{k+1}) in (2.1), p.5 *)
  let z := N.lor (N.land current upper_mask)
                 (N.land next lower_mask) in
  (* (2.1) in p.5 combined with the equation for xA in p.6*)
  let xi := N.lxor (N.lxor far (N.shiftr z 1))
                   (if N.testbit z 0 then a else 0) in
  let next_rand := {|
        index := next_ind;
        state_vector := set_nth 0 state_vec ind xi;
      |} in
  (xi, next_rand).
End Implementation.
