From mathcomp Require Import all_ssreflect all_algebra.
Require Import codegen.codegen primitivity nat_word BinNat.
Require mt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section gluing.
Local Open Scope N_scope.

Notation len := 624. (* 'n' in tgfsr3.pdf, p.4 is 623*)
Notation m := 397. (* 'm' in  tgfsr3.pdf, p.4 *)
Notation w := 32.
Notation r := 31.
Notation u := 11.
Notation s := 7.
Notation t := 15.
Notation l := 18.
Notation a := 2567483615.
Notation b := 2636928640.
Notation c := 4022730752.

Definition upper_mask := Eval compute in @mt.upper_mask r w erefl.
Definition lower_mask := Eval compute in @mt.lower_mask r w erefl.
Definition whole_mask :=
Eval compute in N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))).
Definition set_nth d xs n := Eval compute in @set_nth N d xs n.
Definition nth d xs n := Eval compute in @nth N d xs n.
Definition next_random_state (rand : mt.random_state) :=
let state_vec := mt.state_vector rand in
let ind := mt.index rand in
let current := nth 0 state_vec ind in
let next_ind := N.succ ind mod len in
let next := nth 0 state_vec next_ind in
let far_ind := (ind + m) mod len in
let far := nth 0 state_vec (len - far_ind) in
let z := N.lor (N.land current upper_mask) (N.land next lower_mask) in
let xi := N.lxor (N.lxor far (N.shiftr z 1)) (if N.testbit z 0 then a else 0) in
let next_rand :=
  {| mt.index := next_ind; mt.state_vector := set_nth 0 state_vec ind xi |} in
(xi, next_rand).

Lemma next_random_stateE2 :
  next_random_state =1 @mt.next_random_state len m r a w erefl.
Proof. by []. Qed.

Definition tempering xi :=
  let y1 := N.lxor xi (N.shiftr xi u) in
  let y2 := N.lxor y1 (N.land (N.shiftl y1 s) b) in
  let y3 := N.lxor y2 (N.land (N.shiftl y2 t) c) in
  let y4 := N.lxor y3 (N.shiftr y3 l) in
  y4.
Lemma temperingE : tempering =1 mt.tempering u s t l b c.
Proof. by []. Qed.

Fixpoint generate_state_vector (rest : nat) (acc : seq N) : seq N :=
  match rest with
  | 0%nat | 1%nat => acc
  | S rest' =>
    generate_state_vector rest'
    ((N.land (1812433253 * (N.lxor (head 0 acc) (N.shiftr (head 0 acc) 30)) + N.of_nat(len - rest) + 1) whole_mask) :: acc)
  end.

Definition initialize_random_state (seed : N) : mt.random_state :=
{|
  mt.index := 0;
  mt.state_vector :=
    rev (generate_state_vector len (N.land seed whole_mask :: nil));
|}.

Fixpoint nth_random_value_with_random_state (nth : nat) (rand : mt.random_state) : N :=
  let (r, next_rand) := next_random_state rand in
  match nth with
  | 0%nat => tempering r
  | S nth' => nth_random_value_with_random_state nth' next_rand
  end.

Definition nth_random_value (seed : N) (nth : nat) :=
  let rand := initialize_random_state seed in
  nth_random_value_with_random_state nth rand.

End gluing.

CodeGen Snippet "#include <stdbool.h> /* for bool, true and false */".

CodeGen Inductive Type bool => "bool".
CodeGen Inductive Match bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

CodeGen Snippet "#include <stdint.h>".
CodeGen Snippet "typedef uint64_t nat;".
CodeGen Snippet "typedef uint32_t positive;".
CodeGen Snippet "typedef uint32_t N;".
CodeGen Snippet "#define succn(n) ((n)+1)".
CodeGen Snippet "#define predn(n) ((n)-1)".
CodeGen Snippet "#define xH() (1)".
CodeGen Snippet "#define xO(n) (2*(n))".
CodeGen Snippet "#define xI(n) (2*(n)+1)".
CodeGen Snippet "#define modulo(n, m) ((n) % (m))".
CodeGen Snippet "#define nat_of_bin(n) ((nat)(n))".
CodeGen Snippet "#define N0() (0)".
CodeGen Snippet "#define Npos(n) ((nat)(n))".

CodeGen Inductive Type nat => "nat".
CodeGen Inductive Match nat => ""
| O => "case 0"
| S => "default" "predn".
CodeGen Primitive S => "succn".
(* CodeGen Primitive addn => "addn". *)
(* CodeGen Primitive subn => "subn". *)
(* CodeGen Primitive muln => "muln". *)
(* CodeGen Primitive divn => "divn". *)
(* CodeGen Primitive modn => "modn". *)
(* CodeGen Primitive eqb => "eqb". *)
(* CodeGen Primitive negb => "negb". *)
(* CodeGen Primitive eqn => "eqn". *)

CodeGen Function lower_mask.
CodeGen Function upper_mask.
CodeGen Function set_nth.
CodeGen Function nth.
CodeGen Function next_random_state.

CodeGen GenerateFile "./mt19937_proved.c".
