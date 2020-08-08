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
Hypothesis len1 : 1 < len.
Lemma len0 : len <> 0.
Proof. by case: len len1. Qed.
Hypothesis m0 : m mod len <> 0.

Hint Resolve len0 : core.

Definition upper_mask := (N_of_word (make_upper_mask rw)).
Definition lower_mask := (N_of_word (make_lower_mask rw)).

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
  let far := nth 0 state_vec far_ind in
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

Definition fil0 (y : random_state) :=
  let z := N.land (nth 0%N (state_vector y) (index y)) upper_mask in
  {|
    index := index y;
    state_vector := set_nth 0%N (state_vector y) (index y) z;
  |}.

Lemma random_state_eqP :
  Equality.axiom
  (fun a b => (state_vector a == state_vector b) && (index a == index b)).
Proof.
  case=> [] cx x [] cy y.
  apply/(iffP idP) => [/andP [] /= /eqP -> /eqP -> //|-> /=].
  by rewrite !eqxx.
Qed.

Canonical random_state_eqMixin := EqMixin random_state_eqP.
Canonical random_state_eqType :=
   Eval hnf in EqType random_state random_state_eqMixin.

Lemma next_random_state_fil0 x : next_random_state x = next_random_state (fil0 x).
Proof.
  case: x => // i x.
  rewrite /fil0 /= /next_random_state !nth_set_nth /= set_set_nth eqxx.
  set T := _ == _.
  have->: T = false.
   subst T.
   apply/negP => /eqP /(f_equal bin_of_nat).
   rewrite !nat_of_binK => /(f_equal (fun x => x mod len)%N).
   rewrite N.mod_mod // N.add_mod // -[(i mod len)]N.mod_mod //.
   set I := i mod len.
   move/(f_equal (fun x => (x mod len + (len - I) mod len mod len) mod len)%N).
   rewrite N.mod_mod // -!N.add_mod // N.add_sub_assoc; last
    by apply/N.lt_le_incl/N.mod_lt.
   rewrite [in RHS]N.add_comm N.add_sub N.mod_same //.
   rewrite N.add_comm N.add_assoc.
   rewrite N.add_mod // -[((len - I) mod len + I mod len) mod len]N.add_mod //.
   rewrite N.sub_add; last by apply/N.lt_le_incl/N.mod_lt.
   by rewrite N.mod_same // N.add_0_l !N.mod_mod.
  subst T; set T := _ == _.
  have ->: T = false.
   subst T.
   apply/negP => /eqP /(f_equal bin_of_nat).
   rewrite !nat_of_binK => /(f_equal (fun x => x mod len)%N).
   rewrite -N.add_1_r N.mod_mod // N.add_mod // -[(i mod len)]N.mod_mod //.
   set I := i mod len.
   move/(f_equal (fun x => (x mod len + (len - I) mod len mod len) mod len)%N).
   rewrite N.mod_mod // -!N.add_mod // N.add_sub_assoc; last
    by apply/N.lt_le_incl/N.mod_lt.
   rewrite [in RHS]N.add_comm N.add_sub N.mod_same //.
   rewrite N.add_comm N.add_assoc.
   rewrite N.add_mod // -[((len - I) mod len + I mod len) mod len]N.add_mod //.
   rewrite N.sub_add; last by apply/N.lt_le_incl/N.mod_lt.
   rewrite N.mod_same // N.add_0_l !N.mod_mod //.
   
   
   Search (1 mod _).
  
  rewrite set_nth
  congr (_, _).
  rewrite /=.

End Implementation.
