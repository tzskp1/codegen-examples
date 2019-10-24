(* intermediate implementation between mt and mt_alg *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require Import BinNat.
From infotheo Require Import f2 ssralg_ext ssr_ext natbin.
From mathcomp Require Import boolp. (* classical, choice, and funext *)
Require mt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section word_of_N.
Variable nbits : nat.
Local Notation word := 'rV['F_2]_nbits.

(*
Definition word_of_N : N -> word :=
  poly_rV \o Poly \o (map F2_of_bool) \o bitseq_of_N.
Definition N_of_word : word -> N :=
  N_of_bitseq \o (map bool_of_F2) \o rVpoly.
*)

Definition word_of_N : N -> word := (rV_of_nat nbits) \o nat_of_bin.
Definition N_of_word : word -> N := bin_of_nat \o (@nat_of_rV nbits).

Lemma N_of_wordK : cancel N_of_word word_of_N.
Proof.
by move=> ?; rewrite /N_of_word /word_of_N /= bin_of_natK nat_of_rVK.
Qed.


Lemma rV_of_natK (n : N) :
  n < 2 ^ nbits -> nat_of_rV (rV_of_nat nbits n) = n.
Proof.
move=> ?.
apply (rV_of_nat_inj (nat_of_rV_up _))=> //.
by rewrite nat_of_rVK.
Qed.

Lemma word_of_NK (n : N) :
  n < 2 ^ nbits -> N_of_word (word_of_N n) = n.
Proof.
move=> ?.
rewrite /N_of_word /word_of_N /=.
Set Printing Coercions.
apply (can_inj nat_of_binK).
rewrite bin_of_natK.
by rewrite rV_of_natK.
Qed.
End word_of_N.

Local Notation word := 'rV['F_2]_32.
Local Notation op := 'M['F_2]_(32, 32).

Section shift.
Local Open Scope ring_scope.

Definition M_shiftl : op := 
  \matrix_(i < 32, j < 32) (i == j + 1 : 'F_2).
Definition M_shiftr : op :=
  \matrix_(i < 32, j < 32) (i + 1 == j : 'F_2).

Definition shiftl_with_1 (u : word) : word := 
  \row_(j < 32) (bool_of_F2 ((u *m M_shiftl) 0 j) || (j == 31 :> nat) : 'F_2).
Definition shiftr_with_1 (u : word) : word :=
  \row_(j < 32) (bool_of_F2 ((u *m M_shiftr) 0 j) || (j == 0) : 'F_2).
End shift.

Section matrix_ext.
Import GRing.Theory.
Local Open Scope ring_scope.
Lemma diag_mxK (R : ringType) (n : nat) (d : 'rV_n) :
  const_mx (1 : R) *m diag_mx d = d.
Proof.
rewrite mul_mx_diag.
apply/rowP=> i /=.
by rewrite mxE (_ : fun_of_matrix (const_mx 1) 0 i = 1) ?mul1r // mxE.
Qed.
End matrix_ext.

Section land.
Import GRing.Theory.
Local Open Scope ring_scope.
Definition M_land (u : word) : op := diag_mx u.
Definition land (u v : word) : word := u *m M_land v.
(*Definition land := [ffun u : word => [ffun v : word => u *m M_land v]].*)

Lemma landE (u v : word) : land u v = u *m M_land v.
Proof. by []. Qed.
Lemma landC : commutative land.
Proof.
move=> x y.
by rewrite !landE -[in LHS](diag_mxK x) -mulmxA diag_mxC mulmxA diag_mxK.
Qed.
Lemma landA : associative land.
Proof.
move=> x y z.
rewrite /land /M_land.
rewrite -[in LHS](diag_mxK y) -mulmxA mulmx_diag diag_mxK.
by rewrite -(diag_mxK x) -mulmx_diag mulmxA.
Qed.
Lemma land_is_bilinear :
  (forall x, linear (land x)) /\ (forall y, linear (land^~ y)).
suff H : forall x, linear (land^~ x)
  by split=> // x; rewrite (_ : land x = land^~ x) // funeqE=> y; rewrite landC.
move=> x; rewrite /land (_ : mulmx^~ (M_land x) = mulmxr (M_land x)) //.
exact: mulmxr_is_linear.
Qed.
End land.

Definition n : nat := 624. (* 'n' in tgfsr3.pdf, p.4 is 623*)
Definition m : nat := 397. (* 'm' in  tgfsr3.pdf, p.4 *)

