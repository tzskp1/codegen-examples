(* intermediate implementation between mt and mt_alg *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require Import BinNat.
From infotheo Require Import f2 ssralg_ext natbin.
Require mt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition len : nat := 624. (* 'n' in tgfsr3.pdf, p.4 is 623*)
Definition m : nat := 397. (* 'm' in  tgfsr3.pdf, p.4 *)

Local Notation word := 'rV['F_2]_32.
Local Notation op := 'M['F_2]_(32, 32).

Section shift.
Local Open Scope ring_scope.

Definition M_shiftl : op := 
  \matrix_(i < 32, j < 32) (i == j + 1 : 'F_2).
Definition M_shiftr : op :=
  \matrix_(i < 32, j < 32) (i + 1 == j : 'F_2).

Definition shiftl_with_1 (w : word) : word := 
  \row_(j < 32) (bool_of_F2 ((w *m M_shiftl) 0 j) || (j == inord 31) : 'F_2).
Definition shiftr_with_1 (w : word) : word :=
  \row_(j < 32) (bool_of_F2 ((w *m M_shiftr) 0 j) || (j == 0) : 'F_2).

End shift.

Section word_of_N.
(*
Definition word_of_N : N -> word :=
  poly_rV \o Poly \o (map F2_of_bool) \o bitseq_of_N.
Definition N_of_word : word -> N :=
  N_of_bitseq \o (map bool_of_F2) \o rVpoly.
*)
Definition word_of_N : N -> word := (rV_of_nat 32) \o nat_of_N.
Definition N_of_word : word -> N := N_of_nat \o (@nat_of_rV 32).

Lemma N_of_wordK : cancel N_of_word word_of_N.
Proof.
by move=> w; rewrite /N_of_word /word_of_N /= Nnat.Nat2N.id nat_of_rVK.
Qed.
Lemma word_of_NK (n : N) : (N.size_nat n <= 32)%nat -> N_of_word (word_of_N n) = n.
Admitted.
End word_of_N.
