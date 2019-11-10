From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

From codegen Require Import codegen.
Require Import mt.

Definition mersenne_index : nat := 19937.
Local Notation p := mersenne_index.
Open Scope ring_scope.

Section char2.
Variable p : nat.
Variable t : (0 < p)%N.
Lemma pdiv_gt2 : (2 <= pdiv (2 ^ p))%N.
Proof. by rewrite /pdiv primes_exp. Qed.

Lemma pred_pdiv_gt0 : (0 < (pdiv (2 ^ p)).-1)%N.
Proof. move: pdiv_gt2; by case: (pdiv _). Qed.

Local Definition map : 'F_2 -> 'F_(2 ^ p).
  move=> [] m H.
  apply/(@Ordinal _ m)/(leq_trans H).
  by rewrite ltnS /Zp_trunc /= prednK pred_pdiv_gt0.
Defined.

Local Definition rmorph : rmorphism map.
 apply GRing.RMorphism.Class.
  case => [][? [][?|[]// ?]|[]// ? [][?|[]// ?]];
   by apply: val_inj; rewrite /= /pdiv primes_exp.
 constructor.
  case => [][? [][?|[]// ?]|[]// ? [][?|[]// ?]];
   by apply: val_inj; rewrite /= /pdiv primes_exp.
 by apply: val_inj; rewrite /= /pdiv primes_exp.
Defined.

Lemma char2 : 2 \in [char 'F_(2 ^ p)].
Proof. by apply (GRing.rmorph_char (RMorphism rmorph)). Qed.

Definition F := Frobenius_aut char2.
End char2.

From infotheo Require Import f2 ssralg_ext.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N_scope.

Definition mt19937_cycle : nat := 2 ^ 19937 - 1.

Require mt_alg.

Fail Lemma mt_alg_eq_mt : forall seed n,
    mt_alg.nth_random_value seed n = nth_random_value seed n.

Definition cyclic (f : nat -> N) cycle := forall n, f n = f (n + cycle)%nat.

Fail Lemma Mersenne_Twister_Cycle_alg n seed :
  cyclic (mt_alg.nth_random_value seed).

Section mt19937_cyclic.
Variable seed : N.

Lemma Mersenne_Twister_Cycle :
  cyclic (nth_random_value seed) mt19937_cycle.
Abort.

Lemma least_cycle cycle :
  (cycle < mt19937_cycle)%nat -> ~ cyclic (nth_random_value seed) cycle.

End mt19937_cyclic.
