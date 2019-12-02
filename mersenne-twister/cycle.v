From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require Import polyn mt.
Require irreducible BinNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section phi.
Variables w n m r : nat.
Variable a : w.-tuple [finFieldType of 'F_2].

Local Open Scope ring_scope.
Definition phi' :=
  ('X ^+ n + 'X ^+ m) ^+ (w - r) * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ r
  + \sum_(i < r.-1) a`_i *: ('X ^+ n + 'X ^+ m) ^+ (w - r)
                     * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ (r.-1 - i)
  + \sum_(i < w - r.-1)
     a`_(r.-1 + i) *: ('X ^+ n + 'X ^+ m) ^+ (w - r - i).
End phi.

Lemma a32 : size ([:: 1; 0; 0; 1; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 1; 0; 1;
                     1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 1]: seq 'F_2)%R == 32.
Proof. by []. Qed.
Definition phi := phi' 624 397 31 (Tuple a32).

From infotheo Require Import f2 ssralg_ext.
Require Import BinNat.

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
Abort.

End mt19937_cyclic.
