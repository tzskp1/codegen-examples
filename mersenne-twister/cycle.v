From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require Import irreducible mt.
(* Definition mersenne_exponent := 19937. *)
Section phi.
Variables n m w r : nat.
Variables a : w.-tuple [finFieldType of 'F_2].
Local Open Scope ring_scope.
Definition phi :=
  \poly_(i < r.+1) (a`_i *: (('X ^+ n + 'X ^+ m) ^+ (w - r))
  * (('X ^+ (n - 1) + 'X ^+ (m - 1)) ^+ (r - i)))
  + \poly_(i < w - r.-1)
     (a`_(r.-1 + i) *: (('X ^+ n + 'X ^+ m) ^+ (w - r - i))).
End phi.
Check irreducibleP _.

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
