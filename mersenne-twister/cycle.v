From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From infotheo Require Import f2 ssralg_ext.
Require Import BinNat.
From codegen Require Import codegen.
Require Import mt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope N_scope.

Definition cycle : nat := 2 ^ 19937 - 1.

Lemma Mersenne_Twister_Cycle : forall seed n, nth_random_value n seed = nth_random_value (n + cycle) seed.
