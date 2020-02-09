From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require irreducible BinNat.
Require Import polyn.

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

Axiom pm' : prime (2 ^ 19937 - 1).

Lemma poly_exp_leq (t : poly_ringType [finFieldType of 'F_2]) p :
  1 < size t -> size (t ^+ p)%R < size (t ^+ p.+1)%R.
Proof.
  move=> Ht. elim: p => [|p IHp].
   by rewrite GRing.expr0 size_polyC GRing.oner_neq0 GRing.expr1.
  case s00: (size (t ^+ p.+1)%R == 0).
   by move/eqP: s00 IHp => ->.
  case s0: (size (t ^+ p.+2)%R == 0).
   rewrite size_poly_eq0 GRing.exprS GRing.mulf_eq0 -!size_poly_eq0 in s0.
   case/orP: s0 => s0.
    by move/eqP: s0 Ht => ->.
   by move/eqP: s0 IHp => ->.
  rewrite -(@prednK (size (t ^+ p.+1)%R)) ?(lt0n, s00) //
          -(@prednK (size (t ^+ p.+2)%R)) ?(lt0n, s0) //
          !size_exp ltnS ltn_mul2l ltnSn.
  case: (size t) Ht => // n.
  by rewrite ltnS => ->.
Qed.

Lemma poly_exp_leq' (t : poly_ringType [finFieldType of 'F_2]) p q :
  p < q -> 1 < size t -> size (t ^+ p)%R < size (t ^+ q)%R.
Proof.
  elim: q => // q IHq pq t1.
  case pq0: (p == q).
   by move/eqP: pq0 => ->; apply/poly_exp_leq.
  apply/ltn_trans/poly_exp_leq/t1/IHq => //.
  by rewrite ltnNge leq_eqVlt eq_sym pq0 negb_or /= -ltnNge.
Qed.

Lemma size_phi : (size phi).-1 = 19937.
Proof.
  rewrite /phi /phi' /=.
  have ->: (32 - 31 = 1)%N by []. have ->: (32 - 30 = 2)%N by [].
  rewrite !GRing.expr1. set T := (\sum_(i < 2) _ *: _ ^+ _)%R.
  have ->: T = ('X^624 + 'X^397 + 1)%R.
   by rewrite /T big_ord_recr big_ord1 /= !GRing.scale1r
              subnn subn0 GRing.expr0 GRing.expr1.
  have H : (('X^623 + 'X^396 : poly_ringType [finFieldType of 'F_2])%R != 0%R).
   by rewrite -size_poly_eq0 size_addl ?size_polyXn.
  have x : (('X^624 + 'X^397 : poly_ringType [finFieldType of 'F_2])%R != 0%R).
   by rewrite -size_poly_eq0 size_addl ?size_polyXn.
  have H1: forall n, (('X^623 + 'X^396 : poly_ringType [finFieldType of 'F_2]) ^+ n)%R != 0%R.
   elim => [|n IHn].
    by rewrite GRing.expr0 GRing.oner_neq0.
   by rewrite GRing.exprS GRing.mulf_eq0 negb_or H /=.
  rewrite !size_addl ?size_polyXn ?size_polyC //.
  rewrite size_mul // size_addl ?size_polyXn //.
  set T' := (_ + _)%R.
  rewrite -(@prednK (size (T' ^+ 31)%R)); last by rewrite lt0n size_poly_eq0 /T' H1.
  rewrite /T' size_exp size_addl ?size_polyXn; last by [].
  by native_compute.
  repeat (
  repeat rewrite big_ord_recl /= GRing.scale0r GRing.mul0r GRing.add0r;
  repeat (rewrite big_ord_recl size_addl GRing.scale1r;
    first by rewrite size_mul // [X in _ < X]size_mul // -subn1 -[X in _ < X]subn1
             ltn_sub2r // ?(ltn_add2l, poly_exp_leq') // ?ltn_addr ?size_addl ?size_polyXn)).
  by rewrite big_ord0 size_polyC eqxx lt0n size_poly_eq0 GRing.mulf_eq0 negb_or H1 x.
  rewrite size_mul // size_addl ?size_polyXn //.
  set T' := (_ + _)%R.
  rewrite -(@prednK (size (T' ^+ 31)%R)); last by rewrite lt0n size_poly_eq0 /T' H1.
  by rewrite /T' size_exp size_addl ?size_polyXn.
  repeat (
  repeat rewrite big_ord_recl /= GRing.scale0r GRing.mul0r GRing.add0r;
  repeat (rewrite big_ord_recl size_addl GRing.scale1r;
    first by rewrite size_mul // [X in _ < X]size_mul // -subn1 -[X in _ < X]subn1
             ltn_sub2r // ?(ltn_add2l, poly_exp_leq') // ?ltn_addr ?size_addl ?size_polyXn)).
  by rewrite big_ord0 size_polyC eqxx lt0n size_poly_eq0 GRing.mulf_eq0 negb_or H1 x.
Qed.

Lemma pm : prime (2 ^ (size phi).-1 - 1).
Proof. by rewrite size_phi pm'. Qed.

Check @irreducible.mulX _ pm.
Require Import BinNat mt.
Definition init := initialize_random_state 20190820%N.
Definition zero := next_random_state init.
Definition one := next_random_state zero.2.
Compute length (state_vector one.2).
Check eigenvalue _ _.
Compute one.
Compute zero.
(* 0:324445478 *)
(* 1:774197212 *)


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
