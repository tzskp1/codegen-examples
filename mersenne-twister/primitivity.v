From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coqprime Require Import PocklingtonRefl.

Lemma ZposE p : Z.pos p = Z.of_nat (Pos.to_nat p).
Proof.
  elim: p => // p H.
  + by rewrite Pos2Nat.inj_xI Nat2Z.inj_succ Nat2Z.inj_mul /= -H.
  + by rewrite Pos2Nat.inj_xO Nat2Z.inj_mul /= -H.
Qed.

Lemma NposE p : N.pos p = Pos.to_nat p :> nat.
Proof.
  elim: p => // p H.
  + by rewrite Pos2Nat.inj_xI /= natTrecE Nat.add_0_r -addnn -plusE -!H.
  + by rewrite Pos2Nat.inj_xO /= natTrecE Nat.add_0_r -addnn -plusE -!H.
Qed.

Local Lemma trivial x0 : Z.of_nat x0.+1 = Z.of_nat x0 + 1.
Proof.
  rewrite /Z.of_nat.
  case: x0 => // x0.
  by rewrite /= Pos2Z.inj_add /= Pos.add_1_r.
Qed.

Lemma of_nat_hom' x0 x : Z.of_nat (x0 + x) = Z.of_nat x0 + Z.of_nat x.
Proof.
  elim: x0 x => // x0 IHx0 x.
  by rewrite trivial addSn -addnS IHx0 -[in RHS]Z.add_assoc [X in _ = _ + X]Z.add_comm -trivial.
Qed.

Lemma of_nat_hom x0 x : Z.of_nat (x0 * x) = Z.of_nat x0 * Z.of_nat x.
Proof.
  elim: x0 x => // x0 IHx0 x.
  by rewrite trivial Z.mul_add_distr_r -IHx0 mulSn addnC of_nat_hom' Z.mul_1_l.
Qed.

Lemma of_nat_inj x0 x : Z.of_nat x0 = Z.of_nat x -> x0 = x.
Proof.
  elim: x0 x => [[]//|] x0 IHx0 []// x.
  by rewrite !trivial !Z.add_1_r => /Z.succ_inj/IHx0 ->.
Qed.

Lemma dvdnP' x m : reflect (Z.of_nat x | Z.of_nat m) (dvdn x m).
Proof.
  apply/(iffP idP) => H.
  + case/dvdnP: H => x0 p.
    exists (Z.of_nat x0); by rewrite -of_nat_hom p.
  + case: H => x0 p.
    apply/dvdnP.
    case: x0 p.
    * rewrite Z.mul_0_l.
      case: m => // _.
      by exists 0%nat; rewrite mul0n.
    * move=> x0 p.
      exists (N.pos x0).
      rewrite ZposE -of_nat_hom in p.
      by rewrite NposE (of_nat_inj p).
    * case: x.
      - case: m => // *.
        by exists 0%nat; rewrite muln0.
      - move=> x p /(f_equal Z.sgn).
        by case: m.
Qed.

Lemma to_nat_pos m : (0 < Pos.to_nat m)%nat.
Proof.
  elim: m => // m IHm.
  apply (leq_trans IHm) => {IHm}.
  by rewrite -!NposE /= natTrecE -addnn leq_addr.
Qed.

Lemma of_nat_lt m n : reflect (Z.of_nat m < Z.of_nat n) (m < n)%nat.
Proof.
  apply/(iffP idP) => H.
  + elim: m n H => [[]//|] m IH []// n.
    rewrite ltnS => {}/IH H.
    rewrite -addn1 -[X in _ < _ X]addn1 !of_nat_hom' /= !Z.add_1_r.
    case: (Z.succ_lt_mono (Z.of_nat m) (Z.of_nat n)) => H0 _.
    apply/H0/H.
  + elim: m n H => [[]//|] m IH []// n.
    rewrite !ltnS => H.
    apply/IH; move: H.
    rewrite -addn1 -[X in _ < _ X]addn1 !of_nat_hom' /= !Z.add_1_r.
    case: (Z.succ_lt_mono (Z.of_nat m) (Z.of_nat n)) => _ H0.
    apply/H0.
Qed.

Lemma primeP' n : reflect (prime (Z.of_nat n)) (prime.prime n).
Proof.
  apply/(iffP idP) => H.
  + constructor.
    - case: n H => []//[]// n _.
      apply Pos.lt_1_succ.
    - move=> m H1mn.
      constructor.
      * exists m; by rewrite Z.mul_1_r.
      * exists (Z.of_nat n); by rewrite Z.mul_1_r.
      * case => [[]// ?|x |x ].
        + rewrite Z.mul_0_r => m0.
          by move: m0 H1mn => -> [].
        + case: m H1mn => [[]//|m H1mn|?[]//].
          rewrite !ZposE => /dvdnP' H1 /dvdnP' H2.
          apply/dvdnP'; rewrite dvdn1.
          case/primeP: H => n1 H.
          case/orP: (H _ H2) => // /eqP xn.
          move: xn H1 => -> /dvdn_leq H0.
          case: H1mn => m1 mn.
          have/H0: (0 < Pos.to_nat m)%nat by apply to_nat_pos.
          have: (Pos.to_nat m < n)%nat.
           rewrite /= ZposE in mn.
           by move/of_nat_lt : mn.
          by rewrite ltnNge => /negP H3 {}/H3.
        + case: m H1mn => [[]//|m H1mn|?[]//].
          rewrite -!Z.divide_Zpos_Zneg_l !ZposE => /dvdnP' H1 /dvdnP' H2.
          apply/dvdnP'; rewrite dvdn1.
          case/primeP: H => n1 H.
          case/orP: (H _ H2) => // /eqP xn.
          move: xn H1 => -> /dvdn_leq H0.
          case: H1mn => m1 mn.
          have/H0: (0 < Pos.to_nat m)%nat by apply to_nat_pos.
          have: (Pos.to_nat m < n)%nat.
           rewrite /= ZposE in mn.
           by move/of_nat_lt : mn.
          by rewrite ltnNge => /negP H3 {}/H3.
  + apply/primeP; split.
    - case: H => H1 H2.
      by apply/of_nat_lt/H1.
    - move=> d dn.
      case: H => H1 H2.
      case d1: (d == 1)%nat => //.
      case: d d1 dn => [_|[]// d _ dn].
      * by rewrite dvd0n eq_sym.
        rewrite /rel_prime in H2.
      * case d2: (d.+2 == n)%nat => //.
        have/H2 :1 <= Z.of_nat d.+2 < Z.of_nat n.
         split.
         - rewrite -addn1 !of_nat_hom'.
           have->: 1 = 0 + 1 by rewrite Z.add_0_l.
           apply Zplus_le_compat_r, Zle_0_nat.
         - have/dvdn_leq: (0 < n)%nat by case: n H1 {dn H2 d2}.
           by move=> /(_ _ dn); rewrite leq_eqVlt d2 => /of_nat_lt.
        case => _ _ /(_ (Z.of_nat d.+2)) H.
        have/dvdn_leq: (d.+2 %| 1)%nat by apply/dvdnP'/H; apply/dvdnP'.
        rewrite ltnS leqnn ltnS ltn0.
        by apply.
Qed.

Lemma of_nat_sub x0 x : (x0 > x)%nat -> Z.of_nat (x0 - x) = Z.of_nat x0 - Z.of_nat x.
Proof.
  elim: x0 x => // x0 IHx0 x xx0.
  rewrite trivial subSn // -addn1 of_nat_hom'.
  rewrite ltnS leq_eqVlt in xx0.
  case/orP: xx0 => [/eqP -> | H].
   by rewrite subnn Z.add_0_l Z.add_comm -Z.add_sub_assoc -Zminus_diag_reverse Z.add_0_r.
  by rewrite IHx0 // -[in RHS]Z.add_opp_r -[in RHS]Z.add_assoc [X in (Z.of_nat x0 + X)%Z]Z.add_comm Z.add_assoc.
Qed.

Lemma of_nat_exp x0 x : Z.of_nat (expn x0 x)%nat = Z.of_nat x0 ^ Z.of_nat x.
Proof.
  elim: x x0 => // x IHx x0.
  rewrite expnS of_nat_hom IHx trivial Z.mul_comm Zpower_exp ?Z.pow_1_r //.
  by elim: x {IHx}.
Qed.

Lemma pm : prime.prime (expn 2 19937 - 1)%nat.
Proof.
  apply/primeP'.
  rewrite of_nat_sub ?of_nat_exp; last by apply/ltn_trans/ltn_expl.
  set ln := Init.Nat.of_num_uint _.
  have ->: Z.of_nat ln = Zpos 19937 by [].
  apply Lucas.lucas_prime; by native_compute.
Qed.
