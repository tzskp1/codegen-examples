From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require irreducible.
Require Import polyn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section phi.
Variables w n m r : nat.
Variable a : w.-tuple [fieldType of 'F_2].
Notation p := (n * w - r).
Hypothesis pm : prime (2 ^ p - 1).
Hypothesis mn : m < n.
Hypothesis m0 : 0 < m.
Hypothesis rw : r <= w.
Hypothesis r0 : 0 < r. (* TODO: move to Lemma *)
Hypothesis p3 : p >= 3.

Lemma n2 : 2 <= n.
Proof. by case: n mn m0 => //; case: m => []//[]// ?? + _; apply ltn_trans. Qed.

Lemma w0 : 0 < w.
Proof. by case: w rw r0 => //; rewrite leqn0 => /eqP ->. Qed.

Lemma rw' : r < w.
Proof. Admitted.

Hint Resolve n2 w0 : core.

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
  case: (size t) Ht => // ?.
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

Lemma mon_max r' E F :
  ((forall i, E i <= F i) -> \max_(i < r') E i <= \max_(i < r') F i)%nat.
Proof.
  elim: r' E F.
   move=> *.
   by rewrite big_ord0.
  move=> r' IH E F H.
  rewrite !big_ord_recr /=.
  rewrite /maxn.
  case: ifP => ?.
   apply: (leq_trans (H _)).
   by rewrite leq_max leqnn orbT.
  apply: (leq_trans (IH _ _ _)).
   move=> ?; apply H.
  by rewrite leq_max leqnn.
Qed.

Local Open Scope ring_scope.
Definition phi :=
  ('X ^+ n + 'X ^+ m) ^+ (w - r) * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ r
  + \sum_(i < r.-1) a`_i *: ('X ^+ n + 'X ^+ m) ^+ (w - r)
                     * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ (r.-1 - i)
  + \sum_(i < w - r.-1)
     a`_(r.-1 + i) *: ('X ^+ n + 'X ^+ m) ^+ (w - r - i).

Lemma size_phi : (size phi).-1 = p.
Proof.
  rewrite /phi /=.
  have?:(m.-1.+1 < n.-1.+1)%nat.
   by rewrite ?prednK // ?(esym (lt0n _)) ?(leq_trans _ mn).
  have?: (1 < size ('X^n + 'X^m)%R)%N.
   move=> ?.
   by rewrite size_addl ?size_polyXn // ltnS ?(ltn_trans _ mn).
  have?: (1 < size ('X^n.-1 + 'X^m.-1)%R)%N.
   move=> ?.
   rewrite size_addl ?size_polyXn ?size_polyX //.
   case: n mn => //[][]//.
   by case: m m0.
  have H : ('X^n.-1 + 'X^m.-1 != 0 :> {poly 'F_2})%R.
   by rewrite -size_poly_eq0 size_addl ?size_polyXn.
  have x : ('X^n + 'X^m != 0%R :> {poly 'F_2}).
   by rewrite -size_poly_eq0 size_addl ?size_polyXn.
  have H2: forall n', (('X^n + 'X^m) ^+ n' != 0 :> {poly 'F_2})%R.
   elim => [|? IHn].
    by rewrite GRing.expr0 GRing.oner_neq0.
   by rewrite GRing.exprS GRing.mulf_eq0 negb_or x.
  have H1: forall n', (('X^n.-1 + 'X^m.-1) ^+ n' != 0 :> {poly 'F_2})%R.
   elim => [|? IHn].
    by rewrite GRing.expr0 GRing.oner_neq0.
   by rewrite GRing.exprS GRing.mulf_eq0 negb_or H.
  rewrite !size_addl ?size_polyXn ?size_polyC //.
  + rewrite size_mul //.
    set T' := (_^n.-1 + _)%R.
    rewrite -(@prednK (size (T' ^+ r)%R)); last by rewrite lt0n size_poly_eq0 /T' H1.
    rewrite /T' addnS size_exp size_addl ?size_polyXn {T'}; last by [].
    set T' := (_ + _)%R.
    rewrite -(@prednK (size (T' ^+ (w - r)%nat)%R)); last by rewrite lt0n size_poly_eq0 /T' H2.
    rewrite /T' size_exp size_addl ?size_polyXn {T'}; last by [].
    rewrite mulnBr addSn /= addnBAC; last by apply: leq_mul.
    have H': (n = n.-1 + 1)%nat.
     by rewrite addn1 prednK // ?(ltn_trans _ mn).
    by rewrite [X in (_ + _ - X * r)%nat]H' mulnDl subnDA addnK mul1n.
  + apply: (leq_ltn_trans (size_sum _ _ _)).
    set T := (\max_(i < r.-1) size _%R).
    have/leq_ltn_trans: (T <= \max_(i < r.-1) size ((('X^n + 'X^m) ^+ (w - r)
                * ('X^n.-1 + 'X^m.-1) ^+ (r.-1 - i))%R : {poly 'F_2}))%N.
     subst T; apply: mon_max => i.
     case: a`_i => [][|[]//] H'.
      have->: (Ordinal H' = 0) by apply/val_inj.
      by rewrite !GRing.scale0r GRing.mul0r size_polyC eqxx.
     have->: (Ordinal H' = 1) by apply/val_inj.
     by rewrite !GRing.scale1r leqnn.
    apply.
    case r0': (0 < r.-1)%nat.
     have/eq_bigmax H': (0 < #|'I_r.-1|)%nat by rewrite card_ord.
     rewrite (proj2_sig (H' (fun i => size (('X^n + 'X^m) ^+ (w - r)
                                         * ('X^n.-1 + 'X^m.-1) ^+ (r.-1 - i))%R)))
             !size_mul // {T}.
     set T := size (('X^n + 'X^m) ^+ (w - r)).
     have->: T = T.-1.+1 by rewrite prednK // lt0n size_poly_eq0.
     rewrite !addSn ltn_add2l.
     apply: poly_exp_leq' => //.
      set X := sval _.
      case X0: (X == 0 :> nat)%nat.
       by move/eqP: X0 => ->; rewrite subn0; case: r r0.
      apply: leq_trans.
      apply irreducible.ltn_subr.
       case: X X0 => // ?? X0.
       by rewrite lt0n X0.
      by case: r r0.
    move: r0'; rewrite lt0n => /negP/negP/eqP => ->.
    by rewrite big_ord0 size_mul // -subn1 -addnBA ?ltn_addr // ?lt0n ?size_poly_eq0.
  + apply: (leq_ltn_trans (size_sum _ _ _)).
    set T := (\max_(i < w - r.-1) size _%R).
    have/leq_ltn_trans: (T <= \max_(i < w - r.-1) size (('X^n + 'X^m) ^+ (w - r - i) : {poly 'F_2}))%nat.
     subst T; apply: mon_max => i.
     case: a`_(r.-1 + i) => [][|[]//] H'.
      have->: (Ordinal H' = 0) by apply/val_inj.
      by rewrite !GRing.scale0r size_polyC eqxx.
     have->: (Ordinal H' = 1) by apply/val_inj.
     by rewrite !GRing.scale1r leqnn.
    apply.
    case w0: (w - r.-1 == 0)%nat.
     move/eqP: w0 => ->.
     by rewrite big_ord0 size_mul // -subn1 -addnBA ?ltn_addr // ?lt0n ?size_poly_eq0.
    move/negP/negP: w0; rewrite -lt0n => w0.
    have/eq_bigmax H': (0 < #|'I_(w - r.-1)|)%nat by rewrite card_ord.
    rewrite (proj2_sig (H' (fun i => size (('X^n + 'X^m) ^+ (w - r - i)))))%nat
            !size_mul // {T}.
    set T := sval _.
    case: T => [][?|].
     rewrite /= -subn1 subn0 -[X in (X < _)%nat]addn0 -addnBA
            ?lt0n ?size_poly_eq0 // ltn_add2l.
     rewrite subn1 size_exp size_addl ?size_polyXn ?size_polyX //.
     case: n mn mn m0 => []//[|????]; first by case: m.
     by rewrite mulSn ltn_addr.
    move=> s i.
    rewrite /= -subn1 -addnBA ?lt0n ?size_poly_eq0 // subn1.
    case wr0: (w - r == 0)%nat.
     move/eqP: wr0 => ->.
     rewrite sub0n GRing.expr0 size_polyC /=.
     rewrite -[X in (X < _)%nat]addn0.
     rewrite ltn_add2l size_exp size_addl ?size_polyXn //.
     case: n mn mn m0 => []//[|????]; first by case: m.
     by rewrite mulSn ltn_addr.
    rewrite ltn_addr //.
    apply: poly_exp_leq' => //.
    rewrite /leq -subSn.
     by rewrite subnAC subSnn.
    move: i.
    by rewrite -subn1 subnBA // addn1 subSn //.
  + apply: (leq_ltn_trans (size_sum _ _ _)).
    set T := (\max_(i < r.-1) size _%R).
    have/leq_ltn_trans:
      (T <= \max_(i < r.-1) size (('X^n + 'X^m) ^+ (w - r)
                        * ('X^n.-1 + 'X^m.-1) ^+ (r.-1 - i) : {poly 'F_2})%R)%nat.
     subst T; apply: mon_max => i.
     case: a`__ => [][|[]//] H'.
      have->: (Ordinal H' = 0) by apply/val_inj.
      by rewrite !GRing.scale0r GRing.mul0r size_polyC eqxx.
     have->: (Ordinal H' = 1) by apply/val_inj.
     by rewrite !GRing.scale1r leqnn.
    apply.
    case r0': (0 < r.-1)%nat.
     have/eq_bigmax H': (0 < #|'I_r.-1|)%nat by rewrite card_ord.
     rewrite (proj2_sig (H' (fun i => size (('X^n + 'X^m) ^+ (w - r)
                                         * ('X^n.-1 + 'X^m.-1) ^+ (r.-1 - i))%R)))
             !size_mul // {T}.
     set T := size (('X^n + 'X^m) ^+ (w - r)).
     have->: T = T.-1.+1 by rewrite prednK // lt0n size_poly_eq0.
     rewrite !addSn ltn_add2l.
     apply: poly_exp_leq' => //.
      set X := sval _.
      case X0: (X == 0 :> nat)%nat.
       by move/eqP: X0 => ->; rewrite subn0; case: r r0.
      apply: leq_trans.
      apply irreducible.ltn_subr.
       case: X X0 => // ?? X0.
       by rewrite lt0n X0.
      by case: r r0.
    move: r0'; rewrite lt0n => /negP/negP/eqP => ->.
    by rewrite big_ord0 size_mul // -subn1 -addnBA ?ltn_addr // ?lt0n ?size_poly_eq0.
Qed.

Lemma X2X : 'X ^ 2 %% phi != 'X %% phi.
Proof.
  rewrite -GRing.subr_eq0 -modp_opp -modp_add.
  apply/negP => /dvdp_leq H.
  have/H: 'X ^ 2 - 'X != 0 :> {poly 'F_2}.
   rewrite GRing.subr_eq0.
   apply/negP => /eqP/(f_equal (size : {poly 'F_2} -> nat)).
   by rewrite size_polyXn size_polyX.
  case: (size phi) size_phi => //= p0 => [|->].
   by move: p0 pm => <-; rewrite expn0 subn1.
  rewrite size_addl ?size_polyXn ?size_opp ?size_polyX //.
  by apply/negP; rewrite -leqNgt.
Qed.

Lemma pm' : prime (2 ^ (size phi).-1 - 1).
Proof. by rewrite size_phi. Qed.

Variable x : 'M['F_2]_(n, w).

Definition and (x y : 'rV['F_2]_w) :=
  \row_i ((x ord0 i) * (y ord0 i)).

Definition shiftr : 'M['F_2]_w :=
  \matrix_(i, j) (1 *+ (i == j.+1 :> nat)).

Definition A := \matrix_j (\row_i a`_i *+ (j == w :> nat)) + shiftr.

Lemma tecr : r = r.-1.+1.
Proof. by case: r r0. Qed.

Lemma tecwr : (w - r = (w - r).-1.+1)%nat.
Proof. by rewrite prednK // /leq subnBA // add1n subn_eq0 rw'. Qed.

Lemma tecw : ((w - r).-1.+1 + r.-1.+1 = w)%nat.
Proof. by rewrite !prednK // ?subnK // /leq subnBA // add1n subn_eq0 rw'. Qed.

Lemma tecnw : (w + n.-1 * w = n * w)%nat.
Proof.
  rewrite -mulSn prednK //.
  by case: n mn.
Qed.

Definition S := castmx (etrans (addnC _ _) tecw, tecw)
                (block_mx 0 (castmx (tecr, tecr) 1%:M)
                          (castmx (tecwr, tecwr) 1%:M) 0) *m A.
Definition B := castmx (etrans (addnC _ _) tecnw, tecnw)
                       (block_mx (\matrix_(i, j) (1 *+ (i == j - m :> nat)%nat)) 1%:M
                                 S 0).
Check row_mx S 0 : 'M_(w, w + n.-1 * w).
Check etrans (addnC _ _) tecw.
Check
Check pid_mx
      (1 : 'M_r).
Check block_mx 0 (1 : 'M_(w - r)) 0 1.
Check row _ x.
Check map (fun i => row i x) (enum 'I_n).
size (map (fun i => let y := and x`_(i %% n) u + and x`_(i.+1 %% n) ll in
                 x`_(i + m %% n) + shift1 y + if y`_0 == 1 then a else 0) (iota 0 n))

Check _ *m _.
Check copid_mx (w - r) : 'M['F_2]_w.
Check pid_mx (w - r) : 'M['F_2]_w.
Compute ((pid_mx (1 : 'F_2) : 'M_(1, 1)) 0 0).

Check row _ x.

'rV_w
Check mxvec x.
Check delta_mx.

Definition shift1 (x : w.-tuple 'F_2) : w.-tuple 'F_2.
  apply/Tuple/(_ : size (0 :: take w.-1 x) == w).
  rewrite /= size_take size_tuple.
  case: w w0 => //= *.
  by rewrite ltnS leqnn.
Defined.

Lemma sizef x :
  size (map (fun i => let y := and x`_(i %% n) u + and x`_(i.+1 %% n) ll in
             x`_(i + m %% n) + shift1 y + if y`_0 == 1 then a else 0) (iota 0 n))


Check vec_mx.
Check mxvec.
Check mulmx (_ : 'M_(m, n)) : {linear _ -> _}.

End phi.
(* Definition w := 32. *)
(* Definition r := 1. *)
(* Definition n := 4. *)
(* Definition m := 1. *)
(* Lemma sizea : size ([:: 1;0;0;1;1;0;0;1;0;0;0;0;1;0;0;0;1;0;1;1;0;0;0;0;1;1;0;1;1;1;1;1] : seq 'F_2)%R == w. *)
(*   done. *)
(* Qed. *)

(* Lemma nm : m < n. *)
(*   by []. *)
(* Defined. *)
(* Lemma pm'': prime (2 ^ (n * w - r) - 1). *)
(* Proof. *)
(*   Admitted. *)
(* Definition B := lin1_mx (@f _ _ _ _ (Tuple sizea) pm'' nm erefl erefl erefl). *)
(* Compute B. *)
(* Variable j : 'I_(size (phi n m r (Tuple sizea))).-1. *)
(* Check lin_mx. *)
(* Check lin1_mx. *)
(* Lemma BE : B (delta_mx 0%R j) = B (delta_mx 0%R j) . *)
(* rewrite /B /f. *)

(* rewrite /= /rVnpoly /comp rVpoly_delta. *)
(* rewrite /irreducible.mulX /irreducible.mulV. *)
(* rewrite /insubd. *)
(*       Check row_mx 0. *)
(* Check delta_mx *)

(* Compute B 0. *)
