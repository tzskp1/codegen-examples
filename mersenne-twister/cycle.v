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
Proof.
by case: n mn m0 => //; case: m => []//[]// ?? + _; apply ltn_trans.
Qed.

Lemma w0 : 0 < w.
Proof.
  case: w rw r0 => //.
  by rewrite leqn0 => /eqP ->.
Qed.

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

(* Variable x : (p.*2).-tuple (w.-tuple 'F_2). *)

Fixpoint rep T s (t : T) := if s is q.+1 then t :: rep q t else [::].
Lemma size_rep T s (t : T) : size (rep s t) == s.
Proof. by elim: s => //= s ->. Qed.
Lemma size_mask X Y : size (rep (w - r) (X : 'F_2) ++ rep r (Y : 'F_2)) == w.
Proof. by rewrite size_cat !(eqP (size_rep _ _)) subnK. Qed.
Definition u := Tuple (size_mask 1 0).
Definition ll := Tuple (size_mask 0 1).

Definition xor l (V : zmodType) (x y : l.-tuple V) : l.-tuple V.
  apply/Tuple/(_ : size (map (fun xy => xy.1 + xy.2) (zip x y)) == l).
  case: x y => /= ? /eqP x [] /= ? /eqP y.
  by rewrite size_map size_zip x y minnn.
Defined.
Definition and (x y : w.-tuple 'F_2) : w.-tuple 'F_2.
  apply/Tuple/(_ : size (map (fun xy => xy.1 * xy.2) (zip x y)) == w).
  case: x y => /= ? /eqP x [] /= ? /eqP y.
  by rewrite size_map size_zip x y minnn.
Defined.

Section Canonicals.
Definition zero := Tuple (size_rep w (0 : 'F_2)).

Lemma xor0w : left_id zero (@xor _ _).
Proof.
  case=> x xi.
  apply/val_inj => /=.
  case: w w0 xi => // + _.
  elim: x => // ?? IH sx xi /=.
  congr (_ :: _).
   by rewrite GRing.add0r.
  rewrite eqSS in xi.
  case: sx xi => // /eqP/size0nil ->.
  by apply/size0nil.
Qed.

Lemma xorww x : xor x x = zero.
Proof.
  case: x => x xi.
  apply/val_inj => /=.
  case: w w0 xi => // + _.
  elim: x => // ?? IH sx xi /=.
  congr (_ :: _).
   by rewrite GRing.addrr_char2.
  rewrite eqSS in xi.
  case: sx xi => // /eqP/size0nil ->.
  by apply/size0nil.
Qed.

Lemma xorA : associative (@xor w [zmodType of 'F_2]).
Proof.
  move=> x y z.
  apply/val_inj => /=.
  elim: w w0 x y z => // s IH _.
  case=> [][]//= ??; rewrite eqSS => x.
  case=> [][]//= ??; rewrite eqSS => y.
  case=> [][]//= ??; rewrite eqSS => z.
  rewrite GRing.addrA.
  case: s x y z IH => //.
   move/eqP/size0nil => ->.
   move/eqP/size0nil => ->.
   by move/eqP/size0nil => ->.
  move=> s x y z IH.
  by move: (IH erefl (Tuple x) (Tuple y) (Tuple z)) => /= ->.
Qed.

Lemma xorC : commutative (@xor w [zmodType of 'F_2]).
Proof.
  move=> x y.
  apply/val_inj => /=.
  elim: w w0 x y => // s IH _.
  case=> [][]//= ??; rewrite eqSS => x.
  case=> [][]//= ??; rewrite eqSS => y.
  rewrite GRing.addrC.
  case: s x y IH => //.
   move/eqP/size0nil => ->.
   by move/eqP/size0nil => ->.
  move=> s x y IH.
  by move: (IH erefl (Tuple x) (Tuple y)) => /= ->.
Qed.

Lemma xorIw : left_inverse zero id (@xor w [zmodType of 'F_2]).
Proof. by move=> ?; rewrite xorww. Qed.

Definition w_zmixin := Eval hnf in ZmodMixin xorA xorC xor0w xorIw.
Canonical w_zmodtype := Eval hnf in ZmodType (w.-tuple 'F_2) w_zmixin.

Definition scale (x : [ringType of 'F_2]) (y : w.-tuple 'F_2) : w.-tuple 'F_2 :=
  if x == 0
  then Tuple (size_rep _ 0)
  else y.

Lemma scalerv : forall a b v, scale a (scale b v) = scale (a * b) v.
Proof. case=> [][? [][] ?|[]// ? [][|[]]] //. Qed.

Lemma scale1v : left_id 1 scale.
Proof. by []. Qed.

Lemma scale0E y : scale 0 y = Tuple (size_rep _ 0).
Proof. by []. Qed.

Lemma scalerD : right_distributive scale (@xor w [zmodType of 'F_2]).
Proof.
  case=> [][|[]//] i *.
  by rewrite /scale xor0w.
Qed.

Lemma zeroE : Tuple (size_rep w 0) = zero.
Proof. by []. Qed.

Lemma temp v : v = zero + v.
Proof.
  rewrite /GRing.add.
  by rewrite /= xor0w.
Qed.

Lemma scale_morph :
  forall v : w_zmodtype, {morph scale^~ v : a b / a + b >-> a + b}.
Proof.
  move=> v [][|[]//] x [][|[]//] y;
   rewrite /scale /= ?zeroE.
   by rewrite -temp.
   by rewrite -temp.
   rewrite GRing.addrC.
   by rewrite -temp.
   by rewrite /GRing.add /= xorww.
Qed.

Definition w_lmixin := LmodMixin scalerv scale1v scalerD scale_morph.
Canonical w_lmodType := LmodType _ _ w_lmixin.

Definition wrV (p : w.-tuple 'F_2) : 'rV['F_2]_w := \row_(i < w) p`_i.
Definition rVw (v : 'rV['F_2]_w) : w.-tuple 'F_2 := mktuple (v 0).

Lemma w_rV_K : cancel wrV rVw.
Proof.
move=> p /=; apply/val_inj.
rewrite /wrV /rVw.
have->: mktuple ((\row_i p`_i) 0) = mktuple (fun (i : 'I_w) => tnth p i).
 apply/eq_mktuple => ?.
 by rewrite mxE -tnth_nth.
by rewrite /= map_tnth_enum.
Qed.

Lemma rV_w_K : cancel rVw wrV.
Proof.
move=> p /=.
rewrite /wrV /rVw.
apply/rowP => ?.
by rewrite !mxE nth_mktuple.
Qed.

Lemma w_vect_axiom : Vector.axiom w (w.-tuple 'F_2).
Proof.
  exists wrV.
   case=> [][|[]//] i x y.
    have->: (Ordinal i = 0) by apply/val_inj.
    by rewrite !GRing.scale0r !GRing.add0r.
   have->: (Ordinal i = 1) by apply/val_inj.
   rewrite !GRing.scale1r.
   apply/rowP => X.
   have xy: size x = size y.
    by case: x y => ? /= /eqP -> [] ? /= /eqP ->.
   rewrite !mxE /GRing.add (nth_map 0 0) ?nth_zip //
           size_zip xy minnn.
   by case: X x xy => ? ? [] ? /= /eqP -> <-.
  exists rVw.
   apply w_rV_K.
   apply rV_w_K.
Qed.

Definition w_vmixin := VectMixin w_vect_axiom.
Canonical w_vectType := VectType _ _ w_vmixin.

Variable l : nat.

Definition lzero := Tuple (size_rep l (0 : w.-tuple 'F_2)).

Lemma lxor0w : left_id lzero (@xor _ _).
Proof.
  case=> x xi.
  apply/val_inj => /=.
  case: l xi.
   by move/eqP/size0nil => ->.
   elim: x => // ?? IH sx /= xi.
   congr (_ :: _).
    by rewrite GRing.add0r.
  rewrite eqSS in xi.
  case: sx xi => // /eqP/size0nil ->.
  by apply/size0nil.
Qed.

Lemma lxorA : associative (@xor l [zmodType of w.-tuple 'F_2]).
Proof.
  move=> x y z.
  apply/val_inj => /=.
  elim: l x y z => [|? IH];
  case=> [][|??]//=; rewrite ?eqSS => x;
  case=> [][|??]//=; rewrite ?eqSS => y;
  case=> [][|??]//=; rewrite ?eqSS => z.
  move: (IH (Tuple x) (Tuple y) (Tuple z)) => /= ->.
  by rewrite GRing.addrA.
Qed.

Lemma lxorC : commutative (@xor l [zmodType of w.-tuple 'F_2]).
Proof.
  move=> x y.
  apply/val_inj => /=.
  elim: l x y => [|? IH];
  case=> [][|??]//=; rewrite ?eqSS => x;
  case=> [][|??]//=; rewrite ?eqSS => y.
  move: (IH (Tuple x) (Tuple y)) => /= ->.
  by rewrite GRing.addrC.
Qed.

Lemma lxorww x : xor x x = lzero.
Proof.
  case: x => x xi.
  apply/val_inj => /=.
  elim: l x xi => [? /eqP/size0nil -> //|? IH []// ??].
  rewrite eqSS => ?.
  by rewrite /= IH // /GRing.add /= xorww.
Qed.

Lemma lxorIw : left_inverse lzero id (@xor l [zmodType of w.-tuple 'F_2]).
Proof. move=> ?; by rewrite lxorww. Qed.

Definition lw_zmixin := Eval hnf in ZmodMixin lxorA lxorC lxor0w lxorIw.
Canonical lw_zmodtype :=
  Eval hnf in ZmodType (l.-tuple (w.-tuple 'F_2)) lw_zmixin.

Definition lscale (x : [ringType of 'F_2])
           (y : lw_zmodtype) : lw_zmodtype :=
  if x == 0
  then Tuple (size_rep _ 0)
  else y.

Lemma lscalerv : forall a b v, lscale a (lscale b v) = lscale (a * b) v.
Proof. case=> [][? [][] ?|[]// ? [][|[]]] //. Qed.

Lemma lscale1v : left_id 1 lscale.
Proof. by []. Qed.

Lemma lscale0E y : lscale 0 y = Tuple (size_rep _ 0).
Proof. by []. Qed.

Lemma lscalerD : right_distributive lscale (@xor _ _).
Proof.
  case=> [][|[]//] i *.
  by rewrite /scale lxor0w.
Qed.

Lemma lzeroE : Tuple (size_rep l 0) = lzero.
Proof. by []. Qed.

Lemma lscale_morph :
  forall v : lw_zmodtype, {morph lscale^~ v : a b / a + b >-> a + b}.
Proof.
  move=> v [][|[]//] x [][|[]//] y;
  rewrite /lscale /= ?lzeroE; try by rewrite /GRing.add /= ?lxor0w.
  by rewrite GRing.addrC /GRing.add /= ?lxor0w.
  by rewrite /GRing.add /= ?lxorww.
Qed.

Definition lw_lmixin := LmodMixin lscalerv lscale1v lscalerD lscale_morph.
Canonical lw_lmodType := LmodType _ lw_zmodtype lw_lmixin.

Definition lwrV (p : lw_lmodType) : 'rV['F_2]_(l * w) := \row_(i < l * w) p`_(divn i w)`_(modn i w).

Definition mul_ord X Y : 'I_X -> 'I_Y -> 'I_(X * Y).
Proof.
  move=> x y.
  apply (@Ordinal (X * Y) (x * Y + y)).
  apply: leq_trans.
  apply: (_ : x * Y + y < x * Y + Y)%nat.
  rewrite ltn_add2l.
  case: y => //.
  have->: (x * Y + Y = x.+1 * Y)%nat.
   by rewrite mulSn addnC.
  rewrite leq_mul2r orbC.
  by case: x => //= + ->.
Defined.

Definition rVlw (v : 'rV['F_2]_(l * w)) : lw_lmodType :=
  mktuple (fun (X : 'I_l) => mktuple (fun (Y : 'I_w) => v 0 (mul_ord X Y))).

Lemma lw_rV_K : cancel lwrV rVlw.
Proof.
move=> p; rewrite /lwrV /rVlw; apply: eq_from_tnth => X.
rewrite tnth_mktuple; apply: eq_from_tnth => Y.
rewrite tnth_mktuple mxE.
have->: (mul_ord X Y %/ w)%nat = X.
 by rewrite divnMDl // divn_small // addn0.
have->: (mul_ord X Y %% w)%nat = Y.
 by rewrite modnMDl modn_small.
by rewrite -!tnth_nth.
Qed.

Lemma xwl (X : 'I_(l * w)) : (X %/ w < l)%N.
Proof.
 apply: leq_trans.
 apply: (_ : _ <= l * w %/ w)%nat.
 rewrite ltn_neqAle leq_div2r /= ?andbT ?mulnK //.
 apply/negPn => /eqP xwl.
 case: X xwl => x /= + xwl.
 rewrite -xwl => H.
 move: (leq_trans H (leq_trunc_div _ _)).
 by rewrite ltnn.
 rewrite ltnW //.
 rewrite mulnK //.
Qed.

Hint Resolve xwl : core.

Lemma rV_lw_K : cancel rVlw lwrV.
Proof.
move=> p /=.
rewrite /lwrV /rVlw.
apply/rowP => x.
case l0: (l == 0)%nat.
 case: x => // ? x.
 move: (x) => x0.
 by rewrite (eqP l0) mul0n ltn0 in x.
have d: 'I_l.
 case: l l0 => // *.
 apply: ord0.
have d0: 'I_w.
 case: w w0 => // *.
 apply: ord0.
have? : (x %/ w < l)%N.
 by apply xwl.
have? : (x %% w < w)%N.
 by rewrite ltn_mod.
rewrite !mxE (@nth_map _ d) ?size_enum_ord // (@nth_map _ d0) ?size_enum_ord //.
congr (p 0 _).
apply/val_inj => /=.
by rewrite !nth_enum_ord // -divn_eq.
Qed.

Lemma lw_vect_axiom : Vector.axiom (l * w) lw_lmodType.
Proof.
  exists lwrV.
   case=> [][|[]//] i x y.
    have->: (Ordinal i = 0) by apply/val_inj.
    by rewrite !GRing.scale0r !GRing.add0r.
   have->: (Ordinal i = 1) by apply/val_inj.
   rewrite !GRing.scale1r.
   apply/rowP => X.
   have xy: size x = size y.
    by case: x y => ? /= /eqP -> [] ? /= /eqP ->.
   rewrite !mxE /GRing.add ?(nth_map 0 0) ?nth_zip //=.
   rewrite !size_tuple //.
   rewrite size_zip.
   rewrite !size_tuple //.
   rewrite minnn ltn_mod //.
   rewrite size_zip.
   rewrite !size_tuple //.
   rewrite minnn xwl //.
  exists rVlw.
   apply lw_rV_K.
   apply rV_lw_K.
Qed.

Definition lw_vmixin := VectMixin lw_vect_axiom.
Canonical lw_vectType := VectType _ _ lw_vmixin.
End Canonicals.


(* Compute (1 : [fieldType of 'F_2]) + 1 == 0. *)

(* Variable initial : n.-tuple (w.-tuple 'F_2). *)

(* Definition *)

(*   Check rep. *)
(* iota *)

(* Check 'X. *)
(* Lemma pm' : prime (2 ^ (size phi).-1 - 1). *)
(* Proof. by rewrite size_phi. Qed. *)
(* Check @irreducible.mulX _ pm'. *)
(* Set Printing All. *)
(* Check linear _. *)
(* Check [VectType of {qpoly phi}]. *)

(* Lemma test : reflect _ ('X ^ (2 ^ m)%N %% phi == 'X %% phi). *)

End phi.

Definition test1 : seq 'F_2 := ([:: 1; 0; 0; 0; 0; 0; 0; 0])%R.
Definition test2 : seq 'F_2 := ([:: 1; 0; 0; 0; 0; 0; 0; 1])%R.
Lemma size_test1 : size test1 == 8.
  done.
  Defined.
Lemma size_test2 : size test2 == 8.
  done.
  Defined.
Compute val (and (Tuple size_test1) (Tuple size_test2)).
