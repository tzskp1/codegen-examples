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

Lemma pm' : (prime (2 ^ (size phi).-1 - 1)).
Proof. by rewrite size_phi. Qed.

Definition f :=
   (@npoly_rV _ (size phi).-1)
 \o @irreducible.mulX _ pm'
 \o (@rVnpoly _ (size phi).-1).

Record random_state := {index : nat; state_vector :> n.-tuple (w.-tuple 'F_2)}.

Fixpoint rep T s (t : T) := if s is q.+1 then t :: rep q t else [::].
Lemma size_rep T s (t : T) : size (rep s t) == s.
Proof. by elim: s => //= s ->. Qed.

Definition dw := Tuple (size_rep w (0 : 'F_2)).

Lemma size_foldr_tuple T l (xs : seq (l.-tuple T)) :
size (foldr (fun (y : l.-tuple T) (x : seq T) => y ++ x) [::] xs) = (size xs * l)%nat.
Proof.
  elim: xs => // ?? IH.
  by rewrite /= size_cat IH size_tuple mulSn.
Qed.

Definition tuple_of_random_state_prf (rnd : random_state) :
  let vec := drop (index rnd %% n) rnd ++ take (index rnd %% n) rnd in
  let vec' := foldr (fun (y : w.-tuple 'F_2) (x : seq 'F_2) => y ++ x) [::]
                    (take n.-1 vec) ++ take (w - r) (last dw vec) in
  size vec' == p.
Proof.
  rewrite /= size_cat size_foldr_tuple ?size_take size_cat
          ?size_drop ?size_take ?size_tuple ltn_mod.
  case: n mn => //= n' ?.
  rewrite subnK; last by rewrite ltnW // ltn_mod.
  by rewrite ltnS leqnn /leq -subSn // subnAC subSn // subnn subn_eq0 r0
             mulSn addnBA // addnC.
Qed.

Definition tuple_of_random_state (rnd : random_state) :=
  Tuple (tuple_of_random_state_prf rnd).

Section Canonicals.
Definition zero := Tuple (size_rep p (0 : 'F_2)).

Definition xor l (V : zmodType) (x y : l.-tuple V) : l.-tuple V.
  apply/Tuple/(_ : size (map (fun xy => xy.1 + xy.2) (zip x y)) == l).
  case: x y => /= ? /eqP x [] /= ? /eqP y.
  by rewrite size_map size_zip x y minnn.
Defined.

Lemma xor0w : left_id zero (@xor _ _).
Proof.
  case=> x xi.
  apply/val_inj => /=.
  case: p p3 xi => // + _.
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
  case: p p3 xi => // + _.
  elim: x => // ?? IH sx xi /=.
  congr (_ :: _).
   by rewrite GRing.addrr_char2.
  rewrite eqSS in xi.
  case: sx xi => // /eqP/size0nil ->.
  by apply/size0nil.
Qed.

Lemma xorA : associative (@xor p [zmodType of 'F_2]).
Proof.
  move=> x y z.
  apply/val_inj => /=.
  have p0: (0 < p)%nat by case: p p3.
  elim: p p0 x y z => // s IH _.
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

Lemma xorC : commutative (@xor p [zmodType of 'F_2]).
Proof.
  move=> x y.
  apply/val_inj => /=.
  have p0: (0 < p)%nat by case: p p3.
  elim: p p0 x y => // s IH _.
  case=> [][]//= ??; rewrite eqSS => x.
  case=> [][]//= ??; rewrite eqSS => y.
  rewrite GRing.addrC.
  case: s x y IH => //.
   move/eqP/size0nil => ->.
   by move/eqP/size0nil => ->.
  move=> s x y IH.
  by move: (IH erefl (Tuple x) (Tuple y)) => /= ->.
Qed.

Lemma xorIw : left_inverse zero id (@xor p [zmodType of 'F_2]).
Proof. by move=> ?; rewrite xorww. Qed.

Definition w_zmixin := Eval hnf in ZmodMixin xorA xorC xor0w xorIw.
Canonical w_zmodtype := Eval hnf in ZmodType (p.-tuple 'F_2) w_zmixin.

-Definition scale (x : [ringType of 'F_2]) (y : w.-tuple 'F_2) : w.-tuple 'F_2 :=
-  if x == 0
-  then Tuple (size_rep _ 0)
-  else y.
-
-Lemma scalerv : forall a b v, scale a (scale b v) = scale (a * b) v.
-Proof. case=> [][? [][] ?|[]// ? [][|[]]] //. Qed.
-
-Lemma scale1v : left_id 1 scale.
-Proof. by []. Qed.
-
-Lemma scale0E y : scale 0 y = Tuple (size_rep _ 0).
-Proof. by []. Qed.
-
-Lemma scalerD : right_distributive scale (@xor w [zmodType of 'F_2]).
-Proof.
-  case=> [][|[]//] i *.
-  by rewrite /scale xor0w.
-Qed.
-
-Lemma zeroE : Tuple (size_rep w 0) = zero.
-Proof. by []. Qed.
-
-Lemma temp v : v = zero + v.
-Proof.
-  rewrite /GRing.add.
-  by rewrite /= xor0w.
-Qed.
-
-Lemma scale_morph :
-  forall v : w_zmodtype, {morph scale^~ v : a b / a + b >-> a + b}.
-Proof.
-  move=> v [][|[]//] x [][|[]//] y;
-   rewrite /scale /= ?zeroE.
-   by rewrite -temp.
-   by rewrite -temp.
-   rewrite GRing.addrC.
-   by rewrite -temp.
-   by rewrite /GRing.add /= xorww.
-Qed.
-
-Definition w_lmixin := LmodMixin scalerv scale1v scalerD scale_morph.
-Canonical w_lmodType := LmodType _ _ w_lmixin.
-
-Definition wrV (p : w.-tuple 'F_2) : 'rV['F_2]_w := \row_(i < w) p`_i.
-Definition rVw (v : 'rV['F_2]_w) : w.-tuple 'F_2 := mktuple (v 0).
-
-Lemma w_rV_K : cancel wrV rVw.
-Proof.
-move=> p /=; apply/val_inj.
-rewrite /wrV /rVw.
-have->: mktuple ((\row_i p`_i) 0) = mktuple (fun (i : 'I_w) => tnth p i).
- apply/eq_mktuple => ?.
- by rewrite mxE -tnth_nth.
-by rewrite /= map_tnth_enum.
-Qed.
-
-Lemma rV_w_K : cancel rVw wrV.
-Proof.
-move=> p /=.
-rewrite /wrV /rVw.
-apply/rowP => ?.
-by rewrite !mxE nth_mktuple.
-Qed.
-
-Lemma w_vect_axiom : Vector.axiom w (w.-tuple 'F_2).
-Proof.
-  exists wrV.
-   case=> [][|[]//] i x y.
-    have->: (Ordinal i = 0) by apply/val_inj.
-    by rewrite !GRing.scale0r !GRing.add0r.
-   have->: (Ordinal i = 1) by apply/val_inj.
-   rewrite !GRing.scale1r.
-   apply/rowP => X.
-   have xy: size x = size y.
-    by case: x y => ? /= /eqP -> [] ? /= /eqP ->.
-   rewrite !mxE /GRing.add (nth_map 0 0) ?nth_zip //
-           size_zip xy minnn.
-   by case: X x xy => ? ? [] ? /= /eqP -> <-.
-  exists rVw.
-   apply w_rV_K.
-   apply rV_w_K.
-Qed.
-
-Definition w_vmixin := VectMixin w_vect_axiom.
-Canonical w_vectType := VectType _ _ w_vmixin.

(* Check lin1_mx f. *)
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
