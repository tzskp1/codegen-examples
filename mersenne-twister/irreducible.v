From mathcomp
Require Import all_ssreflect all_algebra all_field all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma f2p_monic (p : {poly 'F_2}) :
  (p != 0)%R -> p \is monic.
Proof.
  move=> /negPf p0; apply/eqP.
  case lp0: (lead_coef p == 0)%R.
   by rewrite lead_coef_eq0 p0 in lp0.
  case: (lead_coef p) lp0 => [][]//[]// *.
  by apply/val_inj.
Qed.

Lemma f2eqp_eq (p q : {poly 'F_2}) : (p %= q)%R = (p == q).
Proof.
  case q0: (q == 0%R).
   by move/eqP: q0 => ->; rewrite eqp0.
  case p0: (p == 0%R).
   by move/eqP: p0 => ->; rewrite eq_sym -eqp0 eqp_sym.
  rewrite eqp_monic // f2p_monic //.
  + by move/negP/negP: p0.
  + by move/negP/negP: q0.
Qed.

Lemma lem1 q n : prime q -> (n < q -> n.+1 != n %[mod q])%N.
Proof.
  move=> Hq nq.
  case n0: (n == 0)%N.
   move/eqP: n0 => ->.
   rewrite mod0n modn_small //.
   by case: q Hq nq => []//[].
  case nsq: (n.+1 == q).
   move/eqP: nsq => <-.
   by rewrite modnn modn_small // eq_sym n0.
  have nsq': (n.+1 < q)%N
   by rewrite ltn_neqAle nq nsq.
  rewrite !modn_small //.
  by elim n.
Qed.

Lemma exp2_dvd a b :
  2^(a * b) - 1 = (2^a - 1) * \sum_(i < b) 2 ^ (a * (b - i.+1)).
Proof.
elim: b => [|b IHb]; first by rewrite muln0 expn0 subn1 big_ord0 muln0.
rewrite big_ord_recl mulnDr -IHb mulnBl !subn1 -mulnBl mulnS expnD.
have H: forall a, 2 ^ a = 2 ^ a - 1 + 1 by move=> *; rewrite subnK // expn_gt0.
by rewrite [in LHS]H mulnDl mul1n [X in _ + X]H addn1 !addnS !subn1.
Qed.

Lemma m_is_prime m : prime (2 ^ m - 1) -> prime m.
Proof.
apply: contraLR => /primePn []; first by case: m => []//[].
case => a aH /dvdnP[] b mba; move: mba aH => -> mba.
rewrite exp2_dvd; apply/primePn; right.
exists (2 ^ b - 1); rewrite ?dvdn_mulr //.
have? : 1 < 2 ^ b - 1.
 case: b mba => [|[|b _]].
  by rewrite mul0n ltn0 andbF.
  by rewrite mul1n ltnn andbF.
 have: 2 ^ b > 0 by rewrite expn_gt0.
 rewrite subn1 !expnS !mul2n.
 by case: (2 ^ b).
apply/andP; split => //; apply/ltn_Pmulr/ltnW => //.
case: a mba => []//[]// a mba.
rewrite !big_ord_recr /= subnn muln0 expn0 -[X in X < _]add0n ltn_add2r.
by rewrite subSnn muln1 ltn_addl // expn_gt0.
Qed.

Section iter_lin.
Variable K : fieldType.
Variable R : vectType K.
Variable f : {linear R -> R}%R.
Lemma iter_linear m : linear (iter m f).
Proof.
  elim: m => // m IHm a x y.
  by rewrite !iterSr !GRing.linearP IHm.
Qed.
Canonical iter_linearType m := Linear (iter_linear m).
End iter_lin.

Section Quotient.
Variable phi : {poly 'F_2}.
Variable phi_gt1 : size phi > 1.
Local Open Scope ring_scope.
Import GRing.Theory.
Import Pdiv.Ring.
Import Pdiv.RingMonic.

Lemma ltn_phi_pred : ((size phi).-1 < size phi)%nat.
Proof. by case: (size phi) phi_gt1. Qed.

Lemma phi_neq0 : phi != 0.
Proof.
  rewrite -size_poly_eq0.
  by case: (size phi) phi_gt1.
Qed.

Lemma phi_is_monic : phi \is monic.
Proof. by apply f2p_monic; rewrite -size_poly_gt0 ltnW. Qed.

Hint Resolve phi_is_monic phi_neq0 ltn_phi_pred : core.

Definition phiI := rdvdp phi.
Fact phiI_key : pred_key phiI. Proof. by []. Qed.

Canonical keyd_phiI : keyed_pred phiI_key.
by apply (@PackKeyedPred _ _ phiI_key (rdvdp phi)).
Defined.

Lemma phiI_addr_closed: addr_closed phiI.
Proof.
  split => [|??].
  * by rewrite unfold_in; apply/eqP/rmod0p.
  * rewrite !unfold_in rmodp_add // => /eqP ->.
    by rewrite add0r.
Qed.

Lemma phiI_oppr_closed: oppr_closed phiI.
Proof.
  move=> x.
  rewrite !unfold_in -mulN1r -rmodp_mulmr // => /eqP ->.
  by rewrite mulr0 rmod0p.
Qed.

Lemma phiI_proper_ideal : proper_ideal phiI.
Proof.
  split => [|??].
  * by rewrite unfold_in rmodp_small ?size_polyC ?size_p oner_neq0.
  * rewrite !unfold_in -rmodp_mulmr ?f2p_monic // => /eqP ->.
    by rewrite mulr0 rmod0p.
Qed.

Canonical phiI_addrPred := AddrPred phiI_addr_closed.
Canonical phiI_zmodPred := ZmodPred phiI_oppr_closed.
Canonical phiI_idealr := MkIdeal phiI_zmodPred phiI_proper_ideal.

Local Open Scope quotient_scope.

Definition QphiI := {ideal_quot keyd_phiI}.

Definition QphiI_rV (x : QphiI) : 'rV['F_2]_(size phi).-1 :=
  poly_rV (rmodp (generic_quotient.repr x) phi).
Definition rVQphiI : 'rV['F_2]_(size phi).-1 -> QphiI :=
  \pi \o rVpoly.

Lemma QphiI_rV_K : cancel QphiI_rV rVQphiI.
Proof.
move=> x.
rewrite /rVQphiI /QphiI_rV /= poly_rV_K;
last by case: (size phi) (ltn_rmodpN0 (generic_quotient.repr x) phi_neq0) phi_gt1.
rewrite -[x in RHS]reprK !piE /=.
apply/eqP.
by rewrite -Quotient.idealrBE /= unfold_in rmodp_add //
           rmodp_small ?ltn_rmodp // -rmodp_add // subrr rmod0p.
Qed.

Lemma rVQphiIK : cancel rVQphiI QphiI_rV.
Proof.
move=> x.
rewrite /rVQphiI /QphiI_rV /= -[RHS]rVpolyK; congr (poly_rV _).
case: piP => y /eqP.
rewrite -Quotient.idealrBE unfold_in rmodp_add // addr_eq0
        -!Pdiv.IdomainMonic.modpE // modp_opp opprK => /eqP <-.
rewrite modp_small //.
by apply(leq_ltn_trans (size_poly _ _)).
Qed.

Hint Resolve QphiI_rV_K rVQphiIK : core.

Canonical QphiI_finMixin := CanFinMixin QphiI_rV_K.
Canonical QphiI_finType := FinType QphiI QphiI_finMixin.
Canonical Quotient.rquot_comRingType.
Canonical QphiI_unitRingMixin :=
  Eval hnf in FinRing.Ring.UnitMixin [finRingType of QphiI].
Canonical QphiI_unitRingType := UnitRingType QphiI QphiI_unitRingMixin.
Canonical QphiI_comUnitRingType := Eval hnf in [comUnitRingType of QphiI].
Canonical QphiI_finComUnitRingType := Eval hnf in [finComUnitRingType of QphiI].
Canonical QphiI_finUnitRingType := Eval hnf in [finUnitRingType of QphiI].
Canonical QphiI_zmodType := Eval hnf in [zmodType of QphiI].

Lemma QphiI_rV_D A B : QphiI_rV (A + B) = QphiI_rV A + QphiI_rV B.
Proof.
  rewrite -linearD -rmodp_add //; congr (poly_rV _).
  rewrite -[A]reprK -[B]reprK.
  case: piP => a ->; case: piP => b ->.
  rewrite -rmorphD; case: piP => ab /eqP.
  by rewrite -Quotient.idealrBE unfold_in -!Pdiv.IdomainMonic.modpE //
             modp_add modp_opp subr_eq0 eq_sym => /eqP.
Qed.

Local Definition scale a v := rVQphiI (scalemx a (QphiI_rV v)).
Local Fact scale1x A : scale 1 A = A.
Proof. by rewrite /scale scale1mx QphiI_rV_K. Qed.
Local Fact scaleA x y A : scale x (scale y A) = scale (x * y) A.
Proof. by rewrite /scale rVQphiIK scalemxA. Qed.
Local Fact scalexDl A x y : scale (x + y) A = scale x A + scale y A.
Proof. by rewrite /scale scalemxDl -rmorphD -linearD. Qed.
Local Fact scalexDr x A B : scale x (A + B) = scale x A + scale x B.
Proof. by rewrite /scale -rmorphD -linearD -scalemxDr QphiI_rV_D. Qed.
Definition QphiI_lmodMixin := LmodMixin scaleA scale1x scalexDr scalexDl.
Canonical QphiI_lmodType :=
  Eval hnf in LmodType 'F_2 QphiI QphiI_lmodMixin.

Lemma QphiI_rV_scaler a A : QphiI_rV (a *: A) = a *: QphiI_rV A.
Proof.
case: a => [][|[]]// i.
* have->: Ordinal i = 0 by apply/val_inj.
  rewrite !scale0r /QphiI_rV -pi_zeror.
  case: piP => x /eqP.
  rewrite -Quotient.idealrBE sub0r unfold_in -!Pdiv.IdomainMonic.modpE //
          modp_opp oppr_char2
          ?(GRing.rmorph_char (polyC_rmorphism [ringType of 'F_2])) // => /eqP ->.
  by rewrite linear0.
* have->: Ordinal i = 1 by apply/val_inj.
  by rewrite !scale1r.
Qed.

Lemma QphiI_vect_axiom : Vector.axiom (size phi).-1 QphiI.
Proof.
by exists QphiI_rV; [move=> ???; rewrite QphiI_rV_D QphiI_rV_scaler|exists rVQphiI].
Qed.

Definition QphiI_vect_mixin := VectMixin QphiI_vect_axiom.
Canonical QphiI_vect_type := VectType 'F_2 QphiI QphiI_vect_mixin.

Lemma pi_phi0 : \pi phi = 0 :> QphiI.
Proof.
have->: 0 = \pi 0 :> QphiI by rewrite pi_zeror.
apply/eqP.
by rewrite -Quotient.idealrBE subr0 unfold_in rmodpp.
Qed.

Lemma pi1 : \pi 1 = 1 :> QphiI.
Proof. by rewrite -pi_oner. Qed.

Lemma piM p q : \pi_QphiI (p * q) = (\pi p : QphiI) * \pi q.
Proof. by rewrite -rmorphM. Qed.

Lemma piD p q : \pi_QphiI (p + q) = (\pi p : QphiI) + \pi q.
Proof.
by rewrite (rmorphD (pi_rmorphism (Quotient.rquot_ringQuotType keyd_phiI))).
Qed.

Lemma piB p q : \pi_QphiI (p - q) = (\pi p : QphiI) - (\pi q : QphiI).
Proof.
by rewrite (rmorphB (pi_rmorphism (Quotient.rquot_ringQuotType keyd_phiI))).
Qed.

Lemma card_QphiI : (#|[finType of QphiI]| = 2 ^ (size phi).-1)%N.
Proof.
have<-: (#|'rV['F_2]_(size phi).-1| = 2 ^ (size phi).-1)%nat
 by rewrite card_matrix mul1n card_ord.
apply/eqP; rewrite eqn_leq; apply/andP; split.
* move: (@card_in_image _ _ QphiI_rV predT) <- => [|????];
   last by apply (can_inj QphiI_rV_K).
  by apply/subset_leq_card/subsetP.
* move: (@card_in_image _ _ rVQphiI predT) <- => [|????];
   last by apply (can_inj rVQphiIK).
  by apply/subset_leq_card/subsetP.
Qed.

Definition QphiIX : (size phi).-1.-tuple QphiI_lmodType
  := [tuple \pi 'X^i | i < (size phi).-1].

Lemma QphiIXE (i : 'I_(size phi).-1) : QphiIX`_i = \pi 'X^i.
Proof. by rewrite nth_mktuple. Qed.

Lemma pi_linear : linear (\pi : _ -> [lmodType 'F_2 of QphiI]).
Proof.
  move=> a x y.
  case: a => [][|[]//] i.
    have->: Ordinal i = 0 by apply/val_inj.
    by rewrite !scale0r !add0r.
   have->: Ordinal i = 1 by apply/val_inj.
   by rewrite !scale1r -rmorphD.
Qed.
Canonical pi_linearType := Linear pi_linear.

Lemma QphiIX_free : free QphiIX.
Proof.
apply/freeP => k.
set T := \sum__ _; have->: T = \sum_(i < (size phi).-1) \pi_QphiI (k i *: 'X^i).
 apply/eq_bigr => j _.
 by rewrite QphiIXE -[k j *: 'X^j]addr0 linearP /= pi_zeror addr0.
rewrite -linear_sum -pi_zeror => /eqP.
rewrite -Quotient.idealrBE unfold_in subr0 rmodp_small; last first.
* apply/(leq_ltn_trans (size_sum _ _ _))/leq_trans/ltn_phi_pred/bigmax_leqP=> i _.
  by apply/(leq_trans (size_scale_leq _ _)); rewrite size_polyXn.
* move: k {T}; elim: (size phi).-1 => [?? [] //|n IHn k].
  rewrite big_ord_recr /=.
  case k0: (k ord_max == 0).
   rewrite (eqP k0) scale0r addr0 => /IHn H i.
   case: (splitP (cast_ord (esym (addn1 _)) i)) => j ji.
    move/H: (j) <-; congr (k _); apply/ord_inj.
    by rewrite /= -ji.
   suff->: i = ord_max by apply/eqP.
   case: j ji => [][|[]//] ?.
   rewrite /= addn0 => ?.
   by apply/ord_inj.
  case: (k ord_max) k0 => [][|[]]// i; have->: Ordinal i = 1 by apply/ord_inj.
  rewrite scale1r addr_eq0 => _ /eqP/(f_equal (size : {poly 'F_2} -> _)).
  rewrite size_opp size_polyXn => C.
  suff: (n.+1 < n.+1)%nat by rewrite ltnn.
  rewrite -[X in (X < _)%nat]C.
  apply/(leq_ltn_trans (size_sum _ _ _))/bigmax_leqP => j _.
  by apply/(leq_trans (size_scale_leq _ _)); rewrite size_polyXn.
Qed.

Lemma dim_QphiI : \dim (fullv : {vspace QphiI}) = (size phi).-1.
Proof. by rewrite [LHS]mxrank_gen mxrank1. Qed.

Lemma QphiIX_full : basis_of fullv QphiIX.
Proof.
by rewrite basisEfree QphiIX_free subvf size_map size_enum_ord dim_QphiI /=.
Qed.

Section Field.
Variable ip : irreducible_poly phi.
Definition QphiI_inv (q : QphiI) :=
  if q == 0 then 0
  else \pi_QphiI ((egcdp phi (generic_quotient.repr q)).2 %% phi).

Lemma QphiI_field : GRing.Field.axiom QphiI_inv.
Proof.
  move=> p /negPf i.
  rewrite /QphiI_inv i -[p in _ * p]reprK -piM -pi1.
  apply/eqP.
  set P := (generic_quotient.repr p).
  rewrite -Quotient.idealrBE unfold_in rmodp_add //
          [rmodp (-1) _]rmodp_small ?size_opp ?size_polyC //
          subr_eq0 -f2eqp_eq // -Pdiv.IdomainMonic.modpE //
          mulrC modp_mul mulrC.
  have<-: (((egcdp phi P).1 * phi + (egcdp phi P).2 * P)) %% phi =
          ((egcdp phi P).2 * P) %% phi
   by rewrite modp_add -modp_mul modpp mulr0 mod0p add0r.
  have->: ((egcdp phi P).1 * phi + (egcdp phi P).2 * P) = gcdp phi P
   by apply/esym/eqP; rewrite -f2eqp_eq // egcdpE.
  suff: gcdp phi P %= 1.
   rewrite !f2eqp_eq => /eqP ->.
   by rewrite modp_small // size_polyC.
  rewrite eqp_sym; apply/eqp_trans/gcdp_modr; rewrite eqp_sym.
  rewrite -size_poly_eq1; apply/eqP; rewrite coprimep_size_gcd //.
  apply/coprimepP => d.
  case d0: (size d == 0)%nat.
   rewrite size_poly_eq0 in d0.
   rewrite (eqP d0) dvd0p => /negPn.
   by rewrite phi_neq0.
  case d1: (size d == 1)%nat.
   case: d d0 d1 => [][|[]]//[|[]]// i0 []//= *.
   set T := Polynomial _; have->: T = 1.
    apply/val_inj; rewrite /= polyseq1.
    congr (_ :: _); apply/val_inj.
    by rewrite /= modn_small //.
   by rewrite eqpxx.
  case: (ip) => _ H1 H2.
  move/H1: H2; rewrite d1 => /implyP /=.
  rewrite f2eqp_eq => /eqP -> /dvdp_leq.
  rewrite leqNgt ltn_modp phi_neq0 => C.
  suff: false by []; apply/C.
  rewrite -[p]reprK -pi_zeror -Quotient.idealrBE subr0 unfold_in
             -Pdiv.IdomainMonic.modpE // in i.
  by rewrite i.
Qed.

Lemma QphiI_inv0 : QphiI_inv 0 = 0.
Proof. by rewrite /QphiI_inv eqxx. Qed.

Definition QphiI_fieldMixin :=
  @FieldMixin [comRingType of QphiI] QphiI_inv QphiI_field QphiI_inv0.
Definition QphiI_fieldType :=
  Eval hnf in FieldType _ QphiI_fieldMixin.

End Field.
End Quotient.

Section Irreducible.
Variable phi : {poly 'F_2}.
Local Notation m := (size phi).-1.
Hypothesis pm : prime (2 ^ m - 1).
Local Notation m_is_prime := (m_is_prime pm).

Lemma phi_gt1 : 1 < size phi.
Proof. by case: (size phi) m_is_prime => []//[]. Qed.

Lemma phi_gt2 : 2 < size phi.
Proof. by case: (size phi) m_is_prime => []//[]//[]. Qed.

Lemma phi_gt0 : 0 < size phi.
Proof. by case: (size phi) m_is_prime. Qed.

Lemma power_gt0 : 0 < 2 ^ m.
Proof. by case: (2 ^ m) pm. Qed.

Lemma predpower_gt0 : 0 < 2 ^ m - 1.
Proof. by case: (2 ^ m - 1) pm. Qed.

Lemma predpower_gt0' : 0 < (2 ^ m).-1.
Proof. by rewrite -subn1 predpower_gt0. Qed.

Lemma predpower_gt1 : 1 < 2 ^ m.
Proof.
  case: (2 ^ m) pm => // n.
  rewrite subSS ltnS subn0.
  by case n.
Qed.

Lemma predpower_neq0 : 0 != 2 ^ m - 1.
Proof. by case: (2 ^ m - 1) pm. Qed.

Lemma predpower_gt_succpower : (2 ^ m).-1 < (2 ^ m).+1.
Proof. by case: (2 ^ m) pm. Qed.

Lemma phi_gtb (b : bool) : b < size phi.
Proof. by case: b; rewrite ?phi_gt1 ?phi_gt0. Qed.

Lemma predphi_neq0 : m != 0.
Proof. by case: m m_is_prime. Qed.

Lemma predphi_gt1 : 1 < m.
Proof. by case: m m_is_prime => []//[]. Qed.

Lemma predpredpower_power : (2 ^ m - 1).-1 < 2 ^ m - 1.
Proof. by case: (2 ^ m - 1) pm. Qed.

Lemma predpredpower_gt0 : 0 < (2 ^ m - 1).-1.
Proof. by case: (2 ^ m - 1) pm => []//[]. Qed.

Lemma p_ord_prf : (2 ^ m - 1 < (2 ^ m).+1)%N.
Proof. by rewrite subn1 predpower_gt_succpower. Qed.

Lemma predphi_geq1 : 1 <= m.
Proof. by case: m m_is_prime => []//[]. Qed.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.
Import GRing.Theory.
Import Pdiv.Ring.
Import Pdiv.RingMonic.

Hint Resolve (phi_is_monic phi_gt1) (phi_neq0 phi_gt1)
     phi_gt1 phi_gt2 phi_gt0
     phi_gtb predphi_neq0 predphi_gt1 predpredpower_power
     predpredpower_gt0 p_ord_prf predphi_geq1
     predpower_gt_succpower predpower_gt1
     power_gt0 predpower_gt0 predpower_neq0 : core.

Section Order.
(*
based on:
 http://www.math.sci.hiroshima-u.ac.jp/~m-mat/TEACH/0407-2.pdf
 P. 27
*)
Definition stab (a : QphiI phi_gt1) n := (a ^+ n * a == a) && (n > 0)%nat.

Variable x : QphiI phi_gt1.
Variable H1 : (x ^ 2 != x)%R.
Variable H2 : (x ^ (2 ^ m)%N == x)%R.

Lemma exstab : stab x (2 ^ m - 1)%nat.
Proof. by rewrite /stab -exprSr subn1 prednK // H2 -subn1. Qed.

Definition minstab := ex_minn (@ex_intro _ (stab x) _ exstab).

Lemma minstab_cond : stab x minstab.
Proof.
  rewrite /minstab.
  by case: (ex_minnP (@ex_intro _ (stab x) _ exstab)).
Qed.

Lemma minstab_exp y : x ^+ minstab ^+ y * x = x.
 elim: y => [|n IH].
  by rewrite GRing.expr0 GRing.mul1r.
 rewrite GRing.exprSr -GRing.mulrA.
 by case/andP: minstab_cond => /eqP -> _.
Qed.

Lemma minstab_dvd : forall y, stab x y -> (minstab %| y)%nat.
Proof.
move=> y.
rewrite /stab (divn_eq y minstab) addnC GRing.exprD mulnC GRing.exprM
 => /andP[] H3.
have H4: x ^+ minstab ^+ (y %/ minstab)%nat * x = x.
 by rewrite minstab_exp.
rewrite -GRing.mulrA H4 in H3.
case ym: (y %% minstab)%nat => *.
 by rewrite add0n dvdn_mulr.
have H5: stab x (y %% minstab)%N.
 by rewrite /stab H3 ym.
move: H5; rewrite /minstab.
case: (ex_minnP (@ex_intro _ (stab x) _ exstab)) => m /andP [] ?? H /H.
by rewrite leqNgt ltn_pmod.
Qed.

Lemma minstabE : minstab = (2 ^ m - 1)%nat.
Proof.
  case/primeP: pm => _ /(_ _ (minstab_dvd exstab))/orP [|/eqP []//].
  rewrite /minstab.
  case: (ex_minnP (@ex_intro _ (stab x) _ exstab)) => [][]//[]// /andP [].
  rewrite -exprSr => H3.
  by move/negP: H1; rewrite H3.
Qed.

Lemma minstab_attain :
forall l k : nat, x ^+ l * x = x ^+ k * x -> (k = l %[mod 2 ^ m - 1])%nat.
Proof.
move: minstabE => /eqP H3.
have base: forall l, (0 < l < 2 ^ m - 1)%N -> x ^+ l * x != x.
 move/eqP: H3 => H l /andP [] Hl0 Hl; apply/negP => /eqP C.
  move: H; rewrite /minstab.
  case: (ex_minnP (@ex_intro _ (stab x) _ exstab)) => m ? H5 H4.
  have/H5 : stab x l by rewrite /stab C Hl0 eqxx.
  by rewrite leqNgt H4 Hl.
have base1:
  forall l k, (l < 2 ^ m - 1 -> 0 < k < 2 ^ m - 1 ->
  (x ^+ l * x = x ^+ k * x)%R -> k = l)%N.
 move=> l k.
 case kl: (k == l %[mod (2 ^ m - 1)])%N.
  move: kl => + Hl1 /andP [] Hk1 Hk2.
  by rewrite !modn_small // => /eqP ->.
 move=> Hl Hk2.
 case kl': (k > l)%N.
  have: (0 < l + (2 ^ m - 1 - k) < 2 ^ m - 1)%N.
   apply/andP; split.
    rewrite lt0n addn_eq0; apply/negP => /andP [] /eqP l0 mk.
    move: l0 mk kl => ->.
    rewrite subn_eq0 leqNgt.
    by case/andP: Hk2 => ? ->.
   case/andP: Hk2 => ? Hk2.
   rewrite addnBA; last by apply ltnW.
   rewrite addnC -subnBA ?ltn_subr //; last by apply ltnW.
   case: (2 ^ m - 1)%nat Hk2 => // ??.
   by rewrite /leq subSS -subnDA addnC subnDA subSn // subnn subnBA
             ?add1n ?subn_eq0 // ltnW.
  move/base => + lk.
  rewrite addnC GRing.exprD -GRing.mulrA lk GRing.mulrA -GRing.exprD subnK.
   by rewrite ?subn1 -GRing.exprSr prednK // H2.
  by case/andP: Hk2 => ??; rewrite ltnW.
 move/negP/negP: kl'; rewrite -ltnNge ltnS leq_eqVlt => /orP [/eqP ->|] // kl'.
 have: (0 < k + (2 ^ m - 1 - l) < 2 ^ m - 1)%N.
  apply/andP; split.
   rewrite lt0n addn_eq0; apply/negP => /andP [] /eqP l0 mk.
   move: l0 mk kl => ->.
   by rewrite subn_eq0 leqNgt Hl.
  rewrite addnBA; last by apply ltnW.
  rewrite addnC -subnBA ?ltn_subr //; last by apply ltnW.
  case/andP: Hk2 => ? Hk2.
   case: (2 ^ m - 1)%nat Hk2 => // ??.
   by rewrite /leq subSS -subnDA addnC subnDA subSn // subnn subnBA
             ?add1n ?subn_eq0 // ltnW.
 move/base => + lk.
 rewrite addnC GRing.exprD -GRing.mulrA -lk GRing.mulrA -GRing.exprD subnK //.
  by rewrite subn1 -GRing.exprSr prednK // H2.
 by rewrite ltnW.
have base2:
  forall l k : nat, (0 < k < 2 ^ m - 1)%N ->
  x ^+ l * x = x ^+ k * x -> (k = l %% (2 ^ m - 1))%N.
  move=> l k /base1 b.
  rewrite [X in (_ ^+ X * _)%R](divn_eq l (2 ^ m - 1)) addnC GRing.exprD
          -GRing.mulrA mulnC exprM -(eqP H3) minstab_exp.
  apply/b.
  by rewrite minstabE ltn_pmod //.
move=> l k.
rewrite (divn_eq k (2 ^ m - 1)) addnC GRing.exprD -GRing.mulrA
        mulnC exprM -(eqP H3) minstab_exp addnC mulnC modnMDl.
case k0: (k %% minstab)%N.
 rewrite expr0 mul1r.
 case l0: (l %% minstab)%N; first by rewrite mod0n.
 rewrite (divn_eq l minstab) addnC exprD -mulrA mulnC exprM minstab_exp => /eqP C.
 move: (base (l %% minstab)%nat).
 by rewrite !minstabE ltn_pmod // -!minstabE l0 /= -l0 C => /implyP.
move/base2 => /=.
rewrite -k0 !minstabE ltn_pmod // -!minstabE => C.
by rewrite modn_mod C.
Qed.

Lemma map_pi_inj :
injective (fun (i : 'Z_(2 ^ m - 1)) => x ^+ i * x).
Proof.
  move=> y z /eqP.
  rewrite eqE /= => /eqP /minstab_attain.
  case: y => y yH.
  case: z => z zH.
  rewrite !modn_small //=.
  by move=> yx; apply/val_inj.
  apply: (leq_trans yH); by rewrite prednK.
  apply: (leq_trans zH); by rewrite prednK.
Qed.

Lemma map_pi_card :
#|image (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x) 'Z_(2 ^ m - 1)| = (2 ^ m - 1)%N.
Proof.
  have Hc : #|'Z_(2 ^ m - 1)| = (2 ^ m - 1)%nat.
   rewrite card_ord.
   by case: (2 ^ m - 1)%nat pm => [][].
  rewrite -[RHS]Hc.
  apply/eqP/image_injP => [][] y Hy1 [] z Hz1 _ _ /minstab_attain /esym H;
   apply/ord_inj.
  rewrite /= ?modn_small // in H.
  move: (Hy1) (Hz1) => ??.
  rewrite /= /Zp_trunc /= ?prednK // in Hy1, Hz1.
  rewrite /= /Zp_trunc /= ?prednK // in Hy1, Hz1.
Qed.

Lemma Xn_phi_neq0 (a : nat) : x ^+ a * x != 0.
Proof.
  move: minstab_attain => H0; apply/negP => /eqP Hc.
  move: (H0 a a.+1).
  rewrite GRing.exprS -GRing.mulrA Hc GRing.mulr0 => /(_ erefl)/eqP.
  rewrite (divn_eq a (2 ^ m - 1)) -addnS !modnMDl.
  by apply/negP/lem1 => //; rewrite ltn_mod.
Qed.

Lemma map_piE :
image (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x) 'Z_(2 ^ m - 1)
=i (finset [finComRingType of QphiI phi_gt1] :\ 0%R).
Proof.
 have H3: [seq x ^ i * x | i : 'Z_(2 ^ (size phi).-1 - 1)] \subset
          [set x | [finComRingType of QphiI phi_gt1] x] :\ 0.
  suff: codom (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x)
        \subset (finset [finComRingType of QphiI phi_gt1] :\ 0%R).
   by apply/subset_trans/subsetP/image_codom.
  apply/subsetP => y.
  rewrite codomE !inE /=.
  elim: (enum 'Z_(2 ^ m - 1)) => // a l IH.
  rewrite in_cons => /orP [/eqP ->|/IH -> //].
  by move: (Xn_phi_neq0 a) => ->.
 apply/subset_cardP => //.
 by rewrite !cardsDS /= ?sub1set ?inE // !cardsT !map_pi_card cards1 card_QphiI.
Qed.

Lemma map_piP q :
reflect (exists (r : 'Z_(2 ^ m - 1)), x ^ r * x = q)
(q \in (image (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x) 'Z_(2 ^ m - 1))).
Proof.
move: map_pi_inj => inj.
apply/(iffP idP).
* rewrite /image_mem.
  elim: (enum 'Z_(2 ^ m - 1)) => // a l IH.
  rewrite in_cons => /orP [/eqP ->|/IH //]; by exists a.
* case => q0 <-.
  set T := (fun (i : 'Z_(2 ^ (size phi).-1 - 1)) => x ^ i * x).
  set S := x ^ q0 * x.
  have->: S = T q0 by [].
  by rewrite mem_map // mem_enum.
Qed.

Lemma irreducibleP_direct : irreducible_poly phi.
Proof.
  split => // q q1 /dvdpP [] qq /eqP.
  case q0: (size q == 0)%nat.
   move/negPn.
   rewrite size_poly_eq0 in q0.
   by rewrite (eqP q0) mulr0 phi_neq0.
  case qq0: (size qq == 0)%nat.
   move/negPn.
   rewrite size_poly_eq0 in qq0.
   by rewrite (eqP qq0) mul0r phi_neq0.
  case qq1: (size qq == 1)%nat.
   case: qq qq0 qq1 => [][]// + []//=.
   case => [][|[]] //= i ?  _ _.
   set T := Polynomial _; have->: T = 1.
    apply/val_inj; rewrite /= polyseq1.
    congr (_ :: _); apply/val_inj.
    by rewrite /= modn_small //.
   rewrite mul1r => /eqP ->.
   by rewrite eqpxx.
  case x0: (x == 0).
   move/eqP: x0 H1 => ->.
   by rewrite -exprnP expr0n eqxx.
  move/eqP => pqq.
  have: \pi q \in (finset [finComRingType of QphiI phi_gt1] :\ 0%R).
   apply/setD1P; split.
    rewrite -pi_zeror -Quotient.idealrBE subr0 unfold_in rmodp_small.
     by rewrite -size_poly_eq0 q0.
    rewrite pqq size_mul ?(esym (size_poly_eq0 _)) ?qq0 ?q0 //.
    case: (size qq) qq0 qq1 => []//[]// *.
    by rewrite !addSn /= ltnS leq_addl.
   by rewrite inE.
  have: \pi qq \in (finset [finComRingType of QphiI phi_gt1] :\ 0%R).
   apply/setD1P; split.
    rewrite -pi_zeror -Quotient.idealrBE subr0 unfold_in rmodp_small.
     by rewrite -size_poly_eq0 qq0.
    rewrite pqq size_mul ?(esym (size_poly_eq0 _)) ?qq0 ?q0 //.
    case: (size q) q0 q1 => []//[]// *.
    by rewrite !addnS /= ltnS leq_addr.
   by rewrite inE.
  rewrite -!map_piE => /map_piP [] r rE /map_piP [] i iE.
  move: (f_equal (\pi : _ -> QphiI phi_gt1) pqq).
  rewrite pi_phi0 piM -rE -iE.
  case: r {rE} => /= r _; case: i {iE} => /= i _.
  rewrite -!exprSr -exprD addSn exprSr (divn_eq (r + i.+1) (2 ^ (size phi).-1 - 1))
          addnC exprD mulnC exprM -minstabE -mulrA minstab_exp minstabE => /esym C.
  have j: ((r + i.+1) %% (2 ^ (size phi).-1 - 1) < (Zp_trunc (2 ^ (size phi).-1 - 1)).+2)%nat
   by rewrite !prednK // (ltn_pmod (r + i.+1) predpower_gt0).
  have: (0 \in (image (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x) 'Z_(2 ^ m - 1)))
   by apply/map_piP; exists (Ordinal j).
  rewrite map_piE => /setD1P/andP.
  by rewrite eqxx.
Qed.
End Order.

Section Inverse.
(*
   This direction is trivial.
   Because the statement just says that the galois group is nontrivial.
*)
Variable ip : irreducible_poly phi.

Lemma piX_neq0 : \pi_(QphiI phi_gt1) 'X%R != 0%R.
Proof.
  by rewrite -pi_zeror -Quotient.idealrBE subr0 unfold_in
          rmodp_small ?size_polyX // -size_poly_eq0 size_polyX.
Qed.

Definition Xu: ((\pi 'X : QphiI_fieldType phi_gt1 ip) \is a GRing.unit)%R.
  by rewrite unitfE piX_neq0.
Defined.

Local Hint Resolve Xu : core.

Lemma piX2X : (\pi_(QphiI phi_gt1) ('X ^ 2) != \pi 'X)%R.
Proof.
  rewrite -Quotient.idealrBE unfold_in; apply/negP => /rdvdpP.
  rewrite phi_is_monic // => [][]// x.
  case x0: (x == 0).
   move/eqP: x0 => -> /eqP.
   rewrite mul0r subr_eq0 => /eqP/(f_equal (size : {poly 'F_2} -> _)).
   by rewrite size_polyXn size_polyX.
  case x1: (size x == 1)%nat.
   case: x x0 x1 => [][]// [][|[]//] i []// ???.
   set T := Polynomial _; have->: T = 1.
    apply/val_inj; rewrite /= polyseq1.
    congr (_ :: _); apply/val_inj.
    by rewrite /= modn_small //.
   rewrite mul1r => x2xp.
   move: x2xp ip => <- [] _ /(_ 'X).
   have->: 'X %| 'X ^ 2 - 'X.
    move=> t.
    by rewrite -exprnP exprS expr1 -[X in _ - X]mulr1 -mulrBr dvdp_mulr //.
   rewrite size_polyX /= => C.
   have/(f_equal (size : {poly 'F_2} -> _)): 'X = 'X ^ 2 - 'X :> {poly 'F_2}
    by apply/eqP; rewrite -f2eqp_eq C.
   by rewrite size_addl ?size_opp ?size_polyXn ?size_polyX.
  move/negP/negP: x0 => x0 /(f_equal (size : {poly 'F_2} -> _)).
  rewrite size_mul // size_addl ?size_polyXn ?size_opp ?size_polyX //.
  rewrite -size_poly_eq0 in x0.
  case: (size x) x0 x1 => []//[]// sx _ _.
  rewrite !addSn /= => [][] C.
  suff: (2 < 2)%nat by [].
  rewrite [X in (_ < X)%nat]C.
  by apply/leq_trans/leq_addl.
Qed.

Canonical QphiI_fieldType_ip := QphiI_fieldType phi_gt1 ip.
Definition piX := FinRing.unit [finFieldType of QphiI_fieldType_ip] Xu.

Lemma piX_order : #[piX]%g = (2 ^ m - 1)%nat.
Proof.
  have/cyclic.order_dvdG: piX \in
      [group of [set: {unit [finFieldType of QphiI_fieldType_ip]}]]
    by rewrite inE.
  rewrite card_finField_unit card_QphiI.
  case/primeP: pm => _.
  rewrite !subn1 => H /H {H} /orP [|/eqP] //.
  rewrite order_eq1 => /eqP piX1.
  move: piX2X.
  rewrite -exprnP exprS piM expr1 /=.
  set T := \pi 'X; have<-: val piX = T by [].
  by rewrite piX1 /= mul1r eqxx.
Qed.

Lemma val_piX_expE p : val (piX ^+ p)%g = \pi_(QphiI phi_gt1) ('X ^+ p)%R.
Proof.
  elim: p => [|p IHp]; first by rewrite expr0 pi1.
  by rewrite !GRing.exprS piM expgS /= IHp.
Qed.

Lemma X2mp_eq1 : (\pi_(QphiI_fieldType_ip) ('X ^+ (2 ^ m - 1)) = \pi 1)%R.
Proof.
  suff/(f_equal val): (piX ^+ (2 ^ m - 1))%g = 1%g.
   rewrite val_piX_expE /= => ->.
   by rewrite pi1.
  suff<-: #[piX]%g = (2 ^ m - 1)%nat by rewrite expg_order.
  by rewrite piX_order.
Qed.

Lemma XnE q :
  ('X ^ q %% phi == 'X %% phi) = (\pi_(QphiI phi_gt1) ('X ^ q) == \pi 'X)%R.
Proof.
  by rewrite -Quotient.idealrBE unfold_in rmodp_add //
             addr_eq0 -!Pdiv.IdomainMonic.modpE // modp_opp opprK.
Qed.

Lemma XnpE q :
  (q > 0)%nat ->
  (\pi_(QphiI phi_gt1) ('X ^ q.-1) == \pi 1)%R
  = (\pi_(QphiI phi_gt1) ('X ^ q) == \pi 'X)%R.
Proof.
  case: q => // q _; rewrite /= -!exprnP exprS piM.
  set T := _ == _.
  case Te: T.
   move/eqP: Te ->.
   set S := \pi 1; have->: S = 1 :> QphiI phi_gt1 by rewrite -pi_oner.
   by rewrite mulr1 eqxx.
  apply/negP; case: ifP => //.
  set S := \pi_(QphiI phi_gt1) 'X.
  rewrite -[X in _ == X](mulr1 (S : [ringType of QphiI phi_gt1]))
          => /eqP/(mulrI Xu)/eqP.
  by rewrite -pi_oner -/T Te.
Qed.

Lemma irreducibleP_inverse :
(('X ^ 2 %% phi != 'X %% phi) && ('X ^ (2 ^ m)%N %% phi == 'X %% phi))%R.
Proof.
rewrite !XnE piX2X /=.
have->: (2 ^ m = (2 ^ m - 1).+1)%nat by rewrite subn1 prednK.
by rewrite -exprnP exprS piM X2mp_eq1 pi1 mulr1.
Qed.

Lemma char2_phi : 2 \in [char QphiI phi_gt1]%R.
Proof.
by apply/(GRing.rmorph_char
         (pi_rmorphism (Quotient.rquot_ringQuotType (keyd_phiI phi))))
        /(GRing.rmorph_char (polyC_rmorphism [ringType of 'F_2])).
Qed.

Definition F :
  [lmodType 'F_2 of QphiI phi_gt1] -> [lmodType 'F_2 of QphiI phi_gt1]
  := Frobenius_aut char2_phi.

Lemma linearF : linear F.
Proof.
move=> a x y.
case: a => [][|[]//] i; set T := Ordinal i.
 have->: T = 0%R by apply/val_inj.
 by rewrite !GRing.scale0r !GRing.add0r.
have->: T = 1%R by apply/val_inj.
by rewrite !GRing.scale1r /F GRing.Frobenius_autD_comm // /GRing.comm GRing.mulrC.
Qed.

Canonical linearType_F := Eval hnf in Linear linearF.

Lemma linearQphiI_rV : linear (@QphiI_rV _ phi_gt1).
Proof.
  move=> a x y.
  by rewrite QphiI_rV_D QphiI_rV_scaler.
Qed.

Canonical linearType_QphiI_rV := Eval hnf in Linear linearQphiI_rV.

Lemma linearrVQphiI : linear (@rVQphiI _ phi_gt1).
Proof. apply (can2_linear (@QphiI_rV_K _ _) (@rVQphiIK _ _)). Qed.

Canonical linearType_rVQphiI := Eval hnf in Linear linearrVQphiI.

Lemma expXpE p x : iter p F x = (x ^+ (2 ^ p))%R.
Proof.
  elim: p x => [x|p IH x].
   by rewrite /= expn0 GRing.expr1.
  by rewrite iterS IH /F GRing.Frobenius_autE
             !GRing.exprS GRing.expr0 GRing.mulr1
             -GRing.exprD addnn expnS mul2n.
Qed.

Lemma expandF q :
  reflect (iter q F =1 id) ('X^(2 ^ q) %% phi == 'X %% phi)%R.
Proof.
pose rmorphX :=
    (rmorphX (pi_rmorphism (Quotient.rquot_ringQuotType (keyd_phiI phi)))).
rewrite exprnP XnE rmorphX.
apply/(iffP idP) => [/eqP H0 x|/(_ (\pi 'X))].
* rewrite (coord_basis (QphiIX_full _) (memvf x)).
  rewrite linear_sum; apply/eq_big => // i _.
  set e0 := QphiIX _.
  by rewrite linearZ_LR /= expXpE !QphiIXE rmorphX -exprM mulnC exprM H0.
* by rewrite expXpE => ->.
Qed.

Lemma cycleF_dvdP p :
  reflect (iter p F =1 id) (2 ^ m - 1 %| 2 ^ p - 1)%nat.
Proof.
pose rmorphX :=
  (rmorphX (pi_rmorphism (Quotient.rquot_ringQuotType (keyd_phiI phi)))).
case/andP: irreducibleP_inverse => _ H0.
apply/(iffP idP).
* case/dvdnP => q H1.
  rewrite XnE -XnpE // in H0.
  apply/expandF.
  rewrite exprnP XnE -XnpE; last first.
   elim: p {H1} => // n IH.
   apply/(leq_trans IH).
   by rewrite -[(2 ^ n)%nat]mul1n expnS leq_mul2r orbT.
  by rewrite -subn1 H1 mulnC -exprnP exprM rmorphX !subn1 /= (eqP H0) pi1 expr1n.
* move/(_ (\pi 'X)).
  rewrite XnE in H0.
  rewrite expXpE -rmorphX /= -(eqP H0) -!val_piX_expE => /val_inj/eqP.
  rewrite cyclic.eq_expg_mod_order piX_order.
  have H2: (2 ^ (size phi).-1 = ((2 ^ (size phi).-1) - 1) + 1)%nat
   by rewrite addn1 subn1 prednK.
  have H3: (1 = 0 + 1)%nat by rewrite add0n.
  case p0: (p > 0)%nat; last first.
   rewrite lt0n in p0.
   by move/negP/negP/eqP: p0 ->.
  have H4: ((2 ^ p) = ((2 ^ p) - 1) + 1)%nat.
   rewrite subn1 addn1 prednK //.
   elim: p p0 => // [][] // p IH _.
   have->: (0 = 2 * 0)%nat by [].
   by rewrite expnS ltn_mul2l /= muln0 IH.
  by rewrite [X in (_ == X %[mod _])%nat]H2 modnDl [X in (_ == X %[mod _])%nat]H3
             [X in (X == _ %[mod _])%nat]H4 eqn_modDr mod0n.
Qed.

Lemma cycleF_dvdP' p :
  (0 < p)%nat ->
  reflect ((\pi 'X : QphiI phi_gt1) ^+ p = \pi 'X)
          (2 ^ m - 1 %| p - 1)%nat.
Proof.
move=> p1; case/andP: irreducibleP_inverse => _ H0.
apply/(iffP idP).
* case/dvdnP => q H1.
  move/expandF/(_ (\pi 'X)) : H0 => H0.
  case q0: (q == 0)%nat.
   move/eqP: q0 H1 => ->.
   by case: p p1 => []//[]//.
  suff/(f_equal (fun y => (\pi 'X : QphiI phi_gt1) * y)):
     (\pi 'X : QphiI phi_gt1) ^+ (p - 1) = 1
   by rewrite -exprS mulr1 subn1 prednK.
  rewrite H1 mulnC mulnBl mul1n (expfB (\pi 'X : QphiI_fieldType phi_gt1 ip))
          ?ltn_Pmull ?lt0n ?q0 //.
  rewrite expXpE in H0.
  by rewrite exprM H0 divff // expf_neq0 // x0.
* rewrite XnE in H0.
  rewrite -(eqP H0) -rmorphX -exprM -!exprnP /= -!val_piX_expE => /val_inj/eqP.
  rewrite cyclic.eq_expg_mod_order piX_order.
  have H2: (2 ^ (size phi).-1 = ((2 ^ (size phi).-1) - 1) + 1)%nat
   by rewrite addn1 subn1 prednK.
  case p0: (p > 0)%nat; last first.
   rewrite lt0n in p0.
   by move/negP/negP/eqP: p0 ->.
  have H3: (p - 1 + 1 = p)%nat by rewrite subn1 addn1 prednK.
  by rewrite [X in (_ == X %[mod _])%nat]H2 modnDl
            -[X in (_ == X %[mod _])%nat]add0n
             [X in (X * _ == _ %[mod _])%nat]H2 mulnDl mulnC modnMDl mul1n -H3
             eqn_modDr H3 mod0n.
Qed.
End Inverse.

Lemma irreducibleP :
reflect (irreducible_poly phi)
(('X ^ 2 %% phi != 'X %% phi) && ('X ^ (2 ^ m)%N %% phi == 'X %% phi))%R.
Proof.
pose rmorphX :=
  (rmorphX (pi_rmorphism (Quotient.rquot_ringQuotType (keyd_phiI phi)))).
apply/(iffP idP); last by apply irreducibleP_inverse.
case/andP; rewrite !XnE -!exprnP !rmorphX.
by apply irreducibleP_direct.
Qed.

Lemma irreducibleP1 :
  reflect (irreducible_poly phi)
  [exists x, (F x != x) && (iter (size phi).-1 F x == x)%R].
Proof.
pose rmorphX :=
  (rmorphX (pi_rmorphism (Quotient.rquot_ringQuotType (keyd_phiI phi)))).
apply/(iffP idP).
* case/existsP => x /andP [] H1 H2.
  apply (irreducibleP_direct H1).
  by rewrite expXpE in H2.
* case/irreducibleP/andP.
  rewrite !XnE => H1 H2; apply/existsP; exists (\pi_(QphiI phi_gt1) 'X).
  apply/andP; split.
   rewrite //= /F Frobenius_autE.
   move: H1; apply/contra.
   by rewrite rmorphX.
  rewrite -!exprnP !rmorphX -!expXpE in H2.
  by rewrite (eqP H2).
Qed.

Lemma irreducibleP2 x :
  F x != x ->
  reflect (irreducible_poly phi) (iter (size phi).-1 F x == x)%R.
Proof.
move=> Hxx.
apply/(iffP idP) => [iHxx|].
* apply/irreducibleP1/existsP.
  by exists x; rewrite Hxx iHxx.
* by case/irreducibleP/andP => ? /expandF ->.
Qed.
End Irreducible.

Require Import Coq.Logic.FunctionalExtensionality
        Eqdep_dec Coq.Logic.ClassicalFacts Coq.Arith.Wf_nat.

Axiom pi : proof_irrelevance.
Axiom em : excluded_middle.

Section Infinite.
Variable phi : {poly 'F_2}.
Variable pm : prime (2 ^ (size phi).-1 - 1).
Local Open Scope ring_scope.
Local Open Scope quotient_scope.
Import GRing.Theory.

Lemma polyF2_char2 : 2 \in [char {poly 'F_2}].
Proof. by apply (GRing.rmorph_char (polyC_rmorphism _)). Qed.

Hint Resolve polyF2_char2 : core.

Definition S := nat -> 'F_2.

Local Definition add (f g : S) := fun i => f i + g i.
Local Definition zero : S := fun i => 0.

Fixpoint subst_rec (s : seq 'F_2) x : S -> S :=
  if s is a :: s'
  then fun (b : S) => add ((subst_rec s' x \o x) b)
                       (if a == 1 then b else zero)
  else fun=> zero.
Definition subst p := subst_rec p.

(* Local Fixpoint subst p D : S -> S := *)
(*   match p with *)
(*   | [::] => fun _ => zero *)
(*   | a :: q => *)
(*     if a == (1 : 'F_2) *)
(*     then fun (b : S) => add (iter (size q) D b) (subst q D b) *)
(*     else subst q D *)
(*   end. *)

Lemma addC : commutative add.
Proof.
  move=> f g.
  apply/functional_extensionality => i.
  by rewrite /add addrC.
Qed.

Lemma addA : associative add.
Proof.
  move=> f g h.
  apply/functional_extensionality => i.
  by rewrite /add addrA.
Qed.

Lemma add0p h : add zero h = h.
Proof.
  apply/functional_extensionality => i.
  by rewrite /add add0r.
Qed.

Lemma addp0 h : add h zero = h.
Proof. by rewrite addC add0p. Qed.

Lemma addpp p : add p p = zero.
Proof.
  apply functional_extensionality => j.
  by rewrite /add addrr_char2.
Qed.

Lemma iterD D :
  (forall a b, D (add a b) = add (D a) (D b)) ->
  forall n a b, (iter n D) (add a b) = add (iter n D a) (iter n D b).
Proof.
  move=> H.
  elim => // n IH a b.
  by rewrite /= IH H.
Qed.

Lemma substD phi' D a b :
  (forall a b, D (add a b) = add (D a) (D b)) ->
  subst phi' D (add a b) = add (subst phi' D a) (subst phi' D b).
Proof.
  move=> H.
  elim: phi' a b => /=[*|c phi' IH a b].
   apply/functional_extensionality => i.
   by rewrite /add /zero addr0.
  rewrite H IH -!addA; congr add.
  case: (c == 1).
   by rewrite addC -addA [X in add _ X]addC.
  by rewrite !add0p !addp0.
Qed.

Lemma substX D a : subst 'X D a = D a.
Proof. by rewrite polyseqX /= !add0p !addp0. Qed.

Definition D (f : S) := fun i => f i.+1.

Definition V := { x : S | subst phi D x = zero }.

Lemma eqV f g H I :
  f = g ->
  exist (fun x : S => subst phi D x = zero) f H
= exist (fun x : S => subst phi D x = zero) g I.
Proof.
  move=> K; move: H I; rewrite K => H I.
  rewrite (eq_proofs_unicity _ H I) // => x y.
  by apply em.
Qed.

Local Definition addv (a b : V) : V.
exists (add (proj1_sig a) (proj1_sig b)).
apply functional_extensionality => i.
case: a => a Ha; case: b => b Hb.
by rewrite substD //= Ha Hb /add add0r.
Defined.

Local Definition zerov : V.
exists (fun _ => 0).
apply functional_extensionality => i.
elim: (polyseq phi) => //= a l.
case: (a == 1); by rewrite /add /zero => ->; rewrite addr0.
Defined.

Lemma addvA : associative addv.
Proof.
  case => []f fH []g gH []h hH.
  rewrite /addv /= (eqV _ _ (addA _ _ _)).
   by rewrite !substD // hH fH gH ?add0p.
  move=> ?; by apply eqV.
Qed.

Lemma addvC : commutative addv.
Proof.
  case => []f fH []g gH.
  by apply eqV, addC.
Qed.

Lemma add0v : left_id zerov addv.
Proof.
  case=> x xH.
  apply eqV, functional_extensionality => i.
  by rewrite /add add0r.
Qed.

Lemma addIv : left_inverse zerov id addv.
Proof.
  case=> x xH.
  apply eqV, functional_extensionality => i.
  by rewrite /add /= addrr_char2.
Qed.

Definition t (f : S) := f 0%nat.

Definition pairing (g: QphiI (phi_gt1 pm)) (x : V) : 'F_2 :=
  t (subst (generic_quotient.repr g) D (sval x)).

Definition H (f : S) : S := fun i => f i.*2.

Lemma DHC x : subst phi D (H x) = H (subst phi (D \o D) x).
Proof.
  elim: (polyseq phi) x => //= a l IH x.
  have DH: forall x, D (H x) = H ((D \o D) x).
   move=> y.
   apply functional_extensionality => j.
   by rewrite /D /H doubleS.
  by case: (a == 1); rewrite DH IH; apply functional_extensionality.
Qed.

Lemma substC j l :
  subst l D (D j) = (D \o subst l D) j.
Proof.
   elim: l j => //= b l IH j.
   apply functional_extensionality => x.
   by case: ifP; rewrite IH.
Qed.

Lemma phiD2 : subst phi (D \o D) = subst phi D \o subst phi D.
Proof.
  elim: (polyseq phi) => //= a l IH.
  apply functional_extensionality => j.
  case: (a == 1).
   rewrite /= !substD // IH -!addA [add _ (add _ j)]addA addpp add0p.
   congr add.
   apply functional_extensionality => x.
   congr subst.
   apply functional_extensionality => i.
   elim: l {IH} j => //= b l IH j.
   case: ifP; by rewrite addC /add IH addrC.
  by rewrite /= !addp0 IH /= !substC.
Qed.

Lemma subst0 p D :
  D zero = zero ->
  subst p D zero = zero.
Proof.
  move=> D00.
  elim: p => //= a p IH.
  by case: (a == 1); rewrite D00 {}IH add0p.
Qed.

Lemma substDMXC (p : {poly 'F_2}) c D a :
  subst (p * 'X + c%:P) D a =
  add ((subst p D \o D) a) (subst c%:P D a).
Proof.
  rewrite -cons_poly_def polyseq_cons.
  case: ifP => /= H; last first.
   case: (polyseq p) H => // _.
   apply/functional_extensionality => i.
   by rewrite /add /= add0r.
  case: ifP => c1.
   by rewrite (eqP c1) polyseqC /= add0p.
  case: c c1 => [][|[]//] /= c c1.
  by rewrite polyseqC.
Qed.

Lemma substMX p x : subst (p * 'X) x = subst p x \o x.
Proof.
  rewrite -[p * 'X]addr0.
  have->: 0 = (0 : 'F_2)%:P by rewrite polyC0.
  apply functional_extensionality => ?.
  by rewrite substDMXC !polyC0 polyseq0 /= addp0.
Qed.

Lemma subst_poly s x : subst (Poly s) x = subst_rec s x.
Proof.
  elim: s => [|a s IH].
   by rewrite polyseqC.
  rewrite /= cons_poly_def.
  apply functional_extensionality => ?.
  by case: a => [][|[]//] /= i; rewrite substDMXC !polyseqC /= IH ?add0p.
Qed.

Lemma subst_rcons s a D x :
  subst_rec (rcons s a) D x =
  add (if a == 1 then iter (size s) D x else zero) (subst_rec s D x).
Proof.
  elim: s a D x => [*| b s IH a D x].
   by rewrite addC.
  rewrite /= IH.
  case: ifP; first by case: ifP; rewrite -!iterS iterSr !addA.
  by rewrite !add0p.
Qed.

Lemma substD' (p r : {poly 'F_2}) a :
  subst (p + r) D a = add (subst p D a) (subst r D a).
Proof.
  rewrite /GRing.add /= /add_poly
          unlock /add_poly_def /poly
          unlock subst_poly.
  move mnE : (maxn (size p) (size r)) => mn.
  elim: (lt_wf mn) p r a mnE => {mn} [][_ _ p r a /eqP|mn _ IH p r a mnE].
   rewrite maxnE addn_eq0 => /andP [] p0.
   rewrite (eqP p0) subn0; move: p0.
   rewrite !size_poly_eq0 => /eqP -> /eqP ->.
   by rewrite !polyseq0 /= add0p.
  move: r a p mnE.
  apply: (@poly_ind _ (fun (r : {poly 'F_2})=> forall a (p : {poly 'F_2}), maxn (size p) (size r) = mn.+1 -> _)).
   move=> ? p.
   rewrite size_poly0 maxn0 => <-.
   have->: (fun i : nat => p`_i + (0: {poly 'F_2})`_i) = fun i => p`_i.
    apply/functional_extensionality => ?.
    by rewrite coef0 addr0.
   case p0: (size p == 0%nat).
    rewrite size_poly_eq0 in p0.
    by rewrite (eqP p0) !polyseq0 /= addp0.
   rewrite polyseq0 /= addp0 -polyseq_poly ?coefK //.
   case: p p0 => /= p + p0.
   by rewrite (last_nth 0%R) -[size p]prednK // lt0n p0.
  move=> p c _ a r H'.
  set P := p * _ + _.
  rewrite /mkseq.
  have->: (mn.+1 = mn + 1)%nat by rewrite -addn1.
  rewrite addnC iota_add add0n map_cat.
  have->: [seq r`_i + P`_i | i <- iota 1 mn]
      = mkseq (fun i : nat => r`_i.+1 + p`_i) mn.
   apply (@eq_from_nth _ 0).
    by rewrite size_map size_iota size_mkseq.
   move=> i H.
   have ?: (i < mn)%nat.
    move: H.
    by rewrite size_map size_iota.
   by rewrite (nth_map 0%nat 0) ?size_iota // !nth_iota // !add1n
              /P -cons_poly_def coef_cons nth_mkseq.
  rewrite cat1s /P -cons_poly_def coef_cons eqxx.
  subst P; move: r a c p H'.
  apply: (@poly_ind _ (fun (r : {poly 'F_2})=> forall a c (p : {poly 'F_2}), maxn (size r) _ = mn.+1 -> _)).
   move=> ? c p.
   rewrite size_poly0 max0n -cons_poly_def size_cons_poly coef0 add0r polyseq0 /= add0p.
   have->: (fun i : nat => (0: 'F_2) + p`_i) = fun i => p`_i.
    apply/functional_extensionality => ?.
    by rewrite add0r.
   case: ifP => // n [] <-.
   case p0: (size p == 0%nat).
    rewrite size_poly_eq0 in p0; move: n.
    rewrite (eqP p0) !polyseq0 /= add0p.
    case: c => [][|[]//] // *.
    by rewrite /= polyseq_cons polyseq0 /= polyseqC /= add0p.
   rewrite -polyseq_poly ?coefK // ?polyseq_cons.
    by case: (polyseq p) p0.
   case: p p0 n => /= p + p0.
   by rewrite (last_nth 0%R) -[size p]prednK // lt0n p0.
  move=> p c _ a b r H'.
  rewrite -!cons_poly_def coef_cons eqxx.
  have->: (fun i : nat => (cons_poly c p)`_i.+1 + r`_i)
        = (fun i : nat => p`_i + r`_i).
   apply/functional_extensionality => ?.
   rewrite polyseq_cons /=.
   case: (polyseq p) => //=.
   rewrite polyseqC /=.
   case: c {H'} => [][|[]//] //= c.
   by rewrite nth_nil !add0r.
  rewrite /= IH //; last first.
   move: H'.
   rewrite -!cons_poly_def !size_cons_poly.
   case: ifP; case: ifP => //.
   + rewrite max0n => ? /andP [] p0 ? [] <-.
     case: (polyseq p) p0 => //=.
     by rewrite max0n.
   + rewrite maxn0 => /andP [] r0 ? ? [] <-.
     by case: (polyseq r) r0.
   + by move=> ?? /eqP; rewrite maxnSS eqSS => /eqP.
  rewrite !cons_poly_def !substDMXC -!addA.
  congr add.
  rewrite [in RHS]addC -!addA.
  congr add.
  rewrite !polyseqC.
  case: c {H'} => [][|[]//]; case: b => [][|[]//] /= c b;
  by rewrite ?(addp0, add0p, addpp).
Qed.

Lemma substM (p q : {poly 'F_2}) a :
  subst (p * q) D a = (subst p D \o subst q D) a.
Proof.
  elim/poly_ind: p a => [?|p c IH a].
   by rewrite mul0r !polyseq0.
  rewrite mulrDl substD' mulrC mulrA substMX /comp mulrC IH.
  case: c => [][|[]//] c.
   have->: Ordinal c = 0 by apply/val_inj.
   by rewrite polyC0 mul0r addr0 substMX polyseq0 /= addp0 substC.
  have->: Ordinal c = 1 by apply/val_inj.
  by rewrite substDMXC polyC1 mul1r polyseq1 /= add0p substC.
Qed.

Lemma substMXn n x : subst 'X^n x = \big[comp/id]_(i < n) subst 'X x.
Proof.
  elim: n x => [x|n IH x].
   rewrite big_ord0 expr0 polyseqC.
   apply/functional_extensionality => ?.
   by rewrite /= add0p.
  rewrite exprSr substMX IH big_ord_recl.
  elim: n {IH} => [|n IH].
   rewrite big_ord0; apply/functional_extensionality => ?.
   by rewrite /= polyseqX /= addp0 add0p.
  by rewrite big_ord_recl -[in RHS]IH.
Qed.

Definition H' : V -> V.
case => x Hx; exists (H x).
rewrite DHC phiD2 /comp Hx subst0 //.
Defined.

Lemma subst_subst x y f :
  subst phi D f = zero ->
  x = y %[mod QphiI (phi_gt1 pm)] -> subst y D f = subst x D f.
Proof.
move => Hf /eqP.
rewrite -Quotient.idealrBE unfold_in Pdiv.RingMonic.rmodp_add
        ?f2p_monic ?phi_neq0 ?phi_gt1 // addr_eq0
        -!Pdiv.IdomainMonic.modpE ?f2p_monic ?phi_neq0 ?phi_gt1 //
        modp_opp opprK => /eqP H.
by rewrite (divp_eq x phi) (divp_eq y phi) H !substD' !substM /comp ?Hf
           // !subst0.
Qed.

Lemma exprsumn_char2 (R : comRingType) s (f : 'I_s -> R) :
  2 \in [char R] ->
  (\sum_(i < s) f i) ^+ 2 = \sum_(i < s) (f i ^+ 2).
Proof.
  move=> H; elim: s f => [f |s IH f]; first by rewrite !big_ord0 expr0n.
  rewrite !big_ord_recl exprDn_comm; last by rewrite /GRing.comm mulrC.
  by rewrite !big_ord_recl !subn0 !subn1 !subnn !expr0
             !expr1 !big_ord0 !mulr1 !mul1r !addr0
             /= /bump /= !addn0 !addn1 (IH (fun i => f (lift ord0 i)))
             binn bin1 mulr1n /= mulr2n addrr_char2 // add0r.
Qed.

Lemma subst_sum s (f : 'I_s -> {poly 'F_2}) x :
  subst (\sum_(i < s) f i) D x = \big[add/zero]_(i < s) subst (f i) D x.
Proof.
  elim: s f => [|s IH] f; first by rewrite !big_ord0 polyseq0.
  by rewrite !big_ord_recl substD' IH.
Qed.

Lemma t_sum s (f : 'I_s -> S) :
  t (\big[add/zero]_(i < s) f i) = \sum_(i < s) t (f i).
Proof.
  elim: s f => [|s IH] f; first by rewrite !big_ord0.
  by rewrite !big_ord_recl -IH.
Qed.

Lemma pairing_adj f x : pairing (@irreducible.F _ pm x) f = pairing x (H' f).
Proof.
  have->: (@irreducible.F _ pm x) = iter 1 (@irreducible.F _ pm) x by [].
  rewrite expXpE /pairing expn1 (coord_basis (QphiIX_full _) (memvf x)).
  under eq_bigr => j _.
   rewrite (nth_map j) ?size_enum_ord // nth_enum_ord // -linearZ_LR.
  over.
  rewrite -linear_sum -rmorphX exprsumn_char2 //=.
  case: piP => y yE; case: piP => z zE; case: f => f fH /=.
  rewrite (subst_subst _ yE) // (subst_subst _ zE); last first.
   by rewrite DHC phiD2 /comp fH subst0.
  rewrite !subst_sum !t_sum; apply/eq_bigr => i _.
  case: (coord (QphiIX (phi_gt1 pm)) i x) => [][|[]//] i0.
   have ->: Ordinal i0 = 0 by apply/val_inj.
   by rewrite !scale0r expr0n !polyseqC.
  have ->: Ordinal i0 = 1 by apply/val_inj.
  rewrite !scale1r -exprM muln2.
  case: i => i /= _; elim: i f fH => [??|i IH f fH].
   by rewrite expr0 polyseqC /= !add0p.
  rewrite doubleS !exprSr !substM /= substM /= IH.
   congr t; congr subst.
   move: (substM 'X 'X) => /= <-.
   by rewrite -expr2 polyseqXn polyseqX /= !addp0 !add0p.
  repeat move: substM => /= <-.
  by rewrite mulrC mulrA mulrC mulrA substM /= fH subst0.
Qed.

Check H'.

Fixpoint add x y :=
  match x, y with
  | a :: x, b :: y =>
    xorb a b :: add x y
  | [::], _ => y
  | _, [::] => x
  end.

Fixpoint mul x y :=
  match x with
  | [::] => [::]
  | a :: x =>
    if a == false then false :: mul x y
    else add (false :: mul x y) y
  end.

(*
Definition rV_seq (x : 'rV['F_2]_(size phi).-1) :=
  mktuple (fun y => x ord0 y).
*)

Fixpoint one n :=
  match n with
  | 0 => [:: true]
  | n.+1 => false :: one n
  end.

(*
Fixpoint div (x y : seq 'F_2) : seq 'F_2 :=
  if (size x < size y)%nat then x
  else add (one (size x - size y))
           (div (add x (mul (one (size x - size y)) y)) y).
*)

Fixpoint truncate x :=
  match x with
  | [::] => [::]
  | a :: x =>
    if a == false then
      let tx := truncate x in
      if tx == [::] then [::] else false :: tx
    else true :: truncate x
  end.

Definition div_rec q :=
  let sq := size q in
   fix loop (k : nat) (qq r : seq bool) (n : nat) {struct n} :=
    let str := size (truncate r) in
    if (str < sq)%nat then (k, qq, r) else
    let m := one (str - sq) in
    let qq1 := add m qq in
    let r1 := add r (mul m q) in
       if n is n1.+1 then loop k.+1 qq1 r1 n1 else (k.+1, qq1, r1).

Definition div_expanded_def p q :=
  let tp := truncate p in
  let tq := truncate q in
  if size tq == 0%N then (0%N, [::], tp) else div_rec tq 0 [::] tp (size tp).

Definition div p q := ((div_expanded_def p q).1).2.
Definition mod p q := (div_expanded_def p q).2.

Definition f x := mul x x.

Compute iter 19937 f [:: false; true].

Require Import nat_word.
Compute mul [:: false; true] [:: false; true].
Compute mul (mul [:: false; true] [:: false; true]) (mul [:: false; true] [:: false; true]).
Check pm.
Compute one (2^19937 - 1).

2 ^ (size phi).-1 - 1
Compute mul [:: false; true].
Time Compute truncate (mod (mul (rep 19937 true) (rep 19937 true)) [:: true; false; true; false]).
(* Finished transaction in 186.546 secs (186.347u,0.s) (successful) *)

Compute truncate (mod (rep 19937 true) [:: true; false; true; false]).

Compute truncate (mul [:: 0; 1; 0; 1] [:: 1; 1]) == [:: 0; 1; 1; 1; 1].
Compute truncate (mul [:: 1; 1] [:: 0; 1; 0; 1]) == [:: 0; 1; 1; 1; 1].
Compute mul [:: 0; 1] [:: 0; 1] == [:: 0; 0; 1].
Compute truncate (div [:: 0; 1; 1; 1] [:: 0; 1]) == [:: 1; 1; 1].
Compute truncate (div [:: 0; 1; 1] [:: 0; 1]) == [:: 1; 1].
Compute truncate (add [:: 1] [:: 1]) == [::].
Compute truncate (mod [:: 0; 1; 1] [:: 0; 1]) == [::].
Compute truncate (div [:: 0; 1] [:: 0; 1]) == [:: 1].

Time Compute (rep 19937 (1 : 'F_2)).
(* Finished transaction in 2.465 secs (1.615u,0.s) (successful) *)
Time Compute (rep 19937 true).
(* Finished transaction in 0.138 secs (0.109u,0.s) (successful) *)
Print mul.
Check add (iota (fun _ => 0) 19937) (iota (fun _ => 0) 19937).

Definition H' x := mod (mul x x) phi.
Compute H' [:: 0; 1].
End Infinite.
End Infinite.
