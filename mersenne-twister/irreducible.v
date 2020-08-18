From mathcomp
Require Import all_ssreflect all_algebra all_field all_fingroup.
From Coq.Logic
Require FunctionalExtensionality.

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

(* Definition H := (@QphiI_rV _ _) \o F \o (@rVQphiI _ _). *)

(* Lemma iterHE s : *)
(*    iter s H =1 (@QphiI_rV _ _) \o iter s F \o (@rVQphiI _ _). *)
(* Proof. *)
(*   elim: s => [?|s IH x]. *)
(*    by rewrite /= rVQphiIK. *)
(*   by rewrite iterS IH /H /= QphiI_rV_K. *)
(* Qed. *)

Lemma irreducibleP1 :
  reflect (irreducible_poly phi)
  [exists x, (F x != x) && (iter (size phi).-1 F x == x)%R].
Proof.
pose rmorphX :=
  (rmorphX (pi_rmorphism (Quotient.rquot_ringQuotType (keyd_phiI phi)))).
apply/(iffP idP).
* case/existsP => x /andP [] H1 H2.
  rewrite expXpE in H2.
  rewrite /F Frobenius_autE in H1.
  by apply (irreducibleP_direct H1 H2).
* case/irreducibleP/andP.
  rewrite !XnE => H1 H2; apply/existsP; exists (\pi_(QphiI phi_gt1) 'X).
  apply/andP; split.
   rewrite /= /F Frobenius_autE.
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
* by case/irreducibleP/andP => ? /expandF/(_ x) ->.
Qed.

Section InversiveDecimation.
Variable f : {linear QphiI phi_gt1 -> QphiI phi_gt1}.
Variable b : {linear QphiI phi_gt1 ->
              (primeChar_lmodType (erefl : 2 \in [char 'F_2]))}.
Definition Phi S := \row_(j < (size phi).-1) (b \o iter j f) S.
Variable Phi_inv : 'rV['F_2]_(size phi).-1 ->  QphiI phi_gt1.
Hypothesis PhiK : cancel Phi_inv Phi.
Hypothesis Phi_invK : cancel Phi Phi_inv.

Lemma linearPhi : linear Phi.
Proof.
move=> a x y.
case: a => [][|[]//] i; set T := Ordinal i.
 have->: T = 0%R by apply/val_inj.
 by rewrite !GRing.scale0r !GRing.add0r.
have->: T = 1%R by apply/val_inj.
rewrite !GRing.scale1r /Phi.
Admitted.

Canonical linearType_Phi := Eval hnf in Linear linearPhi.

Definition Phi_long S := \row_(j < (size phi).-1.*2) (b \o iter j f) S.
Definition double_ord_prf (j : 'I_(size phi).-1) : (j.*2 < (size phi).-1.*2)%nat.
Proof.
  case: j => j H.
  rewrite -!addnn /=.
  apply/leq_trans.
   apply: (_ : _ < j + (size phi).-1)%nat.
   by rewrite ltn_add2l.
  by rewrite leq_add2r ltnW.
Qed.

Definition H (x : 'rV['F_2]_((size phi).-1).*2) :=
  \row_(j < (size phi).-1) x ord0 (Ordinal (double_ord_prf j)).

Definition pairing (x : QphiI phi_gt1) (y : 'rV['F_2]_(size phi).-1) : 'F_2 :=
  ((@QphiI_rV _ _) x *m y^T) ord0 ord0.

Lemma sum_f2_eq0 q (P : pred 'I_q) :
\big[GRing.add_comoid [ringType of 'F_2]/0]_(i0 | P i0) 0 = 0.
Proof.
rewrite big_const; set T := #|_|.
elim: T => // t IHt.
by rewrite iterS IHt /= GRing.addr0.
Qed.

Lemma pairing_nondeg x : (forall y, pairing x y = 0) -> x = 0.
Proof.
  move=> H; apply/(can_inj (@QphiI_rV_K _ _)).
  apply/rowP => j.
  move: H; rewrite /pairing => /(_ (delta_mx ord0 j)).
  rewrite mxE.
  under eq_bigr => k _.
   rewrite ![(delta_mx _ _)^T _ _]mxE ![delta_mx _ _ _ _]mxE.
  over.
  rewrite (bigD1 j) //= eqxx mulr1.
  under eq_bigr => k /negPf K.
   rewrite K mulr0.
  over.
  rewrite sum_f2_eq0 addr0 => ->.
  by rewrite linear0 mxE.
Qed.

Lemma pairing_nondeg' y : (forall x, pairing x y = 0) -> y = 0.
Proof.
  move=> H; apply/rowP => j.
  move: {H} (H (rVQphiI _ (delta_mx ord0 j))).
  rewrite /pairing rVQphiIK 2!mxE.
  under eq_bigr => k _.
   rewrite ![delta_mx _ _ _ _]mxE.
  over.
  rewrite (bigD1 j) //= eqxx mul1r.
  under eq_bigr => k /negPf K.
   rewrite K mul0r.
  over.
  by rewrite mxE sum_f2_eq0 addr0 => ->.
Qed.

Lemma adjFH x y :
pairing ((F \o (@rVQphiI _ _) \o Phi) x) y
= pairing x ((H \o Phi_long \o (@rVQphiI _ _)) y).
Proof.
  rewrite /pairing !mxE; apply/eq_bigr => i _.
  rewrite (coord_basis (QphiIX_full _) (memvf x)) linear_sum.
  rewrite !linear_sum !mxE.
  set e0 := QphiIX _.
  by rewrite linearZ_LR /= expXpE !QphiIXE rmorphX -exprM mulnC exprM H0.
* by rewrite expXpE => ->.
  rewrite /=.
  rewrite /=.

Check F \o (@rVQphiI _ _) \o Phi.
Check pairing ((F \o (@rVQphiI _ _) \o Phi) _) _.
Check pairing _ ((H \o Phi_long) _).

Lemma FPhiE : F \o Phi =1


Definition Phi
Check
Check  Phi.

Check iter _ f.

End InversiveDecimation.
(* Section Infinite. *)
(* Local Open Scope ring_scope. *)
(* Import GRing.Theory. *)

(* Local Definition zero (x : nat) := 0 : 'F_2. *)
(* Local Definition add (x y : nat -> 'F_2) : nat -> 'F_2 := *)
(*   fun i => x i + y i. *)
(* Local Definition opp (x : nat -> 'F_2) : nat -> 'F_2 := *)
(*   fun i => - x i. *)

(* Lemma F2infA : associative add. *)
(* Proof. *)
(*   move=> x y z. *)
(*   apply Coq.Logic.FunctionalExtensionality.functional_extensionality => n. *)
(*   by rewrite /add addrA. *)
(* Qed. *)
(* Lemma F2infC : commutative add. *)
(*   move=> x y. *)
(*   apply Coq.Logic.FunctionalExtensionality.functional_extensionality => n. *)
(*   by rewrite /add addrC. *)
(* Qed. *)
(* Lemma F2inf0r : left_id zero add. *)
(*   move=> x. *)
(*   apply Coq.Logic.FunctionalExtensionality.functional_extensionality => n. *)
(*   by rewrite /add add0r. *)
(* Qed. *)
(* Lemma F2infNr : left_inverse zero opp add. *)
(*   move=> x. *)
(*   apply Coq.Logic.FunctionalExtensionality.functional_extensionality => n. *)
(*   by rewrite /add addNr. *)
(* Qed. *)

(* Definition F2inf_zmodMixin := Eval hnf in ZmodMixin F2infA F2infC F2inf0r F2infNr. *)
(* Canonical F2inf_zmodType := Eval hnf in ZmodType _ F2inf_zmodMixin. *)

(* Check ZmodType _ _. *)

(* Check LmodType 'F_2 _ _. *)
(* End Infinite. *)
End Irreducible.
