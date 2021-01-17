From mathcomp
Require Import all_ssreflect all_algebra all_field all_fingroup.
From mathcomp Require Import boolp classical_sets.
From infotheo Require Import f2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section mathcomp_ssrnat_ext.
Local Open Scope nat_scope.
Lemma ltn0ord [n : nat] : 'I_n -> 0 < n.
Proof. by case=>i; apply/leq_trans/ltn0Sn. Qed.
(* provide Wf_nat.lt_wf_rect with a similar interface to ssrnat.ltn_ind *)
Let _ltn_rect P : (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Proof.
move=> IH n.
apply (@Wf_nat.lt_wf_rect n).
move=> k H.
apply IH.
move=> m H0.
apply (H m (ltP H0)).
Defined.
Definition ltn_rect := Eval hnf in _ltn_rect.
Lemma eqnSn_mod n d : (n == n.+1 %[mod d]) = (d == 1)%N.
Proof. by rewrite -{1}(addn0 n) -addn1 eqn_modDl modnS dvdn1 mod0n; case: (d == 1). Qed.
End mathcomp_ssrnat_ext.

Section infotheo_f2_ext.
Local Open Scope ring_scope.
Import GRing.Theory.
Lemma F2_opp (a : 'F_2) : - a = a.
Proof. by case/F2P: a=> //=; rewrite oppr0. Qed.
Lemma F2_mulI (a : 'F_2) : a * a = a.
Proof. by case/F2P: a; rewrite ?mul1r ?mul0r. Qed.
End infotheo_f2_ext.

Section infotheo_f2_poly.
Lemma F2_eqp_eq (p q : {poly 'F_2}) : (p %= q)%R = (p == q).
Proof.
  case q0: (q == 0%R).
   by move/eqP: q0 => ->; rewrite eqp0.
  case p0: (p == 0%R).
   by move/eqP: p0 => ->; rewrite eq_sym -eqp0 eqp_sym.
  rewrite eqp_monic // monic_F2 //.
  + by move/negP/negP: p0.
  + by move/negP/negP: q0.
Qed.
End infotheo_f2_poly.

Section Mersenne_number.
Lemma Mersenne_composite_exponentE a b :
  2^(a * b) - 1 = (2^a - 1) * \sum_(i < b) 2 ^ (a * (b - i.+1)).
Proof.
elim: b => [|b IHb]; first by rewrite muln0 expn0 subn1 big_ord0 muln0.
rewrite big_ord_recl mulnDr -IHb mulnBl !subn1 -mulnBl mulnS expnD.
have H: forall a, 2 ^ a = 2 ^ a - 1 + 1 by move=> *; rewrite subnK // expn_gt0.
by rewrite [in LHS]H mulnDl mul1n [X in _ + X]H addn1 !addnS !subn1.
Qed.

Lemma Mersenne_prime_has_prime_exponent m : prime (2 ^ m - 1) -> prime m.
Proof.
apply: contraLR => /primePn []; first by case: m => []//[].
case => a aH /dvdnP[] b mba; move: mba aH => -> mba.
rewrite Mersenne_composite_exponentE; apply/primePn; right.
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
End Mersenne_number.

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
Proof. by apply monic_F2; rewrite -size_poly_gt0 ltnW. Qed.

Hint Resolve phi_is_monic phi_neq0 ltn_phi_pred : core.

Definition phiI := rdvdp phi.
Fact phiI_key : pred_key phiI. Proof. by []. Qed.

Canonical keyed_phiI : keyed_pred phiI_key.
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
  * rewrite !unfold_in -rmodp_mulmr ?monic_F2 // => /eqP ->.
    by rewrite mulr0 rmod0p.
Qed.

Canonical phiI_addrPred := AddrPred phiI_addr_closed.
Canonical phiI_zmodPred := ZmodPred phiI_oppr_closed.
Canonical phiI_idealr := MkIdeal phiI_zmodPred phiI_proper_ideal.

Local Open Scope quotient_scope.

Definition QphiI := {ideal_quot keyed_phiI}.

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
by rewrite (rmorphD (pi_rmorphism (Quotient.rquot_ringQuotType keyed_phiI))).
Qed.

Lemma piB p q : \pi_QphiI (p - q) = (\pi p : QphiI) - (\pi q : QphiI).
Proof.
by rewrite (rmorphB (pi_rmorphism (Quotient.rquot_ringQuotType keyed_phiI))).
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
          subr_eq0 -F2_eqp_eq // -Pdiv.IdomainMonic.modpE //
          mulrC modp_mul mulrC.
  have<-: (((egcdp phi P).1 * phi + (egcdp phi P).2 * P)) %% phi =
          ((egcdp phi P).2 * P) %% phi
   by rewrite modp_add -modp_mul modpp mulr0 mod0p add0r.
  have->: ((egcdp phi P).1 * phi + (egcdp phi P).2 * P) = gcdp phi P
   by apply/esym/eqP; rewrite -F2_eqp_eq // egcdpE.
  suff: gcdp phi P %= 1.
   rewrite !F2_eqp_eq => /eqP ->.
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
  rewrite F2_eqp_eq => /eqP -> /dvdp_leq.
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
Local Notation m_is_prime := (Mersenne_prime_has_prime_exponent pm).

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
#|image_mem (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x) (mem 'Z_(2 ^ m - 1))| = (2 ^ m - 1)%N.
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
  rewrite (divn_eq a (2 ^ m - 1)) -addnS !modnMDl eq_sym eqnSn_mod=> /eqP H.
  by move: (prime_gt1 pm); rewrite H ltnn.
Qed.

Lemma map_piE :
image_mem (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x) (mem 'Z_(2 ^ m - 1))
=i (finset [finComRingType of QphiI phi_gt1] :\ 0%R).
Proof.
 have H3: [seq x ^ i * x | i : 'Z_(2 ^ (size phi).-1 - 1)] \subset
          [set x | [finComRingType of QphiI phi_gt1] x] :\ 0.
  suff: codom (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x)
        \subset (finset [finComRingType of QphiI phi_gt1] :\ 0%R).
    by apply/fintype.subset_trans/subsetP/image_codom.
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
(q \in (image_mem (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x) (mem 'Z_(2 ^ m - 1)))).
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
  have: (0 \in (image_mem (fun (i : 'Z_(2 ^ m - 1)) => x ^ i * x) (mem 'Z_(2 ^ m - 1))))
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
    by apply/eqP; rewrite -F2_eqp_eq C.
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
         (pi_rmorphism (Quotient.rquot_ringQuotType (keyed_phiI phi))))
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
    (rmorphX (pi_rmorphism (Quotient.rquot_ringQuotType (keyed_phiI phi)))).
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
  (rmorphX (pi_rmorphism (Quotient.rquot_ringQuotType (keyed_phiI phi)))).
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
  (rmorphX (pi_rmorphism (Quotient.rquot_ringQuotType (keyed_phiI phi)))).
apply/(iffP idP); last by apply irreducibleP_inverse.
case/andP; rewrite !XnE -!exprnP !rmorphX.
by apply irreducibleP_direct.
Qed.

Lemma irreducibleP1 :
  reflect (irreducible_poly phi)
  [exists x, (F x != x) && (iter (size phi).-1 F x == x)%R].
Proof.
pose rmorphX :=
  (rmorphX (pi_rmorphism (Quotient.rquot_ringQuotType (keyed_phiI phi)))).
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
        Eqdep_dec Coq.Logic.ClassicalFacts Coq.Arith.Wf_nat
        Coq.Logic.Classical_Pred_Type
        Coq.Logic.ChoiceFacts.

Axiom pi : proof_irrelevance.
Axiom em : excluded_middle.
Axiom fc : forall a b, FunctionalChoice_on a b.

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
Local Definition scale' (a : 'F_2) (p : S) : S := fun i => a * p i.

Fixpoint subst_rec (s : seq 'F_2) x : S -> S :=
  if s is a :: s'
  then fun (b : S) => add ((subst_rec s' x \o x) b)
                       (scale' a b)
                       (*if a == 1 then b else zero*)
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

Lemma scale'Dr a p q : scale' a (add p q) = add (scale' a p) (scale' a q).
Proof. by apply funext=> i; rewrite /scale' mulrDr. Qed.

Lemma scale'Dl a b p : scale' (a + b) p = add (scale' a p) (scale' b p).
Proof. by apply funext=> i; rewrite /scale' mulrDl. Qed.

Lemma scale'1p p : scale' 1 p = p.
Proof. by apply funext=> i; rewrite /scale' mul1r. Qed.

Lemma scale'0p p : scale' 0 p = zero.
Proof. by apply funext=> i; rewrite /scale' mul0r. Qed.

Lemma scale'p0 a : scale' a zero = zero.
Proof. by apply funext=> i; rewrite /scale' mulr0. Qed.

Lemma scale'Cp a b p : scale' a (scale' b p) = scale' b (scale' a p).
Proof. by apply funext=> i; rewrite /scale' mulrCA. Qed.

Lemma scale'A  a b p : scale' a (scale' b p) = scale' (a * b) p.
Proof. by apply funext=> i; rewrite /scale' mulrA. Qed.

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
  by rewrite (addC a b) [in RHS]addC -addA scale'Dr.
Qed.

Lemma substX D a : subst 'X D a = D a.
Proof. by rewrite polyseqX /= scale'1p scale'0p add0p addp0. Qed.

Definition D (f : S) := fun i => f i.+1.

Lemma addD p q : D (add p q) = add (D p) (D q).
Proof. by []. Qed.

Lemma scale'D a p : D (scale' a p) = scale' a (D p).
Proof. by []. Qed.

Lemma subst_poly_D psi s i :
  subst psi D s i = \sum_(j < size psi) psi`_j * s (i + j)%N.
Proof.
move: s i; elim: psi; first by move=> s i; rewrite big_ord0.
move=> a psi IHpsi s i.
rewrite /= /add IHpsi big_ord_recl addrC.
congr (_ + _); first by rewrite addn0.
apply eq_bigr=> j _ /=.
rewrite /bump /D /=.
congr (_ * s _).
by rewrite add1n addnS.
Qed.

Record V := mkV {
  V_val :> S;
  _ : subst phi D V_val = zero;
}.
Arguments mkV : clear implicits.
(* Definition V := { x : S | subst phi D x = zero }. *)
Canonical V_eqType := Eval hnf in EqType V gen_eqMixin.
Canonical V_choiceType := Eval hnf in ChoiceType V gen_choiceMixin.

(*
Record V' := mkV' {
 x :> S;
 _ : `[<subst phi D x = zero>];
}.
Canonical V'_subType := Eval hnf in [subType for x].
From mathcomp Require Import classical_sets.
Canonical V'_eqType := Eval hnf in EqType V' gen_eqMixin.
Canonical V'_choiceType := Eval hnf in ChoiceType V' gen_choiceMixin.
*)

Lemma eqV f g H I : f = g -> mkV f H = mkV g I.
Proof.
  move=> K; move: H I; rewrite K => H I.
  rewrite (eq_proofs_unicity _ H I) // => x y.
  by apply em.
Qed.

Lemma eqV' u v : V_val u = V_val v -> u = v.
Proof.
  case: u=> u Hu; case: v=> v Hv /= H.
  move: Hu Hv; rewrite H.
  by move=> *; congr mkV; apply Prop_irrelevance.
Qed.

Local Definition addv (a b : V) : V.
exists (add a b).
apply functional_extensionality => i.
case: a => a Ha; case: b => b Hb.
by rewrite substD //= Ha Hb /add add0r.
Defined.

Local Definition zerov : V.
exists zero.
apply functional_extensionality => i.
rewrite subst_poly_D /zero /=.
under eq_bigr do rewrite mulr0.
by rewrite big1.
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

Lemma addvv v : addv v v = zerov.
Proof.
  case: v => v p.
  apply eqV.
  by rewrite addpp.
Qed.

Definition t (f : S) := f 0%nat.

Definition pairing (g: QphiI (phi_gt1 pm)) (x : V) : 'F_2 :=
  t (subst (generic_quotient.repr g) D x).

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
   by rewrite IH -scale'D addD.
Qed.

Lemma scale'_substD a xs p : scale' a (subst xs D p) = subst xs D (scale' a p).
Proof.
move: p; elim: xs; first by rewrite /= scale'p0.
move=> x xs IHxs p /=.
rewrite scale'Dr scale'Cp.
congr add.
by rewrite IHxs -scale'D.
Qed.

Lemma F2_scale'I a p : scale' a (scale' a p) = scale' a p.
Proof. by apply funext=> i; rewrite /scale' mulrA F2_mulI. Qed.

Lemma phiD2 : subst phi (D \o D) = subst phi D \o subst phi D.
Proof.
  elim: (polyseq phi) => //= a l IH.
  apply funext=> p.
  rewrite IH /=.
  rewrite !(addD, substC, scale'Dr) /=.
  rewrite -scale'D scale'_substD F2_scale'I addA.
  congr add.
  rewrite substC -addD -substD /=; last by exact:addD.
  by rewrite -addA addpp addp0 substC.
Qed.

Lemma subst0 p D :
  D zero = zero ->
  subst p D zero = zero.
Proof.
  move=> D00.
  elim: p => //= a p IH.
  by rewrite scale'p0 addp0 D00 IH.
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
  congr add.
  rewrite polyseqC.
  by case/F2P: c => /=; [rewrite scale'0p | rewrite scale'1p add0p].
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
  add (scale' a (iter (size s) D x)) (subst_rec s D x).
  (*add (if a == 1 then iter (size s) D x else zero) (subst_rec s D x).*)
Proof.
  elim: s a D x => [*| b s IH a D x].
   by rewrite addC.
  by rewrite /= IH addA -iterS iterSr.
Qed.

Lemma substD' (p r : {poly 'F_2}) a :
  subst (p + r) D a = add (subst p D a) (subst r D a).
Proof.
  apply funext=> i.
  rewrite /add !subst_poly_D.
  set spr := size (p + r).
  set sp := size p.
  set sr := size r.
  set N := maxn (size p) (size r).
  have Hspr : N = (spr + (N - spr))%N
    by rewrite subnKC // size_add.
  have Hsp : N = (sp + (N - sp))%N
    by rewrite subnKC // leq_maxl.
  have Hsr : N = (sr + (N - sr))%N
    by rewrite subnKC // leq_maxr.
  have-> : \sum_(j < spr) (p + r)`_j * a (i + j)%N =
           \sum_(j < N) (p + r)`_j * a (i + j)%N
    by rewrite -[X in X = _]addr0 Hspr big_split_ord /=; congr (_ + _);
    apply/esym/big1=> -[] j Hj _ /=; rewrite (nth_default _ (leq_addr j spr)) mul0r.
  have-> : \sum_(j < sp) p`_j * a (i + j)%N =
           \sum_(j < N) p`_j * a (i + j)%N
    by rewrite -[X in X = _]addr0 Hsp big_split_ord /=; congr (_ + _);
    apply/esym/big1=> -[] j Hj _ /=; rewrite (nth_default _ (leq_addr j sp)) mul0r.
  have-> : \sum_(j < sr) r`_j * a (i + j)%N =
           \sum_(j < N) r`_j * a (i + j)%N
    by rewrite -[X in X = _]addr0 Hsr big_split_ord /=; congr (_ + _);
    apply/esym/big1=> -[] j Hj _ /=; rewrite (nth_default _ (leq_addr j sr)) mul0r.
  rewrite -big_split /=.
  by under eq_bigr do rewrite coef_add_poly mulrDl.
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
  by rewrite substDMXC polyC1 mul1r polyseq1 /= scale'1p add0p substC.
Qed.

Lemma substMXn n x : subst 'X^n x = \big[comp/id]_(i < n) subst 'X x.
Proof.
  elim: n x => [x|n IH x].
   rewrite big_ord0 expr0 polyseqC /=.
   apply/functional_extensionality => ?.
   by rewrite scale'1p add0p.
  rewrite exprSr substMX IH big_ord_recl.
  elim: n {IH} => [|n IH].
   rewrite big_ord0; apply/functional_extensionality => ?.
   by rewrite polyseqX /= scale'1p scale'0p add0p addp0.
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
        ?monic_F2 ?phi_neq0 ?phi_gt1 // addr_eq0
        -!Pdiv.IdomainMonic.modpE ?monic_F2 ?phi_neq0 ?phi_gt1 //
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
   by rewrite -expr2 polyseqXn polyseqX /= !scale'0p !addp0 !add0p.
  repeat move: substM => /= <-.
  by rewrite mulrC mulrA mulrC mulrA substM /= fH subst0.
Qed.

Lemma nondeg1 x :
  x = zerov <-> (forall y, pairing y x = 0).
Proof.
  split => [-> y|].
* by rewrite /pairing subst0.
* rewrite /pairing; case: x => x p H0.
  apply eqV, functional_extensionality => i.
  move: (H0 (\pi 'X^i)); case: piP => y E.
  rewrite (subst_subst _ E) //= polyseqXn /subst subst_rcons size_nseq.
  have->: (subst_rec (nseq i 0) D x) = zero.
   elim: i x {E p H0} => // i IH x.
   by rewrite /= scale'0p addp0 IH.
  rewrite /= addp0 scale'1p.
  elim: i x {E p H0} => // i IH x.
  by rewrite iterSr => /IH.
Qed.

Definition Veq (x y : V) :=
  [forall i, V_val x (i : 'I_(size phi).-1) == V_val y i].

Lemma add_eq0 x y :
  add x y = zero <-> x = y.
Proof.
  split => [H |->].
  * move: (f_equal (add x) H).
    by rewrite addp0 addA addpp add0p => ->.
  * by rewrite addpp.
Qed.

Lemma addv_eq0 x y :
  addv x y = zerov <-> x = y.
Proof.
  split => [H |->].
  * move: (f_equal (addv x) H).
    by rewrite [in RHS]addvC add0v addvA addvv add0v => ->.
  * by rewrite addvv.
Qed.

Canonical op : Monoid.law zero.
  apply: (@Monoid.Law _ zero add addA) => p;
  by rewrite !(add0p, addp0).
Defined.

Lemma big_subst (F : nat -> S) p j :
  (\big[add/zero]_(i < p) F i) j = \sum_(i < p) F i j.
Proof.
  elim: p F => [?|p IH F].
   by rewrite !big_ord0.
  by rewrite !big_ord_recr /= /add /= IH.
Qed.

Section rVVI_def.
Local Notation n := (size phi).
Variable x : 'rV['F_2]_n.-1.
(*
Require Import Program.

Program Fixpoint rVSI (x : 'rV['F_2]_(size phi).-1) (i : nat) {measure i} : 'F_2 :=
  (if (i < (size phi).-1)%N as b
      return (protect_term ((i < (size phi).-1)%N = b) -> 'F_2)
   then (fun H : (i < (size phi).-1)%N = true => x ord0 (Ordinal H))
   else (fun=> \sum_(j < (size phi).-1) phi`_j * rVSI x (i + j - (size phi).-1)%nat))
    (erefl (i < (size phi).-1)%nat).
Next Obligation.
  apply/ltP.
  rewrite -subnBA; last by apply/ltnW.
  case: j => j /=.
  rewrite ltnNge /leq.
  case H: ((size phi).-1 - j)%nat => // _.
  rewrite subn_eq0.
  case: i H0 rVSI => [/negP/negP|i H0 _].
   rewrite -ltnNge leqNgt prednK // ?phi_gt1 ?phi_gt0 //.
  by rewrite subSS ltnS leq_subr.
Qed.
*)

Fixpoint rVSI_gen (i : nat) : seq 'F_2.
Proof.
refine (match i with O => [::] | i'.+1 => let tail := rVSI_gen i' in _ :: tail end).
refine (if (i' < n.-1)%N then _ else _).
- refine (x ord0 (Ordinal (_ : (i' %% n.-1 < n.-1)%N))).
  by apply/ltn_pmod/(predphi_geq1 pm).
- refine (\sum_(j < n.-1) _)=> /=.
  exact (phi`_j * (nth 0 tail (n.-2 - j))).
Defined.

Definition rVSI i := head 0 (rVSI_gen i.+1).

Lemma rVSI_gen_mkseq' i : rVSI_gen i = mkseq (fun j => rVSI (i - j.+1)) i.
Proof.
elim: i=> //= i IHi.
set X := if _ then _ else _.
rewrite IHi /mkseq /=.
congr (_ :: _); first  by rewrite subn1.
rewrite (map_comp rVSI) [in RHS](map_comp rVSI).
congr map.
apply (@eq_from_nth _ 0%N); first by rewrite !size_map !size_iota.
move=> j; rewrite size_map size_iota=> ji.
rewrite (nth_map 0%N 0%N) ?size_iota // (nth_map 0%N 0%N) ?size_iota //.
rewrite nth_iota ?ji // nth_iota ?ji //.
Qed.

Lemma rVSI_gen_mkseq i : rVSI_gen i = rev (mkseq rVSI i).
Proof.
rewrite rVSI_gen_mkseq' /mkseq -map_rev.
rewrite (map_comp rVSI) [in RHS](map_comp rVSI).
congr map.
apply (@eq_from_nth _ 0%N); first by rewrite  !size_map ?size_rev !size_iota.
move=> j.
rewrite size_map size_iota=> ji.
rewrite (nth_map 0%N 0%N) ? size_iota // (nth_map 0%N 0%N) ?size_rev ?size_iota //.
rewrite nth_rev ?size_iota //.
rewrite nth_iota ?size_iota // nth_iota ?size_iota //.
by rewrite ltn_subLR // -{1}(add0n i) ltn_add2r ltn0Sn.
Qed.

Lemma nth_rVSI_gen (i j : nat) : (j <= i)%N -> nth 0 (rVSI_gen i.+1) (i - j) = rVSI j.
Proof.
move=> ji.
have iji: (i - j < i.+1)%N
  by rewrite -(addn1 i) ltn_subLR // addnCA -{1}(addn0 i) ltn_add2l addn1 ltn0Sn.
rewrite rVSI_gen_mkseq' /mkseq (nth_map 0%N 0) ?size_iota // nth_iota //.
by rewrite add0n subSS subKn.
Qed.

Lemma rVSI_init (i : nat) (H : (i < n.-1)%N) :
  rVSI i = x ord0 (Ordinal H).
Proof. by rewrite /rVSI /= H; congr (_ _ _); apply ord_inj=> /=; rewrite modn_small. Qed.

Lemma rVSI_rec (i : nat) :
  (n.-1 <= i)%N -> rVSI i = \sum_(j < n.-1) phi`_j * rVSI (i - n.-1 + j).
Proof.
move=> ni.
set n':= n.-2.
have Hn' : n.-1 = n'.+1 by rewrite prednK // (predphi_geq1 pm).
rewrite Hn'.
set i' := i.-1.
have Hi' : i = i'.+1 by rewrite prednK //; apply/leq_trans/ni; rewrite Hn' ltnS.
move: (ni); rewrite /rVSI /= leqNgt; move/negbTE ->.
rewrite [in LHS] Hn'; apply eq_bigr=> j _ /=.
congr (_ * _).
set X := if _ then _ else _.
rewrite -(subSS j n').
rewrite -{1}Hn'.
set k := (i - n.-1)%N.
have Hk : n.-1 = (i - k)%N by rewrite subKn.
rewrite Hk Hi' -subnDA addnC subnDA subSS -subnDA nth_rVSI_gen;
first by rewrite /rVSI /= (_ : (j + k)%N = (i - n'.+1 + j)%N) // /k Hn' addnC.
rewrite /k /i' addnC addnBAC //.
rewrite -(leq_add2r 1) !addn1 prednK; last by rewrite Hi'.
rewrite ltn_subLR; last by apply/(leq_trans ni)/leq_addr.
rewrite addnC ltn_add2r.
rewrite {X}; rewrite {Hk}; rewrite {k}.
by case: j=> j; rewrite -Hn'.
Qed.

Lemma rVVI_proof : subst phi D rVSI = zero.
Proof.
apply/funext=> i; apply/eqP.
rewrite subst_poly_D /zero /=.
have -> : n = n.-1.+1
  by rewrite prednK //; move: (leq_pred n); apply/leq_trans/(predphi_geq1 pm).
rewrite big_ord_recr addr_eq0 F2_opp /= -lead_coefE.
have-> : lead_coef phi = 1
  by apply/eqP; rewrite F2_eq1 lead_coef_eq0 -size_poly_leq0 leqNgt negbK (phi_gt0 pm).
rewrite mul1r rVSI_rec ?leq_addl //.
apply/eqP/eq_bigr=> j _; congr (_ * rVSI (_ + _)%N).
by rewrite -addnBA ?leqnn // subnn addn0.
Qed.

Definition rVVI : V := mkV rVSI rVVI_proof.
End rVVI_def.

Definition V_rV (x : V) : 'rV['F_2]_(size phi).-1 :=
  \row_(i < (size phi).-1) V_val x i.

Section rVVI_prop.
Local Notation n := (size phi).
Lemma V_rVVI (v : V) : v = rVVI (V_rV v).
Proof.
rewrite /V_rV.
case: v=> v Hv.
apply/eqV'/funext => /=.
apply: ltn_ind=> i IHi.
case Hin : (i < n.-1)%N; first by rewrite rVSI_init mxE.
move/negbT: Hin; rewrite ltnNge negbK=> Hin.
rewrite rVSI_rec //.
under eq_bigr => j _.
- move: (ltn_ord j)=> Hj.
  rewrite -IHi; last first.
  rewrite addnBAC // ltn_subLR; first by rewrite addnC ltn_add2r.
  by move: (leq_addr j i); apply leq_trans.
  over.
apply/eqP; rewrite -(F2_opp (v i)) eq_sym -addr_eq0.
set X := _ + _.
have->: X = \sum_(j < n) phi`_j * v (i - n.-1 + j)%N.
- have-> : n = n.-1.+1
    by rewrite prednK //; move: (leq_pred n); apply/leq_trans/(predphi_geq1 pm).
  rewrite big_ord_recr /= /X (_ : (i - n.-1 + n.-1)%N = i) ?subnK //.
  rewrite -lead_coefE.
  have-> : lead_coef phi = 1
    by apply/eqP; rewrite F2_eq1 lead_coef_eq0 -size_poly_leq0 leqNgt negbK (phi_gt0 pm).
  rewrite mul1r.
  by congr (_ + _).
by move/(congr1 (fun p => p (i - n.-1)%N)): Hv; rewrite subst_poly_D /zero => ->.
Qed.

Lemma V_rVVI' (v : V) : exists x, v = rVVI x.
Proof. by exists (V_rV v); exact: V_rVVI. Qed.
End rVVI_prop.

Lemma VeqP : Equality.axiom Veq.
Proof.
move=> x y.
apply/(iffP idP).
- rewrite /Veq => /forallP /= H.
  rewrite (V_rVVI x) (V_rVVI y).
  congr (rVVI (\row_j _)).
  by apply funext=> _; apply funext=> j /=; apply/eqP; rewrite H.
-  by move->; rewrite /Veq; apply/forallP.
Qed.

(*
Definition V_eqMixin := EqMixin VeqP.
Canonical V_eqType := Eval hnf in EqType V V_eqMixin.
*)

Lemma pairing_addv x y z :
  pairing x (addv y z) = pairing x y + pairing x z.
Proof.
  case: y z => [y Hy] [z Hz].
  by rewrite /pairing /addv /= substD.
Qed.

Lemma tD x y : t (add x y) = t x + t y.
Proof. by []. Qed.

Lemma pairing_add x y z :
  pairing (x + y) z = pairing x z + pairing y z.
Proof.
  rewrite /pairing -tD -substD'; congr t.
  apply subst_subst; first by case: z.
  by rewrite reprK piD !reprK.
Qed.

Definition V_zmodMixin := ZmodMixin addvA addvC add0v addIv.
Canonical V_zmodType := ZmodType V V_zmodMixin.
Definition scalev (a : 'F_2) (v : V) : V.
Proof.
refine (mkV (scale' a v) _).
case: v=>v /= Hv.
by rewrite -scale'_substD Hv scale'p0.
Defined.
Fact scalev1x v : scalev 1 v = v.
Proof. by apply/VeqP/forallP=> i /=; rewrite scale'1p. Qed.
Fact scalevA x y A : scalev x (scalev y A) = scalev (x * y) A.
Proof. by apply/VeqP/forallP=> i /=; rewrite scale'A. Qed.
Fact scalevxDl A x y : scalev (x + y) A = scalev x A + scalev y A.
Proof. by apply/VeqP/forallP=> i /=; rewrite scale'Dl. Qed.
Fact scalevxDr x A B : scalev x (A + B) = scalev x A + scalev x B.
Proof. by apply/VeqP/forallP=> i /=; rewrite scale'Dr. Qed.
Definition V_lmodMixin := LmodMixin scalevA scalev1x scalevxDr scalevxDl.
Canonical V_lmodType := Eval hnf in LmodType 'F_2 V V_lmodMixin.

(* *)

Lemma V_vect_axiom : Vector.axiom (size phi).-1 V.
Proof.
rewrite /Vector.axiom_def.
exists V_rV.
- move=> a u v.
  rewrite /V_rV.
  apply/rowP=> i.
  by rewrite !mxE /= /add /scale'.
- exists rVVI; first by move=> ?; rewrite -V_rVVI.
  move=> v;  apply/rowP=> i.
  rewrite /V_rV /rVVI /= mxE.
  case: i=> i Hi /=.
  rewrite /rVSI /= Hi /=.
  congr (v _ _).
  apply val_inj=> /=.
  by rewrite modn_small.
Qed.

Definition V_vectMixin := VectMixin V_vect_axiom.
Canonical V_vectType := Eval hnf in VectType 'F_2 V V_vectMixin.

Local Notation "V ^*" := 'Hom([ vectType 'F_2 of V ], regular_vectType [ringType of 'F_2]).

Lemma pairing0v x : pairing 0 x = 0.
Proof.
  rewrite /pairing.
  rewrite -[RHS](_ : t (subst (polyseq 0) D x) = _).
   congr t.
   apply subst_subst.
    by case: x.
   by rewrite reprK (rmorph0 (pi_rmorphism (Quotient.rquot_ringQuotType (keyed_phiI phi)))).
  by rewrite /t polyseqC.
Qed.

Lemma nondeg2 x :
  x = 0 <-> (forall y, pairing x y = 0).
Proof.
  split => [-> ?|]; first by rewrite pairing0v.
  rewrite (coord_vbasis (memvf x)).

  Check nondeg1.



Check (QphiI (phi_gt1 pm))^*.
Check V^*.
Check 'Hom([ vectType 'F_2 of QphiI (phi_gt1 pm) ], regular_vectType [ringType of 'F_2]).
Check regular_vectType [ringType of 'F_2].
Check [ vectType 'F_2 of QphiI (phi_gt1 pm) ] .

Lemma pairing_adj_iter s x y:
  pairing x (iter s H' y) = pairing (iter s (@irreducible.F _ pm) x) y.
Proof.
  elim: s x y => // s IHs x y.
  by rewrite /= -pairing_adj IHs -iterSr -iterS.
Qed.

Lemma fH (w : V) :
  exists (v: QphiI (phi_gt1 pm)), (w <> zerov -> pairing v w = 1)
                             /\ (w = zerov -> v = 0).
Proof.
  case: (em (w = zerov)) => w0.
   apply not_all_not_ex.
   rewrite w0 => /(_ 0).
   case/Classical_Prop.not_and_or => //.
   apply/ex_not_not_all.
   by suff: zerov <> zerov -> pairing 0 zerov = 1 by move=> w1; exists w1.
  move: (w0); rewrite {1}nondeg1 => /not_all_ex_not w1.
  case: w1 => x xH; exists x; split => [|/w0 //].
  move: xH; case: (pairing x w) => [][|[]//] i /eqP // ? ?.
  by apply/val_inj.
Qed.

Lemma addr_eq0 (x y : QphiI_zmodType (phi_gt1 pm)) :
  (y + x == 0) = (y == x).
Proof.
   by rewrite -[in RHS]subr_eq0 oppr_char2 ?char2_phi.
Qed.

Lemma nondeg2 x :
  x = 0 <-> (forall y, pairing x y = 0).
Proof.
  split => [-> [] y yH|].
* rewrite /pairing.
  have->: 0 = \pi_(QphiI (phi_gt1 pm)) 0 by rewrite linear0.
  case: piP => z E.
  by rewrite (subst_subst _ E) // polyseq0.
* move=> xy; apply/eqP/negP => /negP x0.
  apply/ex_not_not_all: xy; move: x0.
  case: (fc fH) => f fH.
  suff: exists y, f y = x.
   case => y fyx x0.
   exists y.
   case: (fH y).
   case y0: (y == zerov).
    move=> + /(_ (eqP y0)).
    rewrite fyx => + x00.
    by rewrite x00 eqxx in x0.
   move/eqP: y0 => y0 /(_ y0).
   by rewrite fyx => ->.

  suff: forall x, exists y, f y = x by apply.

  suff: exists y, (f y) + x = 0.
   case => y; exists y.
   apply/eqP.
   by rewrite -addr_eq0 p.

   Search (_ - _ = _ + _).
   rewrite .subr_char2.
   rewrite
   oppr_char2 ?char2_phi //.
   rewrite
  rewrite -addv_eq0.
  apply/not_all_not_ex.

   move=> /(_ (eqP y0)).
    rewrite x0.
   rewrite fyx.
   rewrite fyx -fyx.
   rew
   rewrite

  have: exists g, cancel f g.

  rewrite (coord_basis (QphiIX_full _) (memvf x)).
  rewrite /=.
* rewrite
* case: (em (x = 0)) => // x0; suff: False by [].
  suff/(_ _ x0): forall x, x <> 0 -> exists y, pairing x y = 1.
   by case => y; move: (H0 y) => ->.
  move=> {x x0 H0} x x0.
  have:
   Check QphiI (phi_gt1 pm).

Lemma irreducibleP3 x :
  H' x <> x ->
  irreducible_poly phi <-> iter (size phi).-1 H' x = x.
Proof.
move=> Hxx.
split; last first.
* move: Hxx; rewrite -addv_eq0 nondeg1 => Hxx.
  rewrite -addv_eq0 nondeg1 => Hpxx.
  apply/irreducibleP1/existsP; case/not_all_ex_not: Hxx => x0 Hxx.
  rewrite pairing_addv -pairing_adj -pairing_add in Hxx.
  exists x0; apply/andP; split.
  + apply/negP => /eqP Fxx.
    move: Fxx Hxx => ->.
    rewrite addrr_char2 ?char2_phi // pairing0v //.
  + move: {Hpxx} (Hpxx x0).
    rewrite pairing_addv pairing_adj_iter -pairing_add => Hpxx.
    rewrite -subr_eq0 oppr_char2 ?char2_phi //.
    apply/eqP.
    subr0_eq
    rewrite addr0_eq.
    rewrite -addv_eq0.

  have/ex_not_not_all {x0 Hxx} : exists x0, pairing (irreducible.F x0 + x0) x <> 0 by exists x0.
  Hxx :
  rewrite pairing_addv -pairing_adj -pairing_add in Hxx.
  rewrite -add_eq0.


   Check not_all_not_ex.

  rewrite /= in Hpxx.


 => [/(@irreducibleP1 _ pm)/existsP[] s /andP[] | ].
* Check pairing_adj x s.


Definition i (x: V) := [ tuple (sval x i) | i < (size phi).-1 ].
(* Require Import Coq.Program.Wf. *)
(* Require Import FunInd. *)
Require Import Recdef.

Function j (x: ((size phi).-1).-tuple 'F_2) (p : nat) {measure p} : 'F_2 :=
  if (p < (size phi).-1)%nat
  then nth 0 x p
  else (\big[add/zero]_(i < (size phi).-1) subst (phi`_i)%:P D (fun k : nat => j x (k + i)%nat)) (p  - (size phi).-1)%nat.
Next Obligation.


   (fun j : nat => x (j + (size phi).-1)%N)
  \big[add/zero]_(i < (size phi).-1) subst (phi`_i)%:P D (fun j : nat => x (j + i)%N) =
  x`_0
case:
  {x : ((size phi).-1).-tuple 'F_2 | subst phi D (nth 0 x) = zero }.
  have d : 'I_(size phi).-1.
   rewrite -[(size phi).-1]prednK.
   apply ord0.
   by case: (size phi) (phi_gt1 pm).
  case: x => x H.
  rewrite /=.
  set T := nth 0 _.
  have->: T = x.
   apply/functional_extensionality => j.
   rewrite /T (nth_map d) ?size_enum_ord //.
  have->: nth 0 [seq x i | i <- enum 'I_(size phi).-1] = x.
  rewrite /= nth_map.
  rewrite /=.

  rewrite /=.
  rewrite (nth_map _ 0).
  rewrite (nth_map (x d)).
  rewrite /=.
  Set Printing All.
  rewrite

  rewrite /=.
  rewrite nth_map
  rewrite nth_seq.
  :=
Check i.
Check {x : ((size phi).-1).-tuple 'F_2 | subst phi D (nth 0 x) = zero }.

Check subst phi D (sval x).

(* Lemma inji: injective i. *)
(* Proof. *)
(*   move=> x y H. *)
(*   apply/eqP/forallP => j. *)
(*   rewrite eqE /=. *)
(*   have d : 'I_(size phi).-1. *)
(*    rewrite -[(size phi).-1]prednK. *)
(*    apply ord0. *)
(*    by case: (size phi) (phi_gt1 pm). *)
(*   have<-: nth 0%R (i x) j = sval x j. *)
(*    by rewrite (nth_map d) /= ?nth_enum_ord ?size_enum_ord. *)
(*   have<-: nth 0%R (i y) j = sval y j. *)
(*    by rewrite (nth_map d) /= ?nth_enum_ord ?size_enum_ord. *)
(*   by rewrite H. *)
(* Qed. *)

Definition jH (x : ((size phi).-1).-tuple 'F_2) :
  exists y : option V,
    match y with
    | Some y => forall (i : 'I_(size phi).-1), sval y i = tnth x i
    | None => True
    end.
  pose f := nth 0 x.
  case (em (subst phi D f = zero)) => z; last by exists None.
  apply: (ex_intro _ (Some (exist _ _ z))) => i.
  by rewrite /f /= -tnth_nth.
Defined.
Check
Check i.
Check {in _ &, injective i}.
Check i @: _.
t
Check #|_|.
(* Print V. *)

(* (* Lemma V_enum : *) *)

(* (* Lemma V_enumP : Finite.axiom *) *)
(* (* Check FinMixin _. *) *)

(* (* Check sig_choiceMixin. *) *)
(* (* Check finType. *) *)
(* (* Print V. *) *)
(* (* Check [choiceMixin of V by <:]. *) *)

(* Check ChoiceMixin _ _. *)
(* Definition jH (x : ((size phi).-1).-tuple 'F_2) : *)
(*   exists y : option V, *)
(*     match y with *)
(*     | Some y => forall (i : 'I_(size phi).-1), sval y i = tnth x i *)
(*     | None => True *)
(*     end. *)
(*   pose f := nth 0 x. *)
(*   case (em (subst phi D f = zero)) => z; last by exists None. *)
(*   apply: (ex_intro _ (Some (exist _ _ z))) => i. *)
(*   by rewrite /f /= -tnth_nth. *)
(* Defined. *)
(* Definition jH': exists j, pcancel i j. *)
(* case: (fc jH) => j H; exists j => x. *)
(* Check H (i x). *)
(* rewrite *)
(* rewrite /=. *)

Definition V_choiceMixin : choiceMixin V.
refine (@PcanChoiceMixin _ _ i _ _).
(* Check i. *)
(* Print pcancel. *)
(* Check pcancel i _. *)
Check fc jH.
  constructor.

Set Printing All.
Print tuple_choiceMixin.
apply: (ex_i

Definition j (x : nat) :=
  if j
  then Some
  else None
Variable x: V.
Check sval x _ : nat.
Check x.

  [forall i, sval x (i : 'I_(size phi).-1) == sval y i].
  Admitted.

Canonical V_choiceType := ChoiceType V V_choiceMixin.


(*   move=> X. *)
(*   rewrite /choiceMixin. *)
(*   done. *)
(* Check ChoiceType _ V_choiceMixin. *)
(* Definition V_choiceType := *)

Definition V_zmodMixin := ZmodMixin addvA addvC add0v addIv.
Canonical V_zmodType := ZmodType V V_zmodMixin.
Check V_zmodType.

Lemma fH (w : V) :
  exists (v: QphiI (phi_gt1 pm)), (w <> zerov -> pairing v w = 1)
                             /\ (w = zerov -> v = 0).
Proof.
  case: (em (w = zerov)) => w0.
   apply not_all_not_ex.
   rewrite w0 => /(_ 0).
   case/Classical_Prop.not_and_or => //.
   apply/ex_not_not_all.
   by suff: zerov <> zerov -> pairing 0 zerov = 1 by move=> w1; exists w1.
  move: (w0); rewrite {1}nondeg1 => /not_all_ex_not w1.
  case: w1 => x xH; exists x; split => [|/w0 //].
  move: xH; case: (pairing x w) => [][|[]//] i /eqP // ? ?.
  by apply/val_inj.
Qed.

Definition f := fc fH.
Check f.

Check Finite.enum V.
Check enum ('I__ : Type).
Check enum .
(* * case: (fc fH) => f H. *)





(*    move/(_ _ x0). *)

(*   rewrite /pairing. *)
(* Qed. *)

Lemma nondeg1' x H' :
  H' x = x <-> (forall y, pairing y (addv (H' x) x) = 0).
Proof.
  split => [-> y|/nondeg1 /(f_equal (addv x))].
* by rewrite addvv /pairing subst0.
* by rewrite addvC -addvA addvv addvC add0v addvC add0v.
Qed.

Lemma lem2 :
  (forall x, H' x <> x -> iter (size phi).-1 H' x = x) <->
  (forall s, irreducible.F s != s ->
         iter (size phi).-1 (irreducible.F (pm:=pm)) s == s).
Proof.
  split => [H s Fss|].
* apply/eqP.
  rewrite -nondeg1' in H.
*
  rewrite

Lemma irreducibleP3 x :
  H' x <> x ->
  irreducible_poly phi <-> iter (size phi).-1 H' x = x.
Proof.
move=> Hxx.
split => [/(@irreducibleP1 _ pm)/existsP[] s /andP[] | ].
* Check pairing_adj x s.

split; last first.
move=> Hxx0.

apply/(iffP idP) => [iHxx|].
* apply/irreducibleP1/existsP.
  by exists x; rewrite Hxx iHxx.
* by case/irreducibleP/andP => ? /expandF ->.
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
