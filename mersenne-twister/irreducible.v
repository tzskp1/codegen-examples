From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
Require Import polyn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
based on:
 http://www.math.sci.hiroshima-u.ac.jp/~m-mat/TEACH/0407-2.pdf
 P. 27
*)

Lemma f2p_monic (p : {poly [finFieldType of 'F_2]}) :
  (p != 0)%R -> p \is monic.
Proof.
  move=> /negPf p0; apply/eqP.
  case lp0: (lead_coef p == 0)%R.
   by rewrite lead_coef_eq0 p0 in lp0.
  case: (lead_coef p) lp0 => [][]//[]// *.
  by apply/val_inj.
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

Lemma ltn_subr a b : 0 < b < a -> a - b < a.
Proof.
  case/andP.
  elim: a => // a IH.
  case ab: (b == a).
   move/eqP: ab => ->.
   by rewrite subSnn !ltnS.
  move/IH => {IH} IH.
  rewrite ltnS leq_eqVlt ab => ba.
  by rewrite subSn ?ltnS ?IH // ltnW.
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

Lemma ltn_size_polyC_X (R : fieldType) (p : {poly R}) (c : R) (n : nat) :
  p != 0%R -> (size (c%:P)%R < size (p * 'X)%R)%N.
Proof.
move=> ?; rewrite size_mul ?polyX_eq0 // size_polyX size_polyC addn2.
case: (c != 0%R) => //.
by rewrite ltnS lt0n size_poly_eq0.
Qed.

Lemma polyX_neq0 (R : fieldType) : (('X : {poly R}) != 0)%R.
Proof. by rewrite -size_poly_eq0 size_polyX. Qed.

Hint Resolve ltn_size_polyC_X polyX_neq0 : core.

Lemma polyXn_eq0 (R : fieldType) n :
  (('X^n : [ringType of {poly R}]) == 0)%R = false.
Proof. by rewrite -size_poly_eq0 size_polyXn. Qed.

Lemma exp2_dvd a b :
  2^(a * b) - 1 = (2^a - 1) * \sum_(i < b) 2 ^ (a * (b - i.+1)).
Proof.
elim: b => [|b IHb]; first by rewrite muln0 expn0 subn1 big_ord0 muln0.
rewrite big_ord_recl mulnDr -IHb mulnBl !subn1 -mulnBl mulnS expnD.
have H: forall a, 2 ^ a = 2 ^ a - 1 + 1 by move=> *; rewrite subnK // expn_gt0.
by rewrite [in LHS]H mulnDl mul1n [X in _ + X]H addn1 !addnS !subn1.
Qed.

Section irreducibility.
Variable phi : {poly [finFieldType of 'F_2]}.
Local Notation m := (size phi).-1.
Hypothesis pm : prime (2 ^ m - 1).

Lemma m_is_prime : prime m.
Proof.
move: pm; apply: contraLR => /primePn []; first by case: m => []//[].
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

Lemma phi_neq0 : (phi != 0)%R.
Proof.
  move: m_is_prime.
  rewrite -size_poly_eq0.
  by case: (size phi).
Qed.

Lemma phi_gt1 : 1 < size phi.
Proof. by case: (size phi) m_is_prime => []//[]. Qed.

Lemma phi_gt2 : 2 < size phi.
Proof. by case: (size phi) m_is_prime => []//[]//[]. Qed.

Lemma phi_gt0 : 0 < size phi.
Proof. by case: (size phi) m_is_prime. Qed.

Lemma predpower_gt_succpower : (2 ^ m).-1 < (2 ^ m).+1.
Proof. by case: (2 ^ m) pm. Qed.

Lemma power_gt0 : 0 < 2 ^ m.
Proof. by case: (2 ^ m) pm. Qed.

Lemma predpower_gt0 : 0 < 2 ^ m - 1.
Proof. by case: (2 ^ m - 1) pm. Qed.

Lemma predpower_neq0 : 0 != 2 ^ m - 1.
Proof. by case: (2 ^ m - 1) pm. Qed.

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

Canonical qpoly_ringType_phi :=
  Eval hnf in qpoly_ringType phi_gt1.
Canonical qpoly_comRingType_phi :=
  Eval hnf in qpoly_comRingType phi_gt1.
Definition pi := canon_surj phi_gt1.

Hint Resolve phi_gt0 phi_gt1 phi_gt2 phi_gtb predphi_neq0
     predpredpower_power predpredpower_gt0 predphi_gt1 predphi_geq1
     predphi_neq0 predpower_neq0 predpower_gt0
     p_ord_prf predpower_gt_succpower power_gt0 phi_neq0 polyX_neq0 : core.

Lemma mod_ord (a : nat) y (x : ordinal y) : ordinal y.
  apply/(@Ordinal _ (x %% a))/(leq_ltn_trans (leq_mod _ _)).
  by case: x.
Defined.

Definition p_ord := Ordinal p_ord_prf.

Lemma one_ord : ordinal (2 ^ m).+1.
 have H: 1 < (2 ^ m).+1.
  case/primeP: pm => pm' _.
  apply/(ltn_trans pm').
  rewrite subn1.
  by case: (2 ^ m) pm.
 by apply (Ordinal H).
Defined.

Section order.
Context {R : ringType}.
Variable t : R.
Implicit Types (a : R).
Local Open Scope ring_scope.

Definition stab a : {set 'I_(2 ^ m).+1} :=
[set n | t ^+ (nat_of_ord n) * a == a].

Lemma foldl_min_cons x y z : foldl minn x (y :: z) = minn y (foldl minn x z).
Proof.
  elim: z x y => [*| ? z IH x y] /=;
  by rewrite minnC // -IH /= minnAC minnC.
Qed.

Definition min_stab a :=
foldl minn (2 ^ m)%N
      (filter (fun x => x > 0)%N (map (@nat_of_ord _) (enum (stab a)))).

Definition min_stab_ord a : ordinal (2 ^ m).+1.
  have H: (min_stab a < (2 ^ m).+1)%N.
   rewrite /min_stab.
   elim: [seq _ | _ <- _] => [|c l IH].
    by case: (2 ^ m)%N pm.
   apply/leq_ltn_trans/IH => {IH} /=.
   by case: ifP => //; rewrite foldl_min_cons geq_minr.
 by apply (Ordinal H).
Defined.

Lemma foldl_minn_in xs m' :
  has (fun x => x < m'.+1)%N xs -> foldl minn m' xs \in xs.
Proof.
  elim: xs m' => // x xs IH m'.
  rewrite /= in_cons.
  case xm: (x < m'.+1)%N.
   rewrite /minn ltnNge -ltnS xm /= -/minn => _ {IH xm}.
   elim: xs x => [?|y ? IH /= x].
    by rewrite /= eqxx.
   case xy: (x < y)%N.
    rewrite /minn xy /= -/minn in_cons.
    case/orP: (IH x) => -> //.
    by rewrite !orbT.
   rewrite /minn xy /= -/minn in_cons.
   by case/orP: (IH y) => ->; rewrite !orbT.
  move/negP/negP: xm; rewrite -ltnNge ltnS leq_eqVlt => /orP [/eqP <-|mx].
  by rewrite /minn ltnSn -/minn => /IH ->; rewrite orbT.
  by rewrite /minn ltnW // -/minn => /IH ->; rewrite orbT.
Qed.

Lemma min_stab_gt0 a : (0 < min_stab_ord a)%N.
Proof.
  rewrite /min_stab_ord /min_stab /=.
  elim: (enum (pred_of_set (stab a))) => [|a' l IH /=] //.
  case: ifP => //.
  case: a' => []//[]// a' ??.
  rewrite foldl_min_cons /=.
  move: IH; set T := (foldl minn _  _).
  case: T => // ?.
  by rewrite minnSS.
Qed.

Lemma min_stab_in a y :
  y \in stab a -> 0 != y ->
  min_stab a \in (filter (fun x => x > 0)%N (map (@nat_of_ord _) (enum (stab a)))).
Proof.
  case: y => y Hy1 Hy2 y0.
  apply/foldl_minn_in/hasP/ex_intro2/Hy1.
  rewrite mem_filter lt0n eq_sym y0.
  have->: y = Ordinal Hy1 by [].
  by rewrite mem_map ?mem_enum ?Hy2 // => *; apply/val_inj.
Qed.

Lemma min_stab_min a y :
  y \in stab a -> 0 != y -> (min_stab_ord a <= y)%N.
Proof.
  rewrite -mem_enum /min_stab_ord /min_stab /=.
  elim: (enum (pred_of_set (stab a))) => // ?? IH.
  rewrite !in_cons /= lt0n => /orP [/eqP <-|/IH {IH} IH /IH {IH}].
   rewrite eq_sym => ->.
   by rewrite foldl_min_cons geq_minl.
  case: ifP => // a0 H.
  apply/leq_trans/H.
  by rewrite foldl_min_cons geq_minr.
Qed.

Lemma min_stab_cond a b y :
  y \in stab a -> 0 != y ->
  t ^+ (b * min_stab a)%N * a == a.
Proof.
  move=> ys y0.
  have H1: t ^+ (min_stab a) * a == a.
   suff: min_stab a \in (filter (fun x => x > 0)%N
                                (map (@nat_of_ord _) (enum (stab a)))).
    have->: min_stab a = min_stab_ord a by [].
    rewrite mem_filter mem_map.
     by rewrite mem_enum inE => /andP [].
    by move=> ?? H; apply/val_inj/H.
   apply: (@min_stab_in _ _ ys y0).
  elim: b => [|b IHb]; first by rewrite !mul0n GRing.mul1r.
  rewrite mulSn GRing.exprD -GRing.mulrA.
  by move/eqP: IHb => ->.
Qed.

Lemma min_stab_dvd a x : x \in stab a -> (min_stab a %| x)%N.
Proof.
  case x0: (0 == x); first by move/eqP: x0 => <-.
  move/negP/negP: x0 => x0 H; move: (H).
  rewrite inE (divn_eq x (min_stab a)) addnC GRing.exprD
  -GRing.mulrA (eqP (@min_stab_cond a (x %/ min_stab a) x H x0)) => H0.
  rewrite dvdn_addr ?dvdn_mull //.
  case x0': (0 != @mod_ord (min_stab a) _ x).
   have: @mod_ord (min_stab a) _ x \in stab a by rewrite inE H0.
   move/(fun x => @min_stab_min a _ x x0') => H1.
   suff: false by [].
   move: (@ltn_pmod x _ (min_stab_gt0 a)).
   by rewrite ltnNge H1.
  move/negP/negP: x0'; rewrite /= eq_sym => /dvdnP [] ? ->;
  by rewrite modnMl.
Qed.

Lemma min_stab_neq1 a y :
y \in stab a -> 0 != y ->
one_ord \notin pred_of_set (stab a) -> min_stab a == 1%N = false.
Proof.
  move=> Hy Hy' H; apply/eqP/eqP; move: H; apply: contra => /eqP H.
  have->: one_ord = min_stab_ord a by apply/val_inj; rewrite /= H.
  rewrite inE /=.
  move: (@min_stab_cond a 1 y Hy Hy').
  by rewrite mul1n.
Qed.

Lemma min_stab_attain :
  p_ord \in stab t -> min_stab t == (2 ^ m - 1)%N ->
forall l k : nat, t ^+ l * t = t ^+ k * t -> k = l %[mod 2 ^ m - 1].
Proof.
move=> H1 H3.
have H2: t ^+ (2 ^ m) == t
 by move: H1; rewrite inE /= -GRing.exprSr subn1 prednK.
have base: forall l, (0 < l < 2 ^ m - 1)%N -> t ^+ l * t != t.
 move/eqP: H3 => H l /andP [] Hl0 Hl; apply/negP => /eqP C.
  have Hl': (l < (2 ^ m).+1)%N.
   by apply (ltn_trans Hl).
  have: Ordinal Hl' \in enum (stab t)
   by rewrite mem_enum inE /= C.
  have Hl2: (l < 2 ^ m - 1)%N.
   by apply/(leq_trans Hl).
  rewrite lt0n eq_sym in Hl0.
  rewrite mem_enum.
  move/min_stab_min.
 by rewrite /= Hl0 H leqNgt Hl2 => /implyP.
have base1: 
  forall l k, (l < 2 ^ m - 1 -> 0 < k < 2 ^ m - 1 ->
  (t ^+ l * t = t ^+ k * t)%R -> k = l)%N.
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
   apply/andP; split.
    by rewrite lt0n subn_eq0 -ltnNge.
   by apply/(leq_ltn_trans (leq_subr _ _)).
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
  apply/andP; split.
   by rewrite lt0n subn_eq0 -ltnNge.
  by apply/(leq_ltn_trans (leq_subr _ _)).
 move/base => + lk.
 rewrite addnC GRing.exprD -GRing.mulrA -lk GRing.mulrA -GRing.exprD subnK //.
  by rewrite subn1 -GRing.exprSr prednK // H2.
 by rewrite ltnW.
have base2: 
  forall l k : nat, (0 < k < 2 ^ m - 1)%N ->
  t ^+ l * t = t ^+ k * t -> (k = l %% (2 ^ m - 1))%N.
  move=> l k /base1 b.
  rewrite [X in (_ ^+ X * _)%R](divn_eq l (2 ^ m - 1)) addnC GRing.exprD
          -GRing.mulrA.
  move/eqP: H3 (min_stab_cond (l %/ (2 ^ m - 1)) H1 predpower_neq0) =>
            -> /eqP -> /b; apply.
  by rewrite ltn_mod.
move=> l k.
rewrite (divn_eq k (2 ^ m - 1)) addnC GRing.exprD -GRing.mulrA.
move: (min_stab_cond (k %/ (2 ^ m - 1)) H1 predpower_neq0).
move/eqP: (H3) => -> /eqP ->.
rewrite addnC modnMDl modn_mod.
case k0: (k %% (2 ^ m - 1))%N.
 case l0: (l %% (2 ^ m - 1))%N => //.
 rewrite (divn_eq l (2 ^ m - 1)) addnC GRing.exprD -GRing.mulrA.
 move: (min_stab_cond (l %/ (2 ^ m - 1)) H1 predpower_neq0).
 move/eqP: (H3) => -> /eqP -> /esym/base2.
 by rewrite ltn_mod l0 /= mod0n => ->.
move/base2.
by rewrite /= -k0 ltn_mod; apply.
Qed.

Lemma map_pi_inj :
(forall l k : nat, t ^+ l * t = t ^+ k * t -> k = l %[mod 2 ^ m - 1])
-> injective (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => t ^+ x * t).
Proof.
  move=> H x y /eqP.
  rewrite eqE /= => /eqP /H.
  case: y => y yH.
  case: x => x xH.
  rewrite !modn_small //=.
  by move=> yx; apply/val_inj.
  apply: (leq_trans xH); by rewrite prednK.
  apply: (leq_trans yH); by rewrite prednK.
Qed.

Lemma Xn_phi_neq0 (a : nat) :
(forall l k : nat, t ^+ l * t = t ^+ k * t -> k = l %[mod 2 ^ m - 1])
-> t ^+ a * t != 0.
Proof.
  move=> H0; apply/negP => /eqP Hc.
  move: (H0 a a.+1).
  rewrite GRing.exprS -GRing.mulrA Hc GRing.mulr0 => /(_ erefl)/eqP.
  rewrite (divn_eq a (2 ^ m - 1)) -addnS !modnMDl.
  by apply/negP/lem1 => //; rewrite ltn_mod.
Qed.
End order.

Lemma map_pi_card :
(forall l k : nat, (pi 'X ^+ l * pi 'X = pi 'X ^+ k * pi 'X)%R
             -> k = l %[mod 2 ^ m - 1])
-> #|image (fun (x: [ringType of 'Z_(2 ^ m - 1)])
           => pi ('X ^ x * 'X)%R) 'Z_(2 ^ m - 1)| = (2 ^ m - 1)%N.
Proof.
  move=> /map_pi_inj H.
  have Hc : #|'Z_(2 ^ m - 1)| = 2 ^ m - 1.
   rewrite card_ord.
   by case: (2 ^ m - 1) pm => [][].
  rewrite -[RHS]Hc.
  apply/eqP/image_injP => x y Hx Hy.
  rewrite !GRing.rmorphM !GRing.rmorphX.
  apply H.
Qed.

Lemma map_piE :
p_ord \in stab (pi 'X : {qpoly phi})%R (pi 'X)%R ->
(min_stab (pi 'X : {qpoly phi})%R (pi 'X)%R == (2 ^ m - 1)%N)%R ->
image (fun (x: [ringType of 'Z_(2 ^ m - 1)])
         => pi ('X ^ x * 'X)%R) 'Z_(2 ^ m - 1)
=i (finset {qpoly phi} :\ (0 : {qpoly phi})%R).
Proof.
 move=> H1 H3; move: (min_stab_attain H1 H3) => H.
 move/map_pi_card: (H) => Hc.
 apply/subset_cardP.
 by rewrite cardsDS /= ?sub1set ?inE // cardsT Hc card_npoly card_ord /m cards1.
 suff: codom (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => pi ('X ^ x * 'X)%R)
       \subset (finset {qpoly phi} :\ (0 : {qpoly phi})%R)
  by apply/subset_trans/subsetP/image_codom.
 apply/subsetP => x.
 rewrite codomE !inE /=.
 elim: (enum 'Z_(2 ^ m - 1)) => // a l IH.
 rewrite in_cons => /orP [/eqP ->|/IH -> //].
 move: (Xn_phi_neq0 a H).
 by rewrite -!GRing.rmorphX -!GRing.rmorphM -!exprnP andbT !eqE.
Qed.

Lemma map_piP q :
(forall l k : nat, (pi 'X ^+ l * pi 'X)%R = (pi 'X ^+ k * pi 'X)%R
              -> k = l %[mod 2 ^ m - 1])
-> reflect (exists (r : 'Z_(2 ^ m - 1)), pi ('X ^ r * 'X)%R = q)
(q \in (image (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => pi ('X ^ x * 'X)%R)
'Z_(2 ^ m - 1))).
Proof.
move/map_pi_inj => inj.
apply/(iffP idP).
* rewrite /image_mem.
  elim: (enum 'Z_(2 ^ m - 1)) => // a l IH.
  rewrite in_cons => /orP [/eqP ->|/IH //]; by exists a.
* case => q0 <-.
  rewrite mem_image // => x y.
  rewrite ?(GRing.rmorphM, GRing.rmorphX).
  apply/inj.
Qed.

Lemma X2m_eqXE : 
(('X ^ (2 ^ m)%N %% phi == 'X %% phi) = (p_ord \in stab (pi 'X) (pi 'X)))%R.
by rewrite inE -!GRing.rmorphX -!GRing.rmorphM -!exprnP !eqE /=
           -GRing.exprSr subn1 prednK.
Qed.

Lemma X2_neqXE : 
(('X ^ 2 %% phi != 'X %% phi) = (one_ord \notin stab (pi 'X) (pi 'X)))%R.
by rewrite inE -!GRing.rmorphX -!GRing.rmorphM -!exprnP !eqE /=
           -GRing.exprSr.
Qed.

Section direct.
Variable H1 : ('X ^ 2 %% phi)%R != ('X %% phi)%R.
Variable H2 : ('X ^ (2 ^ (size phi).-1)%N %% phi)%R == ('X %% phi)%R.
Lemma irreducibleP_direct : irreducible_poly phi.
Proof.
  have H: (p_ord \in stab (pi 'X) (pi 'X))%R by rewrite -X2m_eqXE.
  case/min_stab_dvd: (H) pm => + /primeP [] o pm' => /pm' {pm'}.
  have: (one_ord \notin stab (pi 'X) (pi 'X))%R by rewrite -X2_neqXE.
  move/(@min_stab_neq1 _ _ _ _ H) => -> // x2m1.
  apply/irreducibleP/andP; split => //.
  apply/forallP => q; apply/implyP.
  case q0: (size q == 0); first by move/eqP: q0 => ->.
  move: (min_stab_attain H x2m1) => H0.
  have: q \in (finset {qpoly phi} :\ (0 : {qpoly phi})%R).
   rewrite !inE andbT.
   apply/negP => /eqP T; move: T q0 => ->.
   by rewrite size_polyC eqxx.
  rewrite -!map_piE //.
  case/(map_piP _ H0) => q1 <-.
  have pq0: forall q1 : nat, pi ('X ^ q1 * 'X)%R != 0%R
   by move=> *; rewrite !GRing.rmorphM !GRing.rmorphX Xn_phi_neq0.
  case/Pdiv.RingMonic.rdvdpP => [|x pxp]; first by apply/f2p_monic/pq0.
  case x0: (x == 0)%R.
   move/eqP: x0 pxp phi_neq0 => ->.
   rewrite GRing.mul0r => <-.
   by rewrite eqxx.
  have/dvdp_leq: (x %| phi)%R by rewrite pxp dvdp_mulr.
  rewrite phi_neq0 => /implyP.
  rewrite leq_eqVlt => /orP [/eqP|] xp.
   have: size phi = size (x * pi ('X ^ q1 * 'X))%R by rewrite -pxp.
   rewrite size_mul ?x0 ?pq0 // xp => /eqP.
   by rewrite -subn1 -[X in X == _]addn0 -addnBA ?lt0n ?size_poly_eq0
              ?pq0 // eqn_add2l eq_sym subn_eq0.
  have xx: x = pi x by rewrite /= modp_small.
  have: pi phi == pi (x * pi ('X ^ q1 * 'X))%R by rewrite -pxp.
  have: (pi x)%R \in (finset {qpoly phi} :\ (0 : {qpoly phi})%R)
   by rewrite !inE andbT eqE /= -size_poly_eq0 modp_small //
           ?ltn_size_polyC_X ?size_polyC size_poly_eq0 x0.
  rewrite GRing.rmorphM -!map_piE //.
  case/(map_piP _ H0) => x1 <-.
  rewrite -GRing.rmorphM eqE /= modpp modp_mul
          GRing.mulrCA !GRing.mulrA -GRing.exprD GRing.mulrC
          GRing.mulrA -GRing.exprS eq_sym => /negPn.
  by rewrite pq0.
Qed.
End direct.
  
Section inverse.
(*
   This direction is trivial.
   Because the statement just says that the galois group is nontrivial.
*)
Variable ip : irreducible_poly phi.

Lemma piX_neq0 : pi 'X%R != 0%R.
Proof.
  apply/negP => /eqP /(f_equal val).
  rewrite /= modp_small ?size_polyX // => /eqP.
  by rewrite -size_poly_eq0 size_polyX.
Qed.

Definition qpoly_fieldType_phi := Eval hnf in qpoly_fieldType ip.

Definition Xu: ((pi 'X : qpoly_fieldType_phi) \is a GRing.unit)%R.
  by rewrite GRing.unitfE piX_neq0.
Defined.

Definition L : fieldExtType [finFieldType of 'F_2].
  by case/irredp_FAdjoin: ip.
Defined.

Definition dL : \dim (fullv : {vspace L}) = (size phi).-1.
  rewrite /L.
  by case/irredp_FAdjoin: ip.
Defined.

Definition z : L.
  rewrite /L.
  by case/irredp_FAdjoin: ip => ?? [].
Defined.

Definition zsp : root (map_poly (GRing.in_alg L) phi) z.
  rewrite /z /L /=.
  by case/irredp_FAdjoin: ip => ?? [].
Defined.

Definition sL : <<1; z>>%VS = (fullv : {vspace L}).
  rewrite /z /L /=.
  by case/irredp_FAdjoin: ip => ?? [].
Defined.

Definition e0 : {qpoly phi} -> L
  := (fun g => (map_poly (GRing.in_alg L) g).[z])%R.

Definition rme : rmorphism (e0 : qpoly_fieldType_phi -> _).
  rewrite /e0; repeat constructor.
   * move=> x y.
     by rewrite /= !GRing.rmorphB hornerD hornerN.
   * move=> x y.
     rewrite /= -hornerM -GRing.rmorphM.
     set T := (_ * _)%R.
     rewrite [in RHS](divp_eq T phi) GRing.rmorphD hornerD GRing.rmorphM hornerM.
     move/rootP: zsp => ->.
     by rewrite GRing.mulr0 GRing.add0r.
   * by rewrite /= modp_small ?GRing.rmorph1 ?hornerC // size_polyC.
Defined.

Definition e := RMorphism rme.

Lemma inje: injective e. Proof. by apply GRing.fmorph_inj. Qed.

Lemma a1f: agenv ([aspace of 1%AS] : {subfield L}) = fullv -> False.
Proof.
 have K1: ((\sum_(i < (size phi).-1)
       ([aspace of 1%AS] : {subfield L}) ^+ i)%VS = 1%VS).
  have: (size phi).-1 != 0 by [].
  elim: (size phi).-1 => // n IHn _.
  rewrite big_ord_recr expv1n /=.
  case n0: (n == 0).
   move/eqP: n0 => ->.
   by rewrite big_ord0 add0v.
  by rewrite IHn ?n0 // addvv.
 rewrite /agenv dL K1.
 move: dL => + f1.
 rewrite -f1 dimv1 => p1.
 by move: p1 m_is_prime => <-.
Qed.

Local Hint Resolve Xu : core.

Lemma piX2X : (pi ('X ^ 2) != pi 'X)%R.
Proof.
   set fT := qpoly_fieldType_phi.
   apply/negP => /eqP /(f_equal (fun x => (pi 'X : fT)^-1 * x))%R.
   rewrite GRing.mulVr //.
   have ->: (pi ('X ^ 2) = (pi 'X : fT) * (pi 'X : fT))%R.
    rewrite -exprnP GRing.exprS GRing.expr1 GRing.rmorphM.
   by apply/val_inj.
   rewrite GRing.mulKr // => /(f_equal e) z1; move: z1 sL.
   rewrite /e /e0 /= !modp_small ?size_polyC ?size_polyX //
           map_polyC hornerC map_polyX hornerX /= GRing.scale1r => ->.
   by rewrite addvv => /a1f.
Qed.

Definition piX := FinRing.unit [finFieldType of qpoly_fieldType_phi] Xu.

Lemma piX_order : #[piX]%g = 2 ^ m - 1.
Proof.
  have/cyclic.order_dvdG: piX \in
      [group of [set: {unit [finFieldType of qpoly_fieldType_phi]}]]
    by rewrite inE.
  rewrite card_finField_unit card_npoly card_ord.
  case/primeP: pm => _.
  rewrite !subn1 => H /H {H} /orP [|/eqP] //.
  rewrite order_eq1 => piX1.
  move: piX1 piX2X;
  rewrite /piX GRing.rmorphX !eqE /= !eqE /= => /eqP ->.
  (* TODO : fix canonical structure *)
  by rewrite !modp_small ?GRing.mulr1 ?size_polyC ?eqxx.
Qed.

Lemma val_piX_expE p : val (piX ^+ p)%g = pi ('X ^+ p)%R.
Proof.
  elim: p => [|p IHp].
   by apply/val_inj.
  rewrite !GRing.exprS GRing.rmorphM expgS /= IHp.
  by apply/val_inj.
Qed.

Lemma X2mp_eq1 : (pi ('X ^+ (2 ^ m - 1)) = 1)%R.
Proof.
  suff/(f_equal val): (piX ^+ (2 ^ m - 1))%g = 1%g.
   rewrite val_piX_expE /= => ->.
   by apply/val_inj.
  suff<-: #[piX]%g = 2 ^ m - 1 by rewrite expg_order.
  by rewrite piX_order.
Qed.

Lemma irreducibleP_inverse :
(('X ^ 2 %% phi != 'X %% phi) && ('X ^ (2 ^ m)%N %% phi == 'X %% phi))%R.
Proof.
  apply/andP; split; first by move: piX2X; rewrite eqE.
  suff/(f_equal val) /= ->: (pi ('X ^ (2 ^ m)%N) = (pi 'X))%R by [].
  move: X2mp_eq1; rewrite GRing.rmorphX => H.
  have->: 2 ^ m = (2 ^ m - 1).+1 by rewrite subn1 prednK.
  by rewrite GRing.rmorphX GRing.exprS H GRing.mulr1.
Qed.

Definition mulV (V : [ringType of {qpoly phi}]) v := (v * V)%R.

Lemma linear_mulV V : linear (mulV V).
Proof.
  move=> a x y.
  case: a => [][|[]//] i; set T := Ordinal i.
   have->: T = 0%R by apply/val_inj.
   by rewrite !GRing.scale0r !GRing.add0r.
  have->: T = 1%R by apply/val_inj.
  by rewrite !GRing.scale1r /mulV GRing.mulrDl.
Qed.

Canonical linearType_mulV V := Eval hnf in Linear (linear_mulV V).

Definition mulX := mulV (pi 'X)%R.

Lemma expXpE p : iter p mulX =1 mulV (pi 'X ^+ p)%R.
Proof.
  elim: p => [x|p IHp x].
   by rewrite /= GRing.expr0 /mulV GRing.mulr1.
  by rewrite iterS IHp GRing.exprS /mulX /mulV
  -GRing.mulrA -GRing.rmorphX -GRing.rmorphM GRing.mulrC GRing.rmorphM.
Qed.

Lemma cycleX_dvdP p : reflect (iter p mulX =1 id) (2 ^ m - 1 %| p).
Proof.
  apply/(iffP idP).
  * case/dvdnP => q -> x.
    rewrite (coord_basis (npolyX_full _ _) (memvf x)).
    set e0 := npolyX _ _.
    have->: (\sum_i coord e0 i x *: e0`_i)%R
          = (\sum_(i <- ord_enum (size phi).-1) coord e0 i x *: e0`_i)%R.
     rewrite -big_image_id big_image.
     apply congr_big => //. by rewrite /index_enum unlock.
    rewrite GRing.linear_sum. apply/eq_big => // i _.
    by rewrite GRing.linearZ_LR /= expXpE mulnC GRing.exprM -GRing.rmorphX
               X2mp_eq1 /mulV GRing.expr1n GRing.mulr1.
  * move/(fun x => x 1%R).
    rewrite expXpE /mulV GRing.mul1r -X2mp_eq1
            -GRing.rmorphX -!val_piX_expE => /val_inj/eqP.
    by rewrite cyclic.eq_expg_mod_order piX_order modnn.
Qed.

Lemma cycleX : iter (2 ^ m - 1) mulX =1 id.
Proof. by apply/cycleX_dvdP. Qed.

(* Variable B : @matrix [fieldType of 'F_2] (size phi).-1 (size phi).-1. *)
(* Variable HB : char_poly B = phi. *)

Definition mulX' :
  @matrix [fieldType of 'F_2] (size phi).-1 (size phi).-1.
apply: (castmx (mul1n _, mul1n _)).
(* rewrite prednK //. *)
by apply (lin_mx (fun x => npoly_rV (mulX (rVnpoly x)))).
Defined.

(*               \matrix_(i < (size phi).-1, j < (size phi).-1) ((i : nat) == j.+1 : [fieldType of 'F_2]))%R. *)
(* Check lin_mx. *)
(* Check lin_mx (fun x : 'rV_(size phi).-1 => npoly_rV ((rVnpoly x : {qpoly phi}) * pi 'X)%R). *)
(* Check (\matrix_(i < (size phi).-1, j < (size phi).-1) ((if (i : nat) == j.+1 then 1 else 0) : [fieldType of 'F_2]))%R. *)
(* Check castmx (mul1n _, mul1n _). *)

Lemma polyXnE (R : ringType) n m : n < m -> ('X^n = \poly_(k < m) ((k == n)%:R : R))%R.
  move=> nm.
  apply/polyP => s.
  rewrite coefXn coef_poly.
  case sm: (s == m).
   move/eqP: sm => ->.
   by rewrite ltnn gtn_eqF.
  case: ifP => //.
  by move/negP/negP; rewrite -leqNgt; move/(leq_trans nm) => /gtn_eqF ->.
Qed.
  (* rewrite ltnNge. *)
  (* move/leq *)
  (*   by rewrite ltnS leqnn. *)
  (* elim: m n => // m IHm n. *)
  (* rewrite ltnS leq_eqVlt => /orP[/eqP ->|]. *)
  (*  apply/polyP => s. *)
  (*  rewrite coefXn coef_poly. *)
  (*  case sm: (s == m). *)
  (*   move/eqP: sm => ->. *)
  (*   by rewrite ltnS leqnn. *)
  (*  by case: ifP. *)
  (* elim: {IHm} m => //. *)
  (*  rewrite  *)
  (* move=> nm. *)
  (* set T := ('X^_)%R. *)
  
  (*       match insub k with *)
  (*                                | Some i0 => (\matrix[vec_mx_key]_(i1, j0) (\matrix[delta_mx_key]_(i2, j1) ((i2 == 0) && (j1 == cast_ord (esym (mul1n (size phi).-1)) (Ordinal Hi)))%:R) 0 (mxvec_index i1 j0)) 0 i0 *)
  (*                                | None => 0 *)
  (*                                end)%R *)
Lemma test : (mulX' = \matrix_(i < (size phi).-1, j < (size phi).-1) (((i : nat) == j.+1)%:R : [fieldType of 'F_2]))%R.
(* Lemma test : (castmx (mul1n _, mul1n _) (lin_mx (fun x => npoly_rV ((rVnpoly x : {qpoly phi}) * pi 'X)%R)) = \matrix_(i < (size phi).-1, j < (size phi).-1) (((i : nat) == j.+1)%:R : [fieldType of 'F_2]))%R. *)
Proof.
  rewrite /mulX'.
  apply/matrixP => i j.
  rewrite !castmxE /lin_mx /lin1_mx !mxE /mxvec !castmxE !mxE /=.
  set T := rVnpoly _.
  have <-: ('X ^+ i)%R = T.
   subst T.
   case: i => i Hi. case: j => j Hj.
   rewrite /delta_mx /vec_mx /rVnpoly /rVpoly /=.
   apply/val_inj.
   rewrite val_insubd.
   case: ifP => H.
   rewrite (@polyXnE _ _ (size phi).-1 _) //.
   Admitted.
   
  (*  rewrite /=. *)
  (*  apply polyP. *)
  (*  polyP. *)
  (*  apply congr_big. *)
  (*  congr (val (\poly_(k < (size phi).-1) _)%R). *)
  (*  move=> t. *)
  (*  apply/polyP. *)
  (*  rewrite polyP. *)
  (*  rewrite /=. *)
  (*  set T := (\poly_(k < (size phi).-1) match insub k with *)
  (*                                | Some i0 => (\matrix[vec_mx_key]_(i1, j0) (\matrix[delta_mx_key]_(i2, j1) ((i2 == 0) && (j1 == cast_ord (esym (mul1n (size phi).-1)) (Ordinal Hi)))%:R) 0 (mxvec_index i1 j0)) 0 i0 *)
  (*                                | None => 0 *)
  (*                                end)%R. *)
  (*  have->: (T = val T) by []. *)
  (*  rewrite npoly_is_a_poly_of_size. *)
  (*  rewrite isE. *)
  (*  rewrite memE. *)
  (*  rewrite /=. *)
  (*  rewrite /insubd /odflt /oapp. *)
   
  (*  apply/val_inj. *)
  (*  rewrite /=. *)
  (* Check @ord0 (size phi).-1. *)
  (* suff H: forall i0, ((\matrix[vec_mx_key]_(i1, j) (\matrix[delta_mx_key]_(i2, j0) ((i2 == 0) && (j0 == cast_ord (esym (mul1n (size phi).-1)) (Ordinal Hi)))%:R) 0 (mxvec_index i1 j)) (@ord0 0) i0 = ((if (i0 : nat) == i then 1 else 0) : [fieldType of 'F_2]))%R. *)
  (* rewrite H. *)
  (* move=> ->. *)
  (*  move=> n i0. *)
  (*  rewrite !mxE eqxx eqE /=. *)
  (*  have: (val (enum_rank (ord0, i0)) = i0). *)
  (*   case: i0 => i0 Hi0 n0. *)
  (*   rewrite /enum_rank /enum_rank_in val_insubd /=. *)
  (*   case: ifP => H. *)
  (*   rewrite predX_prod_enum. *)
  (*    rewrite /index. *)
  (*   set T := (fun => true). *)
  (*   have: #|T| > 0 by have/enum_rank_subproof: (ord0, Ordinal Hi0) \in T by []. *)
    
  (*    rewrite cardE. *)
  (*    rewrite size_enum_ord. *)
  (*    Search (size (enum _)). *)
  (*    rewrite  *)
  (*    rewrite enum. *)
  (*   rewrite /=. *)
  (*   rewrite enumX. *)
  (*   rewrite -cardX. *)
  (*   rewrite /=. *)
  (*   rewrite /=. *)
  (*   rewrite card1. *)
  (*   rewrite size_ord. *)
  (*   rewrite  *)
  (*   rewrite  *)
  (*   rewrite enum. *)
  (*   rewrite sizeenumE. *)
  (*  rewrite /ord0 /=. *)
  (*  rewrite /=. *)
  (*  Check (index _ (enum _)). *)
  (*  Check Ordinal. *)
  (*  rewrite enum_rank_subproof. *)
  (*  case ii: (i == i0). *)
  (*   rewrite [in RHS]eq_sym ii. *)
  (*   apply/eqP. *)
  (*   rewrite eqE /= /modn /=. *)
  (*   Check enum_val Hi. *)
  (*   rewrite enum_rankK. *)
  (*    move=> n0. *)
  (*    rewrite /enum_rank /enum_rank_in. *)
  (*    rewrite /= /index. *)
  (*    rewrite /find. *)
  (*    rewrite /=. *)
  (*    rewrite eqE. *)
  (*    rewrite /=. *)
  (*    apply/eqP. *)
  (*    apply enum_val_inj. *)
  (*    rewrite /=. *)
  (*   set T' :=  *)
  (*   set T := i. *)
  (*   rewrite eq_sym. *)
  (*   have: ((enum_rank (ord0, i0) == (i : ordinal_subType _))%:R)%R. *)
  (*    :  *)
  (*   apply (sameP ((enum_rank (ord0, i0) == i)%:R)%R). *)
  (*   apply/idP. *)
  (*   rewrite eqE. *)
  (*   apply is_true. *)
  (*   rewrite /=. *)
  (*   apply/eqP. *)
  (*   apply/implyP. *)
  (*   apply/eqP. *)
  (*   apply/boolP. *)
  (*   rewrite eqE /=. *)
  (*   rewrite modn1. *)
  (*   GRing.mul1r *)
  (*   rewrite  *)
  (*   apply/boolP. *)
  (*   rewrite eq_sym ii. *)
  (*   rewrite /enum_rank /enum_rank_in. *)
  (*   rewrite /=. *)
  (*   rewrite /=. *)
  
  (* Check forall i0, ((\matrix[vec_mx_key]_(i1, j) (\matrix[delta_mx_key]_(i2, j0) ((i2 == 0) && (j0 == cast_ord (esym (mul1n (size phi).-1)) (Ordinal Hi)))%:R) 0 (mxvec_index i1 j)) (@ord0 0) i0 = ((if (i : nat) == j then 1 else 0) : [fieldType of 'F_2]))%R. *)
  (* case ij: ((i : nat) == j.+1). *)
  (*  set T := insub _. *)
  (*  have: T != None. *)
  (*   subst T. *)
  (*   apply/eqP => H. *)
  (*   move: (H) => /insubP. *)
  (*   apply/eqP. *)
  (*   move=> S. *)
  (*   => /val_inj. *)
  (*   move/eqP: ij. *)
  (*   apply/val_inj. *)
  (*   rewrite /insub. *)
   
  (* rewrite nth_default. *)
  (* rewrite mxE. *)
  
  (* Check coef_poly. *)
  (* Check nth *)
  (* rewrite nth_poly. *)
  (* have<-: (Ordinal Hj) = (enum_val (cast_ord (esym (mxvec_cast 1 (size phi).-1)) (cast_ord (esym (mul1n (size phi).-1)) (Ordinal Hj)))).2. *)
  (*  apply val_inj. *)
  (*  rewrite /mxvec_cast. *)
  (*  rewrite cast_ordK. *)
  (*  rewrite /cast_ord /enum_val. *)
  (*  rewrite cast_ord_proof. *)
  (*  rewrite /enum_default. *)
  (*  rewrite castmxE. *)
  (*  rewrite mxcastK. *)
   
  (*  rewrite /=. *)
  (*  rewrite /=. *)
  (*  rewrite enum_val. *)
   
  (* rewrite mxE. *)
  (* rewrite cast_ordK. *)
  (* Check cast_ord. *)
  (* rewrite /rVnpoly /rVpoly /insubd /odflt /oapp /= . *)
  (* rewrite /snd /= /enum_val. *)
  (* rewrite /enum_val /=. *)

Lemma char_phi : char_poly mulX' = phi.
Proof.
  rewrite test.
  rewrite /mulX' /ssr_have /mulX /mulV /GRing.mul
          /GRing.Ring.mul /mul_qpoly /rVnpoly /npoly_rV.
  rewrite /poly_rV /rVpoly /insubd /insub /odflt /oapp /=.
  destruct idP.
  
  rewrite GRing.mulrC.
  rewrite -modp_mod.
  move sp: (size phi) => spe.
  rewrite /mulX'.
  rewrite /char_poly /char_poly_mx /map_mx /lin_mx.
  
  destruct phi.
  case: phi .
  rewrite /mulX' /char_poly /char_poly_mx /map_mx /lin_mx /lin1_mx.
  rewrite /vec_mx /mxvec /ssr_have /=.
  case: phi pm ip.
  rewrite castmxE.
  set T := (\matrix[_]_(_, _) _ _ _)%R.
  have: T = T.
   rewrite /T.
   apply/matrixP => i j.
   rewrite mxE /delta_mx /vec_mx /rVnpoly /poly_nil.
   set S := (\matrix[_]_(_, _) _ _ _)%R.
   have: S = S.
    rewrite /S.
    apply/matrixP => ? ?.
    rewrite !mxE /=.
    rewrite !castmxE .
    Check lin_mulmx.
    rewrite rowE.
    rewrite /=.
     apply/matrixP.
    set R := (\matrix[_]_(_, _) _ _ _)%R.
    have: R = R.
     rewrite /R.
     apply/matrixP => [][]??[]??.
     rewrite mxE /= /npoly_rV /=.
     rewrite /poly_rV /=.
     rewrite /enum_val.
     rewrite /=.
     rewrite rowE.
     rewrite /nth.
     rewrite /=.
     apply/rowP.
     apply/matrixP.
     rewrite rowE.
     apply/rowP => [][] /= ??.
     apply/rowP => [][] /= ??.
     rewrite /=.
     rewrite rowK.
    rewrite /=.
    rewrite rowE.
    rewrite /mxvec /=.
   set S := \
   rewrite /=.
   rewrite /=.
   rewrite /insubd /odflt /oapp.
   rewrite /insub.
   rewrite /=.
   apply/matrixP => i j.
   apply: eq_big.
   congr : \matrix[_](_, _).
  rewrite /=.
  rewrite /= /rVpoly /=.
  apply GRing.subr0_eq.
  rewrite /char_poly /char_poly_mx /map_mx /lin_mx /lin1_mx.
  rewrite /= mxE.
  rewrite -GRing.subrr.
  rewrite GRing.oner_eq0.
  rewrite /mulX /mulV.
  rewrite /npoly_rV /rVnpoly.
  set T := (fun _ : 'rV__ => _).
  have: T =1 T.
   rewrite /T => x.
   rewrite /= modp_mul.
   rewrite GRing.rmorphM.
   rewrite /rVpoly.
  apply/etrans.
    (fun x => char_poly (lin_mx x)).
  
  (* set T' := (fun x => insubd _ (rVpoly x)). *)
  (* rewrite /=. *)
  set Z := 0%R.
  (* (fun x => poly_rV (((insubd Z (rVpoly x) : npoly_subType (size phi).-1) * 'X) %% phi))%R. *)
  
  (* pose T' := (fun x => insubd Z (rVpoly x) : npoly_subType (size phi).-1). *)
   set T' := insubd _ _.
   set T' := 0%R.
   Set Printing All.
   done.
   rewrite 
   rewrite /=.
   done.
  rewrite /npoly_rV.
  rewrite GRing.rmorphM.
  rewrite /=.
Lemma char_phi : char_poly mulX' = phi.

Lemma char_phi B : char_poly B = phi -> similar mulX' B.
Proof.
  
Check mx_inv_horner.
Check lin_mx (fun x => npoly_rV (mulX (rVnpoly x))).

(* Check poly_rV _. *)
(* Check rVpoly . *)
(* Check (fun x => npoly_rV (mulX (rVnpoly x))). *)
(* Check char_poly. *)
(* TODO : prove mulX and matrix B are similar. *)
End inverse.

Lemma irreducibleP :
reflect (irreducible_poly phi)
(('X ^ 2 %% phi != 'X %% phi) && ('X ^ (2 ^ m)%N %% phi == 'X %% phi))%R.
Proof.
  apply/(iffP idP).
   by case/andP; apply irreducibleP_direct.
  by apply irreducibleP_inverse.
Qed.
End irreducibility.
