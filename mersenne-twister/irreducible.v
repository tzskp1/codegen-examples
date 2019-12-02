From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
Require Import polyn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ext.
Variable R : fieldType.
Implicit Types (p : {poly R}) (c : R) (n : nat).

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

Import GRing.Theory.
Local Open Scope ring_scope.

Lemma ltn_size_polyC_X c p : p != 0 -> (size (c%:P) < size (p * 'X)%R)%N.
Proof.
move=> ?; rewrite size_mul ?polyX_eq0 // size_polyX size_polyC addn2.
case: (c != 0) => //.
by rewrite ltnS lt0n size_poly_eq0.
Qed.

Lemma polyX_neq0 : ('X : {poly R}) != 0.
Proof. by rewrite -size_poly_eq0 size_polyX. Qed.

Hint Resolve ltn_size_polyC_X polyX_neq0 : core.

Lemma polyXn_eq0 n : (('X^n : [ringType of {poly R}]) == 0) = false.
Proof. by rewrite -size_poly_eq0 size_polyXn. Qed.
End ext.

Section irreducibility.
Variable phi : {poly [finFieldType of 'F_2]}.
Local Notation m := (size phi).-1.
Hypothesis pm : prime (2 ^ m - 1).

Lemma exp2_dvd a b :
  2^(a * b) - 1 = (2^a - 1) * \sum_(i < b) 2 ^ (a * (b - i.+1)).
Proof.
elim: b => [|b IHb]; first by rewrite muln0 expn0 subn1 big_ord0 muln0.
rewrite big_ord_recl mulnDr -IHb mulnBl !subn1 -mulnBl mulnS expnD.
have H: forall a, 2 ^ a = 2 ^ a - 1 + 1 by move=> *; rewrite subnK // expn_gt0.
by rewrite [in LHS]H mulnDl mul1n [X in _ + X]H addn1 !addnS !subn1.
Qed.

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
  rewrite addnC GRing.exprD -GRing.mulrA lk GRing.mulrA -GRing.exprD .
  rewrite subnK //.
  by rewrite subn1 -GRing.exprSr prednK // H2.
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
 rewrite addnC GRing.exprD -GRing.mulrA -lk GRing.mulrA -GRing.exprD .
  rewrite subnK //.
  by rewrite subn1 -GRing.exprSr prednK // H2.
 by rewrite ltnW.
have base2: 
  forall l k : nat, (0 < k < 2 ^ m - 1)%N ->
  t ^+ l * t = t ^+ k * t -> (k = l %% (2 ^ m - 1))%N.
  move=> l k /base1 b.
  rewrite [X in (_ ^+ X * _)%R](divn_eq l (2 ^ m - 1)).
  rewrite addnC GRing.exprD -GRing.mulrA.
  move: (min_stab_cond (l %/ (2 ^ m - 1)) H1 predpower_neq0).
  move/eqP: H3 => -> /eqP -> /b; apply.
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

Lemma f2p_monic (p : {poly [finFieldType of 'F_2]}) :
  (p != 0)%R -> p \is monic.
Proof.
  move=> /negPf p0; apply/eqP.
  case lp0: (lead_coef p == 0)%R.
   by rewrite lead_coef_eq0 p0 in lp0.
  case: (lead_coef p) lp0 => [][]//[]// *.
  by apply/val_inj.
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

Lemma irreducibleP :
reflect (irreducible_poly phi)
(('X ^ 2 %% phi != 'X %% phi) && ('X ^ (2 ^ m)%N %% phi == 'X %% phi))%R.
Proof.
(*
based on:
 http://www.math.sci.hiroshima-u.ac.jp/~m-mat/TEACH/0407-2.pdf
 P. 27
*)
apply/(iffP idP).
* case/andP => H1 H2.
  have H: (p_ord \in stab (pi 'X) (pi 'X))%R by rewrite -X2m_eqXE.
  case/min_stab_dvd: (H) pm => + /primeP [] o pm' => /pm' {pm'}.
  have: (one_ord \notin stab (pi 'X) (pi 'X))%R by rewrite -X2_neqXE.
  move/(@min_stab_neq1 _ _ _ _ H) => -> //= x2m1.
  apply/irreducibleP/andP; constructor => //.
  apply/forallP => q; apply/implyP.
  case q0: (size q == 0); first by move/eqP: q0 => ->.
  have: q \in (finset {qpoly phi} :\ (0 : {qpoly phi})%R).
   rewrite !inE andbT.
   apply/negP => /eqP q0'.
   move: q0' q0 => ->.
   by rewrite size_polyC eqxx.
  rewrite -!(map_piE H x2m1).
  move: (min_stab_attain H x2m1) => H0.
  case/(map_piP _ H0) => q1 <-.
  have pq0: forall q1 : nat, pi ('X ^ q1 * 'X)%R != 0%R
   by move=> q1'; rewrite !GRing.rmorphM !GRing.rmorphX Xn_phi_neq0.
  case/Pdiv.RingMonic.rdvdpP => [|x pxp]; first by apply/f2p_monic/pq0.
  case x0: (x == 0)%R.
   move/eqP: x0 pxp phi_neq0 => ->.
   rewrite GRing.mul0r => <-.
   by rewrite eqxx.
  have/dvdp_leq: (x %| phi)%R by rewrite pxp dvdp_mulr.
  rewrite phi_neq0 => /implyP /=.
  rewrite leq_eqVlt => /orP [/eqP|] xp.
   have: size phi = size (x * pi ('X ^ q1 * 'X))%R by rewrite /= -pxp.
   rewrite size_mul ?x0 ?pq0 //= xp => /eqP.
   by rewrite -subn1 -[X in X == _]addn0 -addnBA ?lt0n ?size_poly_eq0
              ?pq0 // eqn_add2l eq_sym subn_eq0.
  have xx: x = pi x by rewrite /= modp_small.
  have: pi phi == pi (x * pi ('X ^ q1 * 'X))%R by rewrite -pxp.
  have: (pi x)%R \in (finset {qpoly phi} :\ (0 : {qpoly phi})%R)
   by rewrite !inE andbT eqE /= -size_poly_eq0 modp_small //
           ?ltn_size_polyC_X ?size_polyC // size_poly_eq0 x0.
  rewrite GRing.rmorphM -!(map_piE H x2m1).
  case/(map_piP _ H0) => x1 <-.
  rewrite -GRing.rmorphM eqE /= modpp modp_mul
          GRing.mulrCA !GRing.mulrA -GRing.exprD GRing.mulrC
          GRing.mulrA -GRing.exprS eq_sym => /negPn.
  by rewrite pq0.
* (*
   This direction is trivial.
   Because the statement just says that the galois group is nontrivial.
  *)
  move=> ip; case/irredp_FAdjoin: (ip) => L dL [] z zsp sL.
  set fT := qpoly_fieldType ip.
  set e0 : {qpoly phi} -> L := (fun g => (map_poly (GRing.in_alg L) g).[z])%R.
  have rme: rmorphism (e0 : fT -> _).
   subst e0; repeat constructor.
   * move=> x y.
     by rewrite /= !GRing.rmorphB hornerD hornerN.
   * move=> x y.
     rewrite /= -hornerM -GRing.rmorphM.
     set T := (_ * _)%R.
     rewrite [in RHS](divp_eq T phi) GRing.rmorphD hornerD GRing.rmorphM hornerM.
     move/rootP: zsp => ->.
     by rewrite GRing.mulr0 GRing.add0r.
   * by rewrite /= modp_small ?GRing.rmorph1 ?hornerC // size_polyC.
  set e := RMorphism rme.
  have inje: injective e by apply GRing.fmorph_inj.
  have a1f: agenv ([aspace of 1%AS] : {subfield L}) = fullv -> False.
   have K1: ((\sum_(i < (size phi).-1)
         ([aspace of 1%AS] : {subfield L}) ^+ i)%VS = 1%VS).
    have: (size phi).-1 != 0 by [].
    elim: (size phi).-1 => // n IHn _.
    rewrite big_ord_recr expv1n /=.
    case n0: (n == 0).
     move/eqP: n0 => ->.
     by rewrite big_ord0 add0v.
    by rewrite IHn ?n0 // addvv.
   rewrite -dL in K1.
   rewrite /agenv K1.
   move: dL => + f1.
   rewrite -f1 dimv1 => p1.
   move: m_is_prime.
   by rewrite -p1.
  have piX_neq0 : pi 'X%R != 0%R.
   apply/negP => /eqP /(f_equal e).
   rewrite GRing.rmorph0.
   subst e e0.
   rewrite /= modp_small ?size_polyX // map_polyX hornerX => z0.
   move: z0 sL => ->.
   by rewrite addv0 => /a1f.
  have Xu: ((pi 'X : fT) \is a GRing.unit)%R
   by rewrite GRing.unitfE piX_neq0.
  have piX2X: (pi ('X ^ 2) != pi ('X))%R.
   apply/negP => /eqP.
   move/(f_equal (fun x => (pi 'X : fT)^-1 * x))%R.
   rewrite GRing.mulVr //.
   have ->: ((pi ('X ^ 2) : fT)
            = ((pi 'X) : fT) * ((pi 'X) : fT))%R.
    rewrite -exprnP GRing.exprS GRing.expr1 GRing.rmorphM.
    by apply/val_inj.
   rewrite GRing.mulKr // => /(f_equal e)/eqP.
   subst e e0.
   rewrite /= !modp_small ?size_polyC ?size_polyX //
           map_polyC hornerC map_polyX hornerX  /= => /eqP z1.
   rewrite GRing.scale1r in z1.
   move: z1 sL => ->.
   by rewrite /= addvv => /a1f.
  apply/andP; split; first by rewrite eqE in piX2X.
  suff: (pi ('X ^ (2 ^ m)%N) = (pi 'X))%R by move/(f_equal val) => /= ->.
  suff H: (pi 'X ^+ (2 ^ m - 1) = 1)%R.
   have->: (2 ^ m) = (2 ^ m - 1).+1 by rewrite subn1 prednK.
   by rewrite GRing.rmorphX GRing.exprS H GRing.mulr1.
  set piX := (FinRing.unit [finFieldType of fT] Xu). 
  suff: (piX ^+ (2 ^ m - 1))%g = 1%g.
   subst piX => /(f_equal val).
   rewrite !FinRing.val_unit1 !FinRing.val_unitX.
   set O := 1%R; set O' := 1%R.
   have->: O' = O by apply/val_inj.
   move=> <- /=.
   elim: (2 ^ m - 1) => [|m IHm].
    rewrite !GRing.expr0.
    by apply/val_inj.
   apply/val_inj.
   by rewrite !GRing.exprSr // IHm //.
  suff<-: #[piX]%g = 2 ^ m - 1 by rewrite expg_order.
  have/cyclic.order_dvdG: piX \in [group of [set: {unit [finFieldType of fT]}]]
    by rewrite inE.
  rewrite /= card_finField_unit card_npoly card_ord.
  case/primeP: pm => _.
  rewrite !subn1 => H /H /orP [|/eqP //].
  rewrite order_eq1 => piX1.
  move: piX2X; subst piX; move: piX1.
  rewrite GRing.rmorphX !eqE /= !eqE /= => /eqP ->.
  by rewrite !modp_small ?GRing.mulr1 ?size_polyC ?eqxx.
Qed.

Hypothesis (ip : irreducible_poly phi).

Lemma irreducible_distinct :
(forall l k : nat, pi 'X ^+ l * pi 'X = pi 'X ^+ k * pi 'X -> k = l %[mod 2 ^ m - 1])%R.
Proof.
move/irreducibleP: ip; case/andP => H1 H2.  
have H: (p_ord \in stab (pi 'X) (pi 'X))%R by rewrite -X2m_eqXE.
case/min_stab_dvd: (H) pm => + /primeP [] o pm' => /pm' {pm'}.
have: (one_ord \notin stab (pi 'X) (pi 'X))%R by rewrite -X2_neqXE.
move/(@min_stab_neq1 _ _ _ _ H) => -> //= x2m1.
apply/(min_stab_attain H x2m1).
Qed.

Definition qpoly_fieldType_phi := Eval hnf in qpoly_fieldType ip.
Lemma char2_V : 2 \in [char {qpoly phi}]%R.
Proof.
by apply/(GRing.rmorph_char pi)/(GRing.rmorph_char (polyC_rmorphism _)).
Qed.
Definition H0 : {qpoly phi} -> {qpoly phi} := Frobenius_aut char2_V.
Definition rmH : rmorphism (H0 : qpoly_fieldType_phi -> _).
  repeat constructor.
  * move=> x y.
    rewrite /H0 /= !GRing.Frobenius_autD_comm ?GRing.Frobenius_autN //.
    by apply/eqP; rewrite eqE /= GRing.mulrC.
  * move => x y.
    rewrite /H0 -GRing.Frobenius_autM_comm //.
    by apply/eqP; rewrite eqE /= GRing.mulrC.
  * apply/eqP.
    by rewrite eqE /= modp_mul GRing.mulr1 modp_mod.
Qed.
Definition H := RMorphism rmH.

Lemma dimvm : m = \dim (fullv : {vspace {qpoly phi}}).
 by rewrite dim_polyn.
Defined.

Lemma expHpE p : iter p H (pi 'X)%R = pi ('X ^ (2 ^ p)%N)%R.
Proof.
  elim: p => // p' IHp.
  rewrite -[X in (2 ^ X)%N]addn1 iterS IHp /H /H0 /= GRing.Frobenius_autE.
  set T := (qpolify phi_gt1 _).
  have ->: T = pi ('X ^ (2 ^ p')%N)%R by [].
  by rewrite -GRing.rmorphX expnD expn1 muln2 -addnn exprzD_nat GRing.expr2.
Qed.

Lemma H1E : H (pi 'X)%R = pi ('X ^ 2)%R.
Proof.
  rewrite /H /H0 /= GRing.Frobenius_autE.
  set T := (qpolify phi_gt1 _).
  have ->: T = pi 'X%R by [].
  by rewrite -GRing.rmorphX.
Qed.

Definition e0 :=
  map_tuple (fun j => (iter j H) (pi 'X))%R
            (iota_tuple (\dim (fullv:{vspace {qpoly phi}})) 0).

Lemma basis_e0 : basis_of fullv e0.
Proof.
  rewrite basisEfree size_tuple leqnn subvf !andbT.
  apply/freeP.
Admitted.

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

Lemma linH : linear H.
 move=> a x y.
 rewrite /H /= /H0.
 rewrite GRing.Frobenius_autD_comm /GRing.comm; last first.
  case: a => [][|[]//] i; set T := Ordinal i.
   have->: T = 0%R by apply/val_inj.
   by rewrite !GRing.scale0r GRing.mulr0 GRing.mul0r.
  have->: T = 1%R by apply/val_inj.
  by rewrite !GRing.scale1r
     (GRing.mulrC (x : [comRingType of [ringType of {qpoly phi}]])).
 rewrite !GRing.Frobenius_autE.
 case: a => [][|[]//] i; set T := Ordinal i.
  have->: T = 0%R by apply/val_inj.
  by rewrite !GRing.scale0r GRing.expr0n !GRing.add0r.
 have->: T = 1%R by apply/val_inj.
 by rewrite !GRing.scale1r.
Qed.

Canonical linHType := Linear linH.

Definition canon_mat' f :=
  let m := \dim (fullv : {vspace {qpoly phi}}) in
  (\matrix_(i < m , j < m) coord e0 i (f e0`_j))%R.

Definition mat_inj :
  'M['F_2]_(\dim (fullv : {vspace {qpoly phi}})) -> 'M['F_2]_m.
move=> x; apply (castmx (esym dimvm, esym dimvm) x).
Defined.

Definition canon_mat := mat_inj \o canon_mat'.

Lemma step y (x : ordinal y) : ordinal y.
  apply/(@Ordinal _ (x.+1 %% y)).
  case: x => x /= xy.
  case xy': (x.+1 == y).
   move/eqP: xy' => <-.
   by rewrite modnn.
  by rewrite modn_small ltn_neqAle xy' xy.
Defined.

Lemma sum_col_delta (R : ringType) n (f : nat -> R) j :
  (\sum_(i < n) f i * (i == j)%:R)%R = f j.
Proof.
  elim: n j => [[]//|n IHn [] j].
  case jn: (j == n).
   move/eqP: jn => -> /= ?.
   rewrite big_ord_recr /= eqE /= eqxx GRing.mulr1.
   apply/eqP.
   rewrite -GRing.subr_eq0 GRing.addrK.
   apply/eqP/etrans.
   apply: (_ : _ = \sum_(i < n) 0)%R.
   apply/eq_big => [//|[] i ni _].
   set T := _ == _.
   have->: T = false.
    subst T.
    rewrite /= eqE /=.
    apply/negP => /eqP ni'.
    move: ni' ni => ->.
    by rewrite ltnn.
   by rewrite GRing.mulr0.
   rewrite big_const card_ord.
   elim n => // n'.
   by rewrite iterS GRing.add0r.
  move=> i. 
  rewrite big_ord_recr /=.
  set T := _ == _.
  have->: T = false.
   subst T.
   by rewrite eqE /= eq_sym jn.
  rewrite GRing.mulr0 GRing.addr0 /=.
  have jn': j < n.
   move: i T.
   by rewrite ltnS leq_eqVlt jn /=.
  by move: (IHn (Ordinal jn')) => /= <-.
Qed.

Lemma canon_matK M j :
  (canon_mat M *m delta_mx j (@Ordinal 1 0 erefl) =
   castmx (esym dimvm, erefl) (\col_(i < \dim fullv) coord e0 i (M e0`_j)))%R.
Proof.
  apply/matrixP => k [][]//= i.
  rewrite /canon_mat /canon_mat' /mat_inj !castmxE !mxE /=.
  apply/etrans.
  apply eq_big => [//| s /= _].
  rewrite !castmxE !mxE andbT (nth_map 0).
  apply/erefl.
  rewrite /= size_tuple -dimvm.
  by case: s.
  rewrite /= (nth_map 0).
  by rewrite (sum_col_delta (fun i0 => coord e0 (cast_ord (esym (esym dimvm)) k)
             (M (iter (nth 0 (iota 0 (\dim fullv)) i0) H0 (qpolify phi_gt1 'X))))).
  rewrite /= size_tuple -dimvm.
  by case: j.
Qed.

Lemma X2m_eqX : iter m H (pi 'X)%R = (pi 'X)%R.
Proof.
  rewrite expHpE.
  case/irreducibleP/andP: ip => _ /eqP H.
  by apply/val_inj.
Qed.

Lemma piX_neq0 : pi 'X%R != 0%R.
  apply/negP => /eqP /(f_equal val).
  rewrite /= modp_small ?size_polyX // => /eqP.
  by rewrite -size_poly_eq0 size_polyX.
Qed.

Lemma Xu: ((pi 'X : qpoly_fieldType_phi) \is a GRing.unit)%R.
  by rewrite GRing.unitfE piX_neq0.
Qed.

Lemma piX2X: (pi ('X ^ 2) != pi 'X)%R.
Proof.
  case/irreducibleP/andP: ip => piX2X _.
  by rewrite eqE /= piX2X.
Qed.

Lemma X2mp_eq1 : (pi ('X ^+ (2 ^ m - 1)) = 1)%R.
Proof.
  set piX := (FinRing.unit [finFieldType of qpoly_fieldType_phi] Xu). 
  suff: (piX ^+ (2 ^ m - 1))%g = 1%g.
   subst piX => /(f_equal val).
   rewrite !FinRing.val_unit1 !FinRing.val_unitX.
   set O := 1%R; set O' := 1%R.
   have->: O' = O by apply/val_inj.
   move=> <-.
   elim: (2 ^ m - 1) => [|m IHm].
    rewrite !GRing.expr0.
    by apply/val_inj.
   apply/val_inj.
   by rewrite !GRing.exprSr GRing.rmorphM IHm.
  suff<-: #[piX]%g = 2 ^ m - 1 by rewrite expg_order.
  have/cyclic.order_dvdG: piX \in
      [group of [set: {unit [finFieldType of qpoly_fieldType_phi]}]]
    by rewrite inE.
  rewrite /= card_finField_unit card_npoly card_ord.
  case/primeP: pm => _.
  rewrite !subn1 => H /H /orP [|/eqP //].
  rewrite order_eq1 => piX1.
  move: piX2X; subst piX; move: piX1.
  rewrite GRing.rmorphX !eqE /= !eqE /= => /eqP ->.
  by rewrite !modp_small ?GRing.mulr1 ?size_polyC ?eqxx.
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

Lemma mulHE j : 
 (canon_mat H *m delta_mx j (@Ordinal 1 0 erefl)
= delta_mx (step j) (@Ordinal 1 0 erefl))%R.
Proof.
  rewrite canon_matK.
  apply/matrixP => i [][]// ?.
  rewrite !castmxE !mxE andbT /= esymK (nth_map 0) ?size_iota ?(esym dimvm) //.
  move: (coord_free (cast_ord dimvm i) (step (cast_ord dimvm j))
                    (basis_free basis_e0)).
  have ->: (cast_ord dimvm i == step (cast_ord dimvm j)) = (i == step j).
   by rewrite !eqE /= -dimvm.
  move=> <-.
  rewrite coord_free ?(basis_free basis_e0) // eqE /=
          nth_iota ?(esym dimvm) //= add0n -iterS.
  case: j => // j.
  case jm: (j.+1 == m).
   move/eqP: jm => ->.
   rewrite X2m_eqX -[in RHS]dimvm modnn.
   have O: 0 < m by case: m m_is_prime.
   have->: (pi 'X = e0`_(cast_ord dimvm (Ordinal O)))%R.
    rewrite /e0 /=.
    by case: (\dim fullv) dimvm m_is_prime => // ->.
    by rewrite coord_free ?(basis_free basis_e0) // eqE /= eq_sym.
  move=> jm'.
  have mj : j.+1 < m
   by rewrite ltn_neqAle jm jm'.
  rewrite /= -iterS.
  set T := iter _ _ _.
  have->: (T = e0`_(cast_ord dimvm (Ordinal mj)))%R.
   subst T => /=.
   case: (\dim fullv) dimvm m_is_prime => [-> //|] d md.
   rewrite /= (nth_map 0) ?size_iota ?nth_iota; try by rewrite -ltnS -md.
   by rewrite add1n -iterS // -ltnS -md.
  by rewrite coord_free ?(basis_free basis_e0) // eqE /=
             -[in RHS]dimvm modn_small // eq_sym.
Qed.

Lemma mulCE j : 
((companionmx ('X ^ m + 1: {poly 'F_2}))^T *m delta_mx j (@Ordinal 1 0 erefl)
 = delta_mx (step j) (@Ordinal 1 0 erefl))%R.
Proof.
  apply/matrixP => i [][]// ?.
  rewrite /companionmx /= !mxE andbT /=.
  apply/etrans.
  apply eq_big => [//|i0 _].
  rewrite !mxE !eqE /= !eqxx andbT /=.
  apply/erefl. rewrite /= (sum_col_delta
   (fun i1 => (if eqn i1 (size ('X ^ (size phi).-1 + 1)).-2
             then - ('X ^ (size phi).-1 + 1)`_i else (eqn i1.+1 i)%:R)))%R.
  case: i => i /= i0.
  case: j => j /= j0.
  rewrite !eqE /=.
  rewrite size_addl ?size_polyX ?size_polyXn
          ?ltnS ?size_polyC ?GRing.oner_neq0 // in i0, j0.
  case: ifP => jm; last first.
  rewrite size_addl ?size_polyX ?size_polyXn
          ?ltnS ?size_polyC ?GRing.oner_neq0 // in jm.
   have ?: j.+1 < (size phi).-1.
    rewrite ltn_neqAle j0 andbT.
    move: m_is_prime.
    case: (size phi).-1 j0 jm => //= ?? /eqP jn _.
    rewrite eqSS; apply/negP => jn'.
    by move/eqP: jn' jn => ->.
   by rewrite modn_small ?size_addl ?size_polyX ?size_polyXn ?ltnS
           ?size_polyC // eq_sym eqE.
  rewrite size_addl ?size_polyX ?size_polyXn
          ?ltnS ?size_polyC ?GRing.oner_neq0 // in jm.
  rewrite size_addl ?size_polyX ?size_polyXn
          ?ltnS ?size_polyC ?GRing.oner_neq0 //.
  have->: j.+1 = (size phi).-1.
   rewrite (eqP jm) prednK //.
  rewrite modnn GRing.oppr_char2 // coefD coef1 coefXn.
  case si: (i == (size phi).-1).
   move/eqP: si i0 => ->.
   by rewrite /= ltnn.
  by rewrite GRing.add0r.
Qed.

Lemma sizem : m = (size ('X ^ m + 1: {poly 'F_2})%R).-1.
  by rewrite size_addl ?size_polyX ?size_polyXn
          ?ltnS ?size_polyC ?GRing.oner_neq0 //.
Defined.

Lemma test_delta (O := @Ordinal 1 0 erefl) n (R : finFieldType) (A B : 'M[R]_n) :
(forall j, A *m delta_mx j O = B *m delta_mx j O)%R <-> A = B.
Proof.
  split => [|-> //] H.
  apply/trmx_inj/row_matrixP => i; rewrite !rowE.
  apply/trmx_inj; rewrite !trmx_mul !trmxK !trmx_delta.
  move: (H i).
  set T := delta_mx i _.
  set T' := delta_mx i _.
  suff <-: T = T' by [].
  congr delta_mx.
  by apply/val_inj.
Qed.

Lemma enum_ord_enum_mem n :
  enum 'I_n = @enum_mem _ (@mem _ (predPredType _) (fun _ : ordinal n => true)).
Proof. by []. Qed.

Lemma compHE :
  (castmx (sizem, sizem) (canon_mat H) =
  (companionmx ('X ^ m + 1: {poly 'F_2}))^T)%R.
Proof.
  apply/test_delta => j.
  rewrite mulCE.
  apply/matrixP => i k.
  case: i => i Hi; case: j => j Hj.
  rewrite mxE /=.
  apply/etrans.
   apply/eq_big => [//|s _].
   rewrite !castmxE /= !esymK !cast_ord_comp.
   apply/erefl.
  move/matrixP: (mulHE (cast_ord (esym sizem) (Ordinal Hj)))
   => /(_ (cast_ord (esym sizem) (Ordinal Hi)) k).
  rewrite !mxE !eqE /= [in RHS]sizem => <-.
  rewrite -big_image_id -[RHS]big_image_id /=.
  apply congr_big => [|//|//].
  rewrite /image_mem -!enum_ord_enum_mem.
  have: map val (enum 'I_(size phi).-1)
      = map val (enum 'I_(size ('X ^ (size phi).-1 + 1 : {poly 'F_2})%R).-1).
   by rewrite -!sizem.
  case: (enum 'I_(size phi).-1) => [/(f_equal size)|].
   rewrite /= size_map size_enum_ord => H0.
   suff: false by [].
   move: H0 m_is_prime.
   by rewrite size_addl ?size_polyXn ?size_polyC //= => <-.
  case: (enum 'I_(size ('X ^ (size phi).-1 + 1)%R).-1) => //= a l r r0 [] H1 H2.
  set A := (canon_mat' _ _ _ * _)%R.
  set B := (canon_mat _ _ _ * _)%R.
  have->: A = B.
   rewrite /A /B.
   rewrite !mxE !castmxE !eqE /= !H1.
   rewrite !(nth_map 0) ?size_iota ?esymK.
   rewrite nth_iota // ?add0n.
   rewrite !mxE !cast_ord_comp (nth_map 0).
   rewrite nth_iota ?add0n.
   by rewrite -!iterS /= !H1.
   case: r H1 B => //.
   case: r H1 B => //= r ?.
   by rewrite size_iota -dimvm.
   case: a H1 A => //= a.
   by rewrite -dimvm -sizem.
   case: a H1 A => //= a.
   by rewrite -dimvm -sizem.
  congr cons => {A B H1}.
  elim: l r0 H2.
   move=> r0 /= r0m.
   apply/esym/size0nil.
   move/(f_equal size): r0m.
   by rewrite !size_map.
  move=> b l IH [] //= b0 r0 [] H1 /IH ->.
  congr cons.
  rewrite !mxE !castmxE !eqE /= !H1
          !(nth_map 0) ?size_iota ?esymK.
  rewrite nth_iota // ?add0n.
  rewrite !mxE !cast_ord_comp (nth_map 0).
  rewrite nth_iota ?add0n.
  by rewrite -!iterS /= !H1.
  case: b0 H1 => //.
  case: b0 H1 => //= ? ?.
  by rewrite size_iota -dimvm.
  case: b H1 => //= ?.
  by rewrite -dimvm -sizem.
  case: b H1 => //= ?.
  by rewrite -dimvm -sizem.
Qed.

Lemma mulXHC:
  mulX \o mulX \o H =1 H \o mulX.
Proof.
  move=> x.
  rewrite (coord_basis basis_e0 (memvf x)).
  have->: (\sum_i coord e0 i x *: e0`_i)%R
   = (\sum_(i <- ord_enum (\dim fullv)) coord e0 i x *: e0`_i)%R.
   rewrite -big_image_id big_image.
   apply congr_big => [|//|//].
   by rewrite /index_enum unlock.
  rewrite (GRing.linear_sum (GRing.comp_linear (Linear linH) (linearType_mulV _)))
          (GRing.linear_sum (GRing.comp_linear (linearType_mulV _)
                         (GRing.comp_linear (linearType_mulV _) (Linear linH)))).
  apply/eq_big => [//|i _].
  case: (coord e0 i x) => [][|[]//] i0; set T := Ordinal i0.
   have->: T = 0%R by apply/val_inj.
   by rewrite !GRing.scale0r !GRing.linear0.
  have->: T = 1%R by apply/val_inj.
  rewrite !GRing.scale1r !(nth_map 0) ?size_iota // !nth_iota // !add0n
          !expHpE /= /mulX /mulV /H0 /= !GRing.Frobenius_autE
          -!(GRing.rmorphM pi) -!(GRing.rmorphX pi)
          !GRing.exprS !GRing.expr0 !GRing.mulr1.
  have<-: ('X = pi 'X)%R
   by rewrite /= modp_small // size_polyX.
  apply/eqP; rewrite eqE /=; apply/eqP.
  have->: ('X ^ (2 ^ i)%N * 'X * ('X ^ (2 ^ i)%N * 'X) = 
           'X ^ (2 ^ i)%N * 'X ^ (2 ^ i)%N * 'X * 'X)%R.
   move=> ?.
   by rewrite GRing.mulrCA !GRing.mulrA.
  have<-: ('X * 'X * ('X ^ (2 ^ i)%N * 'X ^ (2 ^ i)%N)
        = 'X ^ (2 ^ i)%N * 'X ^ (2 ^ i)%N * 'X * 'X)%R.
   move=> ?.
   by rewrite GRing.mulrC GRing.mulrA.
  by rewrite -[in RHS]modp_mul -GRing.mulrA GRing.mulrC.
Qed.

Lemma cycleH : iter m H =1 id.
Proof.
  move=> x.
  rewrite (coord_basis basis_e0 (memvf x)).
  have->: (\sum_i coord e0 i x *: e0`_i)%R
   = (\sum_(i <- ord_enum (\dim fullv)) coord e0 i x *: e0`_i)%R.
   rewrite -big_image_id big_image.
   apply congr_big => [|//|//].
   by rewrite /index_enum unlock.
  move: ((GRing.linear_sum (Linear (iter_linear (Linear linH) m)))
           _ (ord_enum (\dim fullv)) xpredT
          (fun i => coord e0 i x *: e0`_i)%R) => /= ->.
  apply/eq_big => [//|i _].
  rewrite !(nth_map 0) ?size_iota // !nth_iota //.
  move: (GRing.linearZ_LR (Linear (iter_linear (Linear linH) m))) => /= ->.
  congr (_ *: _)%R.
  rewrite -iter_add !add0n !expHpE expnD
          -exprnP GRing.exprM GRing.rmorphX exprnP.
  by rewrite -expHpE X2m_eqX GRing.rmorphX.
Qed.

Lemma expXpE p : iter p mulX =1 mulV (pi 'X ^+ p)%R.
Proof.
  elim: p => [x|p IHp x].
   by rewrite /= GRing.expr0 /mulV GRing.mulr1.
  by rewrite iterS IHp GRing.exprS /mulX /mulV
  -GRing.mulrA -GRing.rmorphX -GRing.rmorphM GRing.mulrC GRing.rmorphM.
Qed.
  
Lemma cycleX : iter (2 ^ m - 1) mulX =1 id.
Proof.
  move=> x.
  rewrite (coord_basis basis_e0 (memvf x)).
  have->: (\sum_i coord e0 i x *: e0`_i)%R
   = (\sum_(i <- ord_enum (\dim fullv)) coord e0 i x *: e0`_i)%R.
   rewrite -big_image_id big_image.
   apply congr_big => [|//|//].
   by rewrite /index_enum unlock.
  move: ((GRing.linear_sum (Linear (iter_linear (linearType_mulV (pi 'X)%R) (2 ^ m - 1))))
           _ (ord_enum (\dim fullv)) xpredT
          (fun i => coord e0 i x *: e0`_i)%R) => /= ->.
  apply/eq_big => [//|i _].
  rewrite !(nth_map 0) ?size_iota // !nth_iota //.
  move: (GRing.linearZ_LR (Linear (iter_linear (linearType_mulV (pi 'X)%R) (2 ^ m - 1)))) => /= ->.
  by rewrite expXpE -GRing.rmorphX X2mp_eq1 /mulV GRing.mulr1.
Qed.
End irreducibility.
