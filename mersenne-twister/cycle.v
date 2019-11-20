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

Section irreduciblity.
Variable phi : {poly [finFieldType of 'F_2]}.
Definition m := (size phi).-1.
Hypothesis pm : prime (2 ^ m - 1).

Local Lemma exp2_dvd a b :
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
  rewrite -size_poly_eq0 /m.
  by case: (size phi).
Qed.

Lemma phi_gt1 : 1 < size phi.
Proof.
  move: m_is_prime; rewrite /m.
  by case: (size phi) => []//[].
Qed.

Lemma phi_gt2 : 2 < size phi.
Proof.
  move: m_is_prime; rewrite /m.
  by case: (size phi) => []//[]//[].
Qed.

Lemma phi_gt0 : 0 < size phi.
Proof.
  move: m_is_prime; rewrite /m.
  by case: (size phi).
Qed.

Lemma predpower_gt_succpower : (2 ^ m).-1 < (2 ^ m).+1.
Proof. by case: (2 ^ m) pm. Qed.

Lemma power_gt0 : 0 < 2 ^ m.
Proof. by case: (2 ^ m) pm. Qed.

Lemma predpower_gt0 : 0 < 2 ^ m - 1.
Proof. by case: (2 ^ m - 1) pm. Qed.

Lemma predpower_neq0 : 0 != 2 ^ m - 1.
Proof. by case: (2 ^ m - 1) pm. Qed.

Lemma phi_gtb (b : bool) : b < size phi.
Proof.
  by case: b; rewrite ?phi_gt1 ?phi_gt0.
Qed.

Lemma predphi_neq0 : (size phi).-1 != 0.
Proof.
  move: m_is_prime.
  rewrite /m.
  by case: (size phi).-1.
Qed.

Lemma predpredpower_power : (2 ^ m - 1).-1 < 2 ^ m - 1.
Proof. by case: (2 ^ m - 1) pm. Qed.

Lemma predpredpower_gt0 : 0 < (2 ^ m - 1).-1.
Proof. by case: (2 ^ m - 1) pm => []//[]. Qed.

Lemma p_ord_prf : (2 ^ m - 1 < (2 ^ m).+1)%N.
Proof. by rewrite subn1 predpower_gt_succpower. Qed.

Local Canonical qpoly_ringType_phi :=
  Eval hnf in qpoly_ringType phi_gt1.
Local Canonical qpoly_comRingType_phi :=
  Eval hnf in qpoly_comRingType phi_gt1.
Local Definition pi := canon_surj phi_gt1.

Hint Resolve phi_gt0 phi_gt1 phi_gt2 phi_gtb
     predpredpower_power predpredpower_gt0
     predphi_neq0 predpower_neq0 predpower_gt0
     p_ord_prf predpower_gt_succpower power_gt0 phi_neq0 polyX_neq0 : core.

Lemma div_ord (a : nat) y (x : ordinal y) : ordinal y.
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
  case x0': (0 != @div_ord (min_stab a) _ x).
   have: @div_ord (min_stab a) _ x \in stab a by rewrite inE H0.
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
(forall l k : nat, (pi 'X ^+ l * pi 'X = pi 'X ^+ k * pi 'X)%R -> k = l %[mod 2 ^ m - 1])
-> #|image (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => pi ('X ^ x * 'X)%R) 'Z_(2 ^ m - 1)|
= (2 ^ m - 1)%N.
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
image (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => pi ('X ^ x * 'X)%R) 'Z_(2 ^ m - 1)
=i (finset {qpoly phi} :\ (0 : {qpoly phi})%R).
(* =i {unit [comRingType of [ringType of {qpoly phi}]]}. *)
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
(forall l k : nat, (pi 'X ^+ l * pi 'X)%R = (pi 'X ^+ k * pi 'X)%R -> k = l %[mod 2 ^ m - 1])
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

(* Lemma mem_qpoly_phi x : *)
(*   (x != 0 -> irreducible_poly phi -> exists y, pi 'X ^+ y = x)%R. *)
(* Proof. *)
(* move=> + ip. *)
(* case: x. *)
(* apply: poly_ind => [?|x c IH w]; first by rewrite eqE /= eqxx. *)
(* case x0: (x == 0)%R. *)
(*  move/eqP: x0 w => ->. *)
(*  rewrite GRing.mul0r GRing.add0r. *)
(*  case: c => [][|[]//] /= i w; first by rewrite -size_poly_gt0 size_polyC /= ltnn. *)
(*  exists 0; apply/val_inj => /=. *)
(*  rewrite modp_small ?size_polyC //. *)
(*   by congr (_ %:P)%R; apply/val_inj. *)
(* have X: x \is a poly_of_size (size phi).-1. *)
(*  apply/eqP/eqP; move/eqP/eqP: w. *)
(*  rewrite size_addl size_mul ?x0 ?polyX_neq0 ?size_polyX ?addn2 // ?subn_eq0. *)
(*  by apply/leq_trans/ltnW. *)
(*  rewrite size_polyC. *)
(*  case: (c != 0%R) => //. *)
(*  by rewrite ltnS leqNgt ltnS leqn0 size_poly_eq0 x0. *)
(* case: (IH X); first by rewrite eqE /= x0. *)
(* move=> y /(f_equal val). *)
(* rewrite /=. *)

Lemma X2m_eqXE : 
(('X ^ (2 ^ m)%N %% phi == 'X %% phi) = (p_ord \in stab (pi 'X) (pi 'X)))%R.
by rewrite inE -!GRing.rmorphX -!GRing.rmorphM -!exprnP !eqE /=
           -GRing.exprSr subn1 prednK.
Qed.

Lemma z2m_eqzE (L : ringType) (z : L)  : 
((z ^+ (2 ^ m)%N == z) = (p_ord \in stab z z))%R.
  by rewrite inE -GRing.exprSr /= subn1 prednK.
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
  set e0 : {qpoly phi} -> L := (fun g => (map_poly (GRing.in_alg L) g).[z])%R.
  have rme: rmorphism (e0 : (qpoly_fieldType ip) -> _).
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
   by rewrite /m -p1.
  have Xu: ((pi 'X : qpoly_fieldType ip) \is a GRing.unit)%R.
   rewrite GRing.unitfE.
   apply/negP => /eqP /(f_equal e).
   rewrite GRing.rmorph0.
   subst e e0.
   rewrite /= modp_small ?size_polyX // map_polyX hornerX => z0.
   move: z0 sL => ->.
   by rewrite addv0 => /a1f.
  apply/andP; split.
   suff: (pi ('X ^ 2) != pi ('X))%R by rewrite eqE.
   apply/negP => /eqP.
   move/(f_equal (fun x => (pi 'X : qpoly_fieldType ip)^-1 * x))%R.
   rewrite GRing.mulVr //.
   have ->: ((pi ('X ^ 2) : qpoly_fieldType ip)
            = ((pi 'X) : qpoly_fieldType ip) * ((pi 'X) : qpoly_fieldType ip))%R.
    rewrite -exprnP GRing.exprS GRing.expr1 GRing.rmorphM.
    by apply/val_inj.
   rewrite GRing.mulKr // => /(f_equal e)/eqP.
   subst e e0.
   rewrite /= !modp_small ?size_polyC ?size_polyX //
           map_polyC hornerC map_polyX hornerX  /= => /eqP z1.
   rewrite GRing.scale1r in z1.
   move: z1 sL => ->.
   by rewrite /= addvv => /a1f.
  suff: (pi ('X ^ (2 ^ m)%N) = pi ('X))%R by move/(f_equal val) => /= ->.
  (* suff H: (pi 'X ^+ (2 ^ m - 1) = 1)%R. *)
  (*  have->: (2 ^ m) = (2 ^ m - 1).+1 by rewrite subn1 prednK. *)
  (*  by rewrite GRing.rmorphX GRing.exprS H GRing.mulr1. *)
  (* apply/eqP/negP => /negP Hc. *)
  (* have/setD1P: ((pi 'X ^+ (2 ^ m - 1))%R != 1%R) /\ *)
  (*              ((pi 'X ^+ (2 ^ m - 1))%R \in (finset {qpoly phi})) *)
  (* by rewrite inE. *)
  apply/inje/eqP.
  suff: (e \o pi) ('X ^ (2 ^ m)%N)%R == ((e \o pi) 'X%R) by [].
  (* workaround *)
  have rme': rmorphism e0.
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
  set e' := RMorphism rme'.
  have epi: rmorphism (e' \o pi).
   constructor.
   apply GRing.comp_is_additive.
   apply GRing.comp_is_multiplicative.
  have<-: (e' \o pi) =1 (e \o pi) by [].
  rewrite !GRing.rmorphX.
  have /= ->: (e' \o pi) 'X%R = z.
   subst e e0.
   by rewrite /= !modp_small ?size_polyC ?size_polyX //
              map_polyX hornerX.
  
   have: ((z ^+ (2 ^ m)) \in <<1; z>>%VS)%R.
    rewrite Fadjoin_eq_sum /=.
    rewrite /Fadjoin_sum.
    rewrite /adjoin_degree.
    rewrite /= sL.
    rewrite dL.
    rewrite dimv1.
    rewrite divn1.
    rewrite prod1v.
    rewrite div
    move=> x.
    rewrite /=.
    apply/eqP/eqP.
    rewrite inE.
    done.
  Check Fadjoin_polyP.
  suff H: (z ^+ (2 ^ m - 1) = 1)%R.
   have->: (2 ^ m) = (2 ^ m - 1).+1 by rewrite subn1 prednK.
   by rewrite GRing.exprS H GRing.mulr1.
   
  have: (forall l k : nat, (z ^+ l * z = z ^+ k * z)%R -> k = l %[mod 2 ^ m - 1]).
   move=> l k.
   rewrite [X in (_ ^+ X * _)%R](divn_eq l (2 ^ m - 1)).
   rewrite [X in _ = (_ ^+ X * _)%R](divn_eq k (2 ^ m - 1)).
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
 
  move: sL.
  
  rewrite agenvE .
  have zm: forall m : nat, (<[z]> * <<1; z ^+ m>> = <<1; z ^+ m.+1>>)%VS.
   elim.
    rewrite GRing.expr0 GRing.expr1 addvv.
    rewrite prodv_line.
    rewrite expv0.
   rewrite -expvSr.
   move=> m.
   rewrite agenvEl prodvDl prod1v.
  rewrite addvC.
  rewrite -agenvEr. prodvDl prod1v.
  rewrite [X in (1 + (_ + _ * X))%VS = _]agenvEl.
  rewrite agenvEl. prodvDl prod1v.
  prodv1.
  rewrite agenvEr.
  rewrite agenvEr .
  rewrite agenvEr .
  Check [finType of L].
  Check #|L|.
  
End irreduciblity.
  
From codegen Require Import codegen.
Require Import mt.

From infotheo Require Import f2 ssralg_ext.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

End mt19937_cyclic.
