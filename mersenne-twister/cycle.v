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

(* Variable m : nat. *)
(* Hypothesis sp : (size phi).-1 = m. *)

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

Local Canonical qpoly_ringType_phi :=
  Eval hnf in qpoly_ringType phi_gt1.
Local Canonical qpoly_comRingType_phi :=
  Eval hnf in qpoly_comRingType phi_gt1.
Local Definition pi := canon_surj phi_gt1.

Definition stab a : {set 'I_(2 ^ m).+1} :=
[set n | ('X ^ (nat_of_ord n) * a %% phi == a %% phi)%R].

Lemma foldl_min_cons x y z : foldl minn x (y :: z) = minn y (foldl minn x z).
Proof.
  elim: z x y => [*| ? z IH x y] /=;
  by rewrite minnC // -IH /= minnAC minnC.
Qed.

Definition min_stab a :=
foldl minn (2 ^ m)
      (filter (fun x => x > 0) (map (@nat_of_ord _) (enum (stab a)))).

Definition min_stab_ord (a: {poly [finFieldType of 'F_2]}): ordinal (2 ^ m).+1.
  have H: (min_stab a < (2 ^ m).+1).
   rewrite /min_stab.
   elim: [seq _ | _ <- _] => [|c l IH].
    by case: (2 ^ m) pm.
   apply/leq_ltn_trans/IH => {IH} /=.
   by case: ifP => //; rewrite foldl_min_cons geq_minr.
 by apply (Ordinal H).
Defined.

Lemma phi_gt0 : 0 < size phi.
Proof.
  move: m_is_prime; rewrite /m.
  by case: (size phi).
Qed.

Lemma power_gt0 : 0 < 2 ^ m.
Proof. by case: (2 ^ m) pm. Qed.
Hint Resolve phi_gt0 phi_gt1 power_gt0 phi_neq0 polyX_neq0 : core.

Lemma foldl_minn_in xs m' :
  has (fun x => x < m'.+1) xs -> foldl minn m' xs \in xs.
Proof.
  elim: xs m' => // x xs IH m'.
  rewrite /= in_cons.
  case xm: (x < m'.+1).
   rewrite /minn ltnNge -ltnS xm /= -/minn => _ {IH xm}.
   elim: xs x => [?|y ? IH /= x].
    by rewrite /= eqxx.
   case xy: (x < y).
    rewrite /minn xy /= -/minn in_cons.
    case/orP: (IH x) => -> //.
    by rewrite !orbT.
   rewrite /minn xy /= -/minn in_cons.
   by case/orP: (IH y) => ->; rewrite !orbT.
  move/negP/negP: xm; rewrite -ltnNge ltnS leq_eqVlt => /orP [/eqP <-|mx].
  by rewrite /minn ltnSn -/minn => /IH ->; rewrite orbT.
  by rewrite /minn ltnW // -/minn => /IH ->; rewrite orbT.
Qed.

Lemma min_stab_in a y :
  y \in stab a -> 0 != y ->
  min_stab a \in (filter (fun x => x > 0) (map (@nat_of_ord _) (enum (stab a)))).
Proof.
  case: y => y Hy1 Hy2 y0.
  apply/foldl_minn_in/hasP/ex_intro2/Hy1.
  rewrite mem_filter lt0n eq_sym y0.
  have->: y = Ordinal Hy1 by [].
  by rewrite mem_map ?mem_enum ?Hy2 // => *; apply/val_inj.
Qed.

Lemma min_stab_min a y :
  y \in stab a -> 0 != y -> min_stab_ord a <= y.
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

Lemma min_stab_gt0 a : 0 < min_stab_ord a.
Proof.
  rewrite /min_stab_ord /min_stab /=.
  elim: (enum (pred_of_set (stab a))) => [|a' l IH /=] //.
  case: ifP => //.
  case: a' => []//[]// a' ??.
  rewrite foldl_min_cons /=.
  move: IH; set T := (foldl minn _  _).
  case: T => // t.
  by rewrite minnSS.
Qed.

Lemma min_stab_cond a b y :
  y \in stab a -> 0 != y ->
  (('X ^ (b * min_stab a)%N * a) %% phi == a %% phi)%R.
Proof.
  move=> ys y0.
  have H1: (('X ^ (min_stab a) * a) %% phi)%R == (a %% phi)%R.
   suff: min_stab a \in (filter (fun x => x > 0)
                                (map (@nat_of_ord _) (enum (stab a)))).
    have->: min_stab a = min_stab_ord a by [].
    rewrite mem_filter mem_map.
     by rewrite mem_enum inE => /andP [].
    by move=> ?? H; apply/val_inj/H.
   apply: (@min_stab_in _ _ ys y0).
  elim: b => [|b IHb]; first by rewrite !mul0n GRing.mul1r.
  rewrite mulSn -exprnP GRing.exprD -GRing.mulrA !exprnP -modp_mul.
  move/eqP: IHb => ->.
  by rewrite modp_mul H1.
Qed.

Lemma div_ord (a : nat) y (x : ordinal y) : ordinal y.
  apply/(@Ordinal _ (x %% a))/(leq_ltn_trans (leq_mod _ _)).
  by case: x.
Defined.

Lemma p_ord_prf : 2 ^ m - 1 < (2 ^ m).+1.
  case: (2 ^ m) pm => // n.
  by rewrite subn1.
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

Lemma min_stab_dvd a x : x \in stab a -> min_stab a %| x.
  case x0: (0 == x); first by move/eqP: x0 => <-.
  move/negP/negP: x0 => x0 H; move: (H).
  rewrite inE (divn_eq x (min_stab a)) -exprnP GRing.exprD
          GRing.mulrAC GRing.mulrC !exprnP -modp_mul.
  move/eqP: (@min_stab_cond a (x %/ min_stab a) x H x0) ->.
  rewrite modp_mul dvdn_addr ?dvdn_mull // => H0.
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
one_ord \notin pred_of_set (stab a) -> min_stab a == 1 = false.
Proof.
  move=> Hy Hy' H; apply/eqP/eqP; move: H; apply: contra => /eqP H.
  have->: one_ord = min_stab_ord a by apply/val_inj; rewrite /= H.
  rewrite inE /=.
  move: (@min_stab_cond a 1 y Hy Hy').
  by rewrite mul1n.
Qed.

Lemma min_stab_attain_base :
  (min_stab 'X == (2 ^ m - 1)%N)%R ->
  forall l, 0 < l < 2 ^ m - 1 -> ('X ^ l * 'X %% phi != 'X %% phi)%R.
Proof.
  move/eqP => H l /andP [] Hl0 Hl; apply/negP => /eqP C.
   have Hl': l < (2 ^ m).+1.
    apply (ltn_trans Hl).
    by case: (2 ^ m) Hl => []//[]// n ?; rewrite subn2 /=.
   have: Ordinal Hl' \in enum (stab 'X)
    by rewrite mem_enum inE /= C.
   have Hl2: (l < 2 ^ m - 1).
    apply/(leq_trans Hl).
    by case: (2 ^ m) pm => []//[]// ??.
   rewrite lt0n eq_sym in Hl0.
   rewrite mem_enum.
   move/min_stab_min.
   by rewrite /= Hl0 H leqNgt Hl2 => /implyP.
Qed.

Lemma min_stab_attain :
  ('X^(2 ^ m) %% phi)%R == ('X %% phi)%R ->
  (min_stab 'X == (2 ^ m - 1)%N)%R ->
  forall l k, l < 2 ^ m - 1 -> 0 < k < 2 ^ m - 1 ->
  ('X ^ l * 'X %% phi = 'X ^ k * 'X %% phi)%R -> k = l.
Proof.
  move => m2 /min_stab_attain_base => Hl l k.
  case kl: (k == l %[mod (2 ^ m - 1)])%N.
   move: kl => + Hl1 /andP [] Hk1 Hk2.
   by rewrite !modn_small // => /eqP ->.
  move=> Hl2 Hk2.
  case kl': (k > l).
   have: (0 < l + (2 ^ m - 1 - k) < 2 ^ m - 1).
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
   move/Hl => + lk.
   rewrite -exprnP GRing.exprD -GRing.mulrA GRing.mulrCA
    !exprnP -modp_mul lk modp_mul -!exprnP
    -GRing.mulrCA GRing.mulrA -GRing.exprD addnBA.
    by rewrite addnC addnK subn1 GRing.mulrC -GRing.exprS prednK // m2.
   by case/andP: Hk2 => ??; apply/ltnW.
  move/negP/negP: kl'; rewrite -ltnNge ltnS leq_eqVlt => /orP [/eqP ->|] // kl'.
  have: (0 < k + (2 ^ m - 1 - l) < 2 ^ m - 1).
   apply/andP; split.
    rewrite lt0n addn_eq0; apply/negP => /andP [] /eqP l0 mk.
    move: l0 mk kl => ->.
    by rewrite subn_eq0 leqNgt Hl2.
   rewrite addnBA; last by apply ltnW.
   rewrite addnC -subnBA ?ltn_subr //; last by apply ltnW.
   apply/andP; split.
    by rewrite lt0n subn_eq0 -ltnNge.
   by apply/(leq_ltn_trans (leq_subr _ _)).
  move/Hl => + lk.
  rewrite -exprnP GRing.exprD -GRing.mulrA GRing.mulrCA
   !exprnP -modp_mul -lk modp_mul -!exprnP
   -GRing.mulrCA GRing.mulrA -GRing.exprD addnBA.
   by rewrite addnC addnK subn1 GRing.mulrC -GRing.exprS prednK // m2.
  by rewrite ltnW // Hl2.
Qed.

Lemma min_stab_attain_extend :
  p_ord \in stab 'X ->
  ('X^(2 ^ m) %% phi)%R == ('X %% phi)%R ->
  (min_stab 'X == (2 ^ m - 1)%N)%R ->
  forall l k : nat, 0 < k < 2 ^ m - 1 ->
  ('X ^ l * 'X %% phi = 'X ^ k * 'X %% phi)%R -> k = l %% (2 ^ m - 1).
Proof.
  move=> Hp.
  move/min_stab_attain => H Hm; move/H: (Hm) => {H} H l k.
  rewrite [X in (_ ^ (_ X) * _ %% _)%R](divn_eq l (2 ^ m - 1)).
  have: 0 != p_ord by rewrite /=; case: (2 ^ m - 1) pm.
  move/(min_stab_cond (l %/ (2 ^ m - 1)) Hp).
  move/eqP: Hm => -> /eqP Hm.
  rewrite -!exprnP GRing.exprD GRing.mulrAC GRing.mulrC
          -modp_mul !exprnP Hm modp_mul.
  move/H => {H} /(_ (l %% (2 ^ m - 1))) H /H -> //.
  by rewrite ltn_mod; case: (2 ^ m - 1) pm => //.
Qed.

Lemma min_stab_attain2 :
  p_ord \in stab 'X ->
  ('X^(2 ^ m) %% phi)%R == ('X %% phi)%R ->
  (min_stab 'X == (2 ^ m - 1)%N)%R ->
forall l k : nat, ('X ^ l * 'X %% phi = 'X ^ k * 'X %% phi)%R -> k = l %[mod 2 ^ m - 1].
move=> H1 H2 H3.
move: (min_stab_attain_extend H1 H2 H3) => H4 l k.
rewrite (divn_eq k (2 ^ m - 1)).
have: 0 != p_ord by rewrite /=; case: (2 ^ m - 1) pm.
move/(min_stab_cond (k %/ (2 ^ m - 1)) H1).
move/eqP: (H3) => -> /eqP H3' /esym.
rewrite -!exprnP GRing.exprD GRing.mulrAC GRing.mulrC
          -modp_mul !exprnP H3' modp_mul.
rewrite modnMDl modn_mod (divn_eq l (2 ^ m - 1)).
have: 0 != p_ord by rewrite /=; case: (2 ^ m - 1) pm.
move/(min_stab_cond (l %/ (2 ^ m - 1)) H1).
move/eqP: (H3) => -> /eqP H3'' /esym.
rewrite -!exprnP GRing.exprD GRing.mulrAC GRing.mulrC.
rewrite -[in LHS]modp_mul !exprnP  H3'' modp_mul.
rewrite modnMDl.
case k0: (k %% (2 ^ m - 1)).
 case l0: (l %% (2 ^ m - 1)).
  by rewrite mod0n.
 move/esym/H4 => -> //.
  by rewrite !mod0n.
 rewrite /= -l0 ltn_mod.
 case: (2 ^ m - 1) pm => //.
move/H4 => -> //.
rewrite /= -k0 ltn_mod.
case: (2 ^ m - 1) pm => //.
Qed.

Lemma map_pi_inj :
(forall l k : nat, ('X ^ l * 'X %% phi = 'X ^ k * 'X %% phi)%R -> k = l %[mod 2 ^ m - 1])
  -> injective (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => pi ('X ^ x * 'X)%R).
Proof.
  move=> H x y /eqP.
  rewrite eqr_pi => /eqP /H.
  case: y => y yH.
  case: x => x xH.
  rewrite !modn_small //=.
  by move=> yx; apply/val_inj.
  apply: (leq_trans xH).
  by rewrite /Zp_trunc prednK; case: (2 ^ m - 1) pm => []//[].
  apply: (leq_trans yH).
  by rewrite /Zp_trunc prednK; case: (2 ^ m - 1) pm => []//[].
Qed.

Lemma map_pi_card :
(forall l k : nat, ('X ^ l * 'X %% phi = 'X ^ k * 'X %% phi)%R -> k = l %[mod 2 ^ m - 1])
-> #|image (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => pi ('X ^ x * 'X)%R) 'Z_(2 ^ m - 1)|
= 2 ^ m - 1.
Proof.
  move=> /map_pi_inj H.
  have Hc : #|'Z_(2 ^ m - 1)| = 2 ^ m - 1.
   rewrite card_ord.
   by case: (2 ^ m - 1) pm => [][].
  rewrite -[RHS]Hc.
  apply/eqP/image_injP => x y Hx Hy.
  by apply: H.
Qed.

Lemma Xn_phi_neq0 (a : nat) :
(forall l k : nat,
(('X ^ l * 'X) %% phi)%R = (('X ^ k * 'X) %% phi)%R -> k = l %[mod 2 ^ m - 1])
-> (('X ^ a * 'X) %% phi)%R != 0%R.
Proof.
  move=> H0; apply/negP => /eqP Hc.
  move: (H0 a a.+1).
  rewrite -!exprnP GRing.exprS -GRing.mulrA -[X in _ = X]modp_mul
          Hc GRing.mulr0 mod0p => /(_ erefl)/eqP.
  rewrite (divn_eq a (2 ^ m - 1)) -addnS !modnMDl.
  apply/negP/lem1 => //.
  rewrite ltn_mod.
  by case: (2 ^ m - 1) pm.
Qed.

Lemma map_piE :
  p_ord \in stab 'X ->
  ('X^(2 ^ m) %% phi)%R == ('X %% phi)%R ->
  (min_stab 'X == (2 ^ m - 1)%N)%R ->
(image (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => pi ('X ^ x * 'X)%R) 'Z_(2 ^ m - 1)
=i (finset {qpoly phi} :\ (0 : {qpoly phi})%R)).
(* =i {unit [comRingType of [ringType of {qpoly phi}]]}. *)
Proof.
  move=> H1 H2 H3.
  move: (min_stab_attain2 H1 H2 H3) => H0.
  move/map_pi_card: (H0) => H.
  apply/subset_cardP.
   rewrite cardsDS /= ?sub1set ?inE //.
   by rewrite cardsT H card_npoly card_ord /m cards1.
  suff: codom (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => pi ('X ^ x * 'X)%R)
        \subset (finset {qpoly phi} :\ (0 : {qpoly phi})%R)
   by apply/subset_trans/subsetP/image_codom.
  apply/subsetP => x.
  rewrite codomE !inE /=.
  elim: (enum 'Z_(2 ^ m - 1)) => //= a l IH.
  rewrite in_cons => /orP [/eqP ->|/IH -> //].
  rewrite andbT !eqE Xn_phi_neq0 //.
Qed.
  
Lemma map_piP q :
(forall l k : nat, ('X ^ l * 'X %% phi = 'X ^ k * 'X %% phi)%R -> k = l %[mod 2 ^ m - 1])
-> reflect (exists (r : 'Z_(2 ^ m - 1)), pi ('X ^ r * 'X)%R = q)
(q \in (image (fun (x: [ringType of 'Z_(2 ^ m - 1)]) => pi ('X ^ x * 'X)%R)
'Z_(2 ^ m - 1))).
Proof.
move/map_pi_inj => ?.
apply/(iffP idP).
* rewrite /image_mem.
  elim: (enum 'Z_(2 ^ m - 1)) => // a l IH.
  rewrite in_cons => /orP [/eqP ->|/IH //]; by exists a.
* case => q0 <-.
  by rewrite mem_image.
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

Lemma irreducibleP :
reflect (irreducible_poly phi)
(('X ^ 2 %% phi != 'X %% phi) && ('X ^ (2 ^ m)%N %% phi == 'X %% phi))%R.
Proof.
apply/(iffP idP).
* case/andP => H1 H2.
  have H: p_ord \in stab 'X
   by rewrite inE -exprnP GRing.mulrC -GRing.exprS /= subn1 prednK.
  case/min_stab_dvd: (H) pm => + /primeP [] o pm' => /pm' {pm'}.
  have: one_ord \notin stab 'X by rewrite inE -exprnP GRing.mulrC -GRing.exprS.
  move/(@min_stab_neq1 _ _ H) => -> /= => [x2m1|]; last by case: (2 ^ m - 1) o.
  apply/irreducibleP/andP.
  constructor => //.
  apply/forallP => q; apply/implyP.
  case q0: (size q == 0); first by move/eqP: q0 => ->.
  have: q \in (finset {qpoly phi} :\ (0 : {qpoly phi})%R).
   rewrite !inE andbT.
   apply/negP => /eqP q0'.
   move: q0' q0 => ->.
   by rewrite size_polyC eqxx.
  rewrite -!(map_piE H H2 x2m1).
  move: (min_stab_attain2 H H2 x2m1) => H0.
  case/(map_piP _ H0) => q1 <-.
  have pq0: pi ('X ^ q1 * 'X)%R != 0%R by rewrite /= Xn_phi_neq0.
  case/Pdiv.RingMonic.rdvdpP => [|x pxp]; first by apply/f2p_monic.
  case x0: (x == 0)%R.
   move/eqP: x0 pxp phi_neq0 => ->.
   rewrite GRing.mul0r => <-.
   by rewrite eqxx.
  have/dvdp_leq: (x %| phi)%R by rewrite pxp dvdp_mulr.
  rewrite phi_neq0 => /implyP /=.
  rewrite leq_eqVlt => /orP [/eqP|] xp.
   have: size phi = size (x * pi ('X ^ q1 * 'X))%R by rewrite /= -pxp.
   rewrite size_mul ?x0 //= xp => /eqP.
   by rewrite -subn1 -[X in X == _]addn0 -addnBA ?lt0n ?size_poly_eq0
              // eqn_add2l eq_sym subn_eq0.
  have xx: x = pi x by rewrite /= modp_small.
  have: pi phi == pi (x * pi ('X ^ q1 * 'X))%R by rewrite -pxp.
  have: (pi x)%R \in (finset {qpoly phi} :\ (0 : {qpoly phi})%R)
   by rewrite !inE andbT eqE /= -size_poly_eq0 modp_small //
           ?ltn_size_polyC_X ?size_polyC // size_poly_eq0 x0.
  rewrite GRing.rmorphM -!(map_piE H H2 x2m1).
  case/(map_piP _ H0) => x1 <-.
  rewrite -GRing.rmorphM eqE /= modpp modp_mul
          GRing.mulrCA !GRing.mulrA -GRing.exprD GRing.mulrC
          GRing.mulrA -GRing.exprS eq_sym => /negPn.
  by rewrite Xn_phi_neq0.
* move=> ip; case/irredp_FAdjoin: (ip) => L + [] z zsp.
  Check ([aspace of 1%VS] : {subfield L})%R.
  case: (@galLgen _ L [aspace of 1%VS]).
  rewrite /=.
  
  Check [finFieldType of L].
  move/FinSplittingFieldFor : (phi).
  Check (@SubFieldExtType _ L _ z _ _ ip).
  (* have f: [finFieldType of 'F_2] -> L by []. *)
   (* Show Proof. *)
  have: {rmorphism [finFieldType of 'F_2] -> L}%R.
   apply/(RMorphism _)/(_ : rmorphism (f L)).
   constructor.
   case => [][|[]//] ? [][|[]//] ?.
   by rewrite !GRing.subr0.
   rewrite !GRing.sub0r.
   rewrite /f /=.
    rewrite /=.
   done.
    move=> ?.
   constructor.
  Check splitting_field_normal _.
  move/SubFieldExtType .
  Check subfx_irreducibleP.
  case/splittingFieldForL.
  Check @PrimePowerField 2 m.
  Check [ fieldExtType _ of [finFieldType of 'F_2 ]].
  rewrite /root.
  apply/polyn.irreducibleP/andP.
  Check @subfx_irreducibleP _.
  rewrite /=.
  constructor; first by case: (size phi) sp m_is_prime => [<- //|[]// <-].
  apply/forallP => q; apply/implyP.
  case: q; apply: poly_ind.
  rewrite /=.
  move/eqP.
  move: q.
  rewrite /=.
  apply (forallPP (idP).
  move=> q.
  rewrite /=.
   
  apply FiniteQuant.Quantified.
  constructor.
  apply/
  Set Printing All.
  apply/implyP.
  move=> ?.
  
End irreduciblity.
  
From codegen Require Import codegen.
Require Import mt.

Definition mersenne_exponent : nat := 19937.
Local Notation p := mersenne_exponent.
Definition V := @PrimePowerField 2 p erefl erefl.
Definition F2 := @PrimePowerField 2 1 erefl erefl.
  


(* Lemma test : target_poly p != 0%R. *)
(*   by rewrite -size_poly_eq0 /=. *)
(*   Defined. *)
(* Eval unfold test in test. *)
(* Print test. *)

Check @FinSplittingFieldFor _ (target_poly p).

Check sval F2 = [finFieldType of 'F_2].
Check FalgType 'F_2.
Check [ringType of 'F_2].
Check [finFieldType of 'F_2].
Check fieldExtType [ringType of 'F_2].
Check finField_galois_generator.
Check @FinSplittingFieldFor [finFieldType of 'F_2].
Check @splittingFieldFor [fieldType of 'F_2].
Check [fieldExtType _ of _].
Check [fieldExtType (sval V) of (sval F2)].
{subfield 'F_p}.
Check @galLgen (sval V).
      (sval F2).
Open Scope ring_scope.
Definition F := Frobenius_aut (let (x, p, _) as s return (2 \in [char sval s]) := V in p).

     = let (x, p, _) as s return (2 \in [char sval s]) := V in p

Lemma test : 2 \in [char (sval V)].
  case: V.
  rewrite //=.
  Defined.
Eval unfold test in test.
  
  move=> ? H

Module Char2.
Section s.
Open Scope ring_scope.
Variable p : nat.
Variable t : (0 < p)%N.
Lemma pdiv_gt2 : (2 <= pdiv (2 ^ p))%N.
Proof. by rewrite /pdiv primes_exp. Qed.

Lemma pred_pdiv_gt0 : (0 < (pdiv (2 ^ p)).-1)%N.
Proof. move: pdiv_gt2; by case: (pdiv _). Qed.

Local Definition map : 'F_2 -> 'F_(2 ^ p).
  move=> [] m H.
  apply/(@Ordinal _ m)/(leq_trans H).
  by rewrite ltnS /Zp_trunc /= prednK pred_pdiv_gt0.
Defined.

Local Definition rmorph : rmorphism map.
 apply GRing.RMorphism.Class.
  case => [][? [][?|[]// ?]|[]// ? [][?|[]// ?]];
   by apply: val_inj; rewrite /= /pdiv primes_exp.
 constructor.
  case => [][? [][?|[]// ?]|[]// ? [][?|[]// ?]];
   by apply: val_inj; rewrite /= /pdiv primes_exp.
 by apply: val_inj; rewrite /= /pdiv primes_exp.
Defined.

Lemma char2 : 2 \in [char 'F_(2 ^ p)].
Proof. by apply (GRing.rmorph_char (RMorphism rmorph)). Qed.

Definition F := Frobenius_aut char2.
End s.
End Char2.
Compute Char2.F p erefl 1.

Module Delay.
Section s.
Definition G : 'F_(2 ^ p).
End s.
End Delay.


Check _ : 'F_(2 ^ p).

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
