From mathcomp Require Import all_ssreflect all_algebra all_field.

Section irreduciblity.
Variable m : nat.
Variable phi : {poly [finFieldType of 'F_2]}.
Hypothesis pm : prime (2 ^ m - 1).
Hypothesis sp : (size phi).-1 = m.

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

Definition stab a : {set 'I_(2 ^ m)} :=
[set n | ('X ^ (nat_of_ord n) * a %% phi == a %% phi)%R].

Lemma foldl_min_cons x y z : foldl minn x (y :: z) = minn y (foldl minn x z).
Proof.
  elim: z x y => [*| ? z IH x y] /=;
  by rewrite minnC // -IH /= minnAC minnC.
Qed.

Definition min_stab a :=
foldl minn (2 ^ m).-1
      (filter (fun x => x > 0) (map (@nat_of_ord _) (enum (stab a)))).

Lemma gap_exp_num : size phi <= (2 ^ m) - 1.
Proof.
   case: (size phi) sp m_is_prime => [<-|m' <-] //=.
   rewrite (erefl : 2 = 1 + 1) Pascal.
   rewrite subn1 big_ord_recr !exp1n binn !mul1n /= addn1.
   case: m' => // m'.
   rewrite big_ord_recr !exp1n !mul1n binSn muln1.
   case: m' => // m' _.
   rewrite big_ord_recr !exp1n !mul1n /= -addnA.
   apply/leq_trans/leq_addl.
   by rewrite -[X in X < _]add0n ltn_add2r muln1 bin_gt0 ltnW.
Qed.

Definition min_stab_ord (a: {poly [finFieldType of 'F_2]}): ordinal (2 ^ m).
  have H: (min_stab a < 2 ^ m).
   rewrite /min_stab.
   elim: [seq _ | _ <- _] => [|c l IH].
    by case: (2 ^ m) pm.
   apply/leq_ltn_trans/IH => {IH} /=.
   by case: ifP => //; rewrite foldl_min_cons geq_minr.
 by apply (Ordinal H).
Defined.

Lemma phi_is_not_zero' : size phi > 0.
Proof. by case: (size phi) sp m_is_prime=> [<-|/= ? ->]. Qed.

Lemma power_gt0 : 0 < 2 ^ m.
Proof. by case: (2 ^ m) pm. Qed.
Hint Resolve phi_is_not_zero' power_gt0 : core.

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

Lemma phi_is_not_zero : lead_coef phi != 0%R.
Proof. by rewrite lead_coef_eq0 -size_poly_gt0. Qed.

Lemma min_stab_in a y :
  y \in stab a -> 0 != y ->
  min_stab a \in (filter (fun x => x > 0) (map (@nat_of_ord _) (enum (stab a)))).
Proof.
  case: y => y Hy1 Hy2 y0.
  apply/foldl_minn_in/hasP/ex_intro2;
    last by rewrite prednK; first apply/Hy1.
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
  elim: (enum (pred_of_set (stab a))) => [|a' l IH /=].
   by rewrite -subn1; case: (2 ^ m - 1) pm.
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
   apply: (min_stab_in _ _ ys y0).
  elim: b => [|b IHb]; first by rewrite !mul0n GRing.mul1r.
  rewrite mulSn -exprnP GRing.exprD -GRing.mulrA !exprnP -modp_mul.
  move/eqP: IHb => ->.
  by rewrite modp_mul H1.
Qed.

Lemma div_ord (a : nat) y (x : ordinal y) : ordinal y.
  apply/(@Ordinal _ (x %% a))/(leq_ltn_trans (leq_mod _ _)).
  by case: x.
Defined.

Lemma p_ord : ordinal (2 ^ m).
  have H: 2 ^ m - 1 < 2 ^ m.
   case: (2 ^ m) pm => // n.
   by rewrite subn1.
  apply: (Ordinal H).
Defined.

Lemma one_ord : ordinal (2 ^ m).
 have H: 1 < 2 ^ m.
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
  move/eqP: (min_stab_cond a (x %/ min_stab a) x H x0) ->.
  rewrite modp_mul dvdn_addr ?dvdn_mull // => H0.
  case x0': (0 != div_ord (min_stab a) _ x).
   have: div_ord (min_stab a) _ x \in stab a by rewrite inE H0.
   move/(fun x => min_stab_min a _ x x0') => H1.
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
  move: (min_stab_cond a 1 y Hy Hy').
  by rewrite mul1n.
Qed.

Lemma irreduciblity_equiv :
reflect (irreducible_poly phi)
(('X ^ 2 %% phi != 'X %% phi) && ('X ^ (2 ^ m)%N %% phi == 'X %% phi))%R.
Proof.
apply/(iffP idP).
* case/andP => H1 H2.
  have H: p_ord \in stab 'X
   by rewrite inE -exprnP GRing.mulrC -GRing.exprS /= subn1 prednK.
  case/min_stab_dvd: (H) pm => + /primeP [] o pm' => /pm' {pm'}.
  have: one_ord \notin stab 'X by rewrite inE -exprnP GRing.mulrC -GRing.exprS.
  move/(min_stab_neq1 _ _ H) => -> /= => [x2m1|]; last by case: (2 ^ m - 1) o.
  constructor; first by case: (size phi) sp m_is_prime => [<- //|[]// <-].
  move=> q.
  apply/andP; split.
  
   rewrite GRing.exprD.
   rewrite GRing.mulrA. 
   GRing.exprD -GRing.mulrA !exprnP -modp_mul.
  
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
