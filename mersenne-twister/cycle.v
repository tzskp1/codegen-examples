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
rewrite big_ord_recl mulnDr /= -IHb mulnBl !subn1 -mulnBl mulnS expnD.
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

Lemma irreduciblity_equiv :
reflect (irreducible_poly phi)
(('X ^ 2 %% phi != 'X %% phi)%R && (('X ^ 2) ^ m %% phi == 'X %% phi)%R).
Proof.
  apply/(iffP idP).
  
End irreduciblity.
  
From codegen Require Import codegen.
Require Import mt.

Definition mersenne_exponent : nat := 19937.
Local Notation p := mersenne_exponent.
Definition V := @PrimePowerField 2 p erefl erefl.
Definition F2 := @PrimePowerField 2 1 erefl erefl.
  

Section roots.
Variable p : nat.
Local Definition pseq : seq [finFieldType of 'F_2] :=
match p with
| 0%N | 1%N => [::]
| S (S p') => 0%R :: (-1)%R :: mkseq (fun _ => 0%R) p' ++ [:: 1%R]
end.

Local Lemma largest_degree : last 1%R pseq != 0%R.
rewrite /pseq.
case: p => []//[]// q /=.
by rewrite last_cat /=.
Qed.

(* X ^ p - X = 0 *)
Definition target_poly : {poly [finFieldType of 'F_2]} :=
  Polynomial largest_degree.
End roots.

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
