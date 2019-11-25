From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
Require Import polyn irreducible.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section test.
  Variable phi : {poly [finFieldType of 'F_2]}.
  Variable pm : prime (2 ^ (size phi).-1 - 1).
  Variable ip : irreducible_poly phi.
  Local Notation m := (size phi).-1.
  
Definition e a :=
  map_tuple (fun j => (iter j (H pm ip)) a)%R
            (iota_tuple (\dim (fullv:{vspace {qpoly phi}})) 0).

Definition independents :=
  [set n |
  [exists (t : (nat_of_ord (n : 'I_m.+1)).-tuple 'F_2 | all (fun x => x != 0)%R t),
  [forall a, (\sum_(i < n) t`_i *: (e a)`_i == 0)]%R] && (n > 0)].

Definition min_dim :=
foldl minn m (map (@nat_of_ord _) (enum independents)).

Lemma min_dim_in : min_dim < m.+1.
Proof.
  rewrite /min_dim.
  elim: (enum independents) => // b l IH.
  rewrite irreducible.foldl_min_cons /minn.
  by case: ifP.
Defined.

Lemma predphi_neq0 : (size phi).-1 != 0.
Proof. by case: m (m_is_prime pm). Qed.

Hint Resolve predphi_neq0.
Lemma min_dim_neq0 : min_dim != 0.
Proof.
  rewrite /min_dim.
  have: ord0 \notin independents.
   by rewrite inE negb_and ltnn orbT.
  rewrite -mem_enum.
  elim: (enum independents) => // x xs IH.
  rewrite in_cons irreducible.foldl_min_cons negb_or => /andP [] x0 /IH r0.
  rewrite /minn.
  case: ifP => //.
  by rewrite eq_sym x0.
Qed.

(* Lemma ind_neq0 : #|independents| != 0. *)
(* Proof. *)

(* Lemma min_dim_neqm : *)
(*   min_dim != m ->  *)
(*   Ordinal min_dim_in \in independents. *)
(* Proof. *)
(*   rewrite inE. *)

Check ord1 : 'I_3.
Lemma basis_e0 : basis_of fullv (e (pi pm 'X))%R.
Proof.
  rewrite basisEfree size_tuple leqnn subvf !andbT.
  apply/freeP => k H i; apply/eqP/negP => /negP Hc.
  case i0: (#|independents| == 0).
   move: k H i Hc .
    elim: (\dim fullv) => //.
   rewrite -sizem.
   move: (card0_eq (eqP i0)).
  rewrite 
  rewrite /independents.
   
Lemma ind_neq0 : 
Proof.
  
  have: Ordinal min_dim_in \in independents.
   rewrite inE.
   apply/negP => /idP/negPn.
   rewrite /= negb_exists => /forallP x.
   move: i Hc.
   case m1: (min_dim <= 1).
    move: m1.
    rewrite leq_eqVlt /leq subSS subn0 (negPf min_dim_neq0) orbF => /eqP m1.
    move: m1 x => -> x.
    have ki1: size [:: k i] == 1 by [].
    move: (x (Tuple ki1)).
    rewrite negb_and negb_forall.
    case na: (~~ all (fun x0 : 'F_2 => x0 != 0%R) (Tuple ki1)) => //=.
     move: na.
     by rewrite andbT Hc.
    move/existsP => [] x0.
    rewrite /= big_ord1 (nth_map 0) ?size_iota ?nth_iota ?addn0.
    rewrite /=.
    rewrite iter.
     => /orP.
    [/allPn|/existsP] [].
     move=> ? /=.
     rewrite mem_seq1 => /eqP -> /negP.
     by rewrite Hc.
    move=> x0 /=.
    rewrite big_ord1 GRing.scaler_eq0 (negPf Hc) negb_imply.
    rewrite negb_or /=.
    apply/negP/negP/idP.
    rewrite h
    rewrite /=.
    rewrite /=.
    rewrite /=.
    negb_all.
    rewrite /=.
    
    move: (x
   rewrite negb_and in x.
   
   apply/existsP.
   apply/negP.
   
   move/negP.
   move/negP.
   set S := negb _.
   rewrite /=.
   apply/negP => /negP.
   rewrite negb_exists_in.
   rewrite -negb_exists.
   rewrite negb_forall_in.
   apply/negP.
   move/negb_forall.
   => /existsP.
   => /negb_exists.
   /negb_forall.
   rewrite /=.
   rewrite /=.
         => . /existsP.
Admitted.

Definition canon_mat' f :=
  let m := \dim (fullv : {vspace {qpoly phi}}) in
  (\matrix_(i < m , j < m) coord e0 i (f e0`_j))%R.

Lemma basis_e0' : basis_of fullv (e0 pm ip).
Proof.
  rewrite basisEfree size_tuple leqnn subvf !andbT.
  apply/freeP.
  
Admitted.

