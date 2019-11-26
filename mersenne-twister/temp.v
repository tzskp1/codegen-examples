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
Lemma predphi_neq0 : m != 0.
Proof. case: m (m_is_prime pm) => //. Qed.
Hint Resolve predphi_neq0.
Canonical qpoly_ringType_phi.
Canonical qpoly_comRingType_phi.

Definition e a :=
  map_tuple (fun j => (iter j (H pm ip)) a)%R (iota_tuple m 0).

Definition independents :=
[set n | [exists (s : {ffun 'I_(nat_of_ord n) -> 'I_m} | true),
[exists (t : (nat_of_ord (n : 'I_m.+1)).-tuple 'F_2 | all (fun x => x != 0)%R t),
[forall a, (\sum_(i < n) t`_i *: (e a)`_(s i) == 0)]%R]]
&& (n > 0)].

Definition independents1 :=
[set n | [exists (s : {ffun 'I_(nat_of_ord n) -> 'I_m} | true),
[exists (t : (nat_of_ord (n : 'I_m.+1)).-tuple 'F_2 | has (fun x => x != 0)%R t),
[forall a, (\sum_(i < n) t`_i *: (e a)`_(s i) == 0)]%R]]
&& (n > 0)].

Lemma ind1_in_ind : independents \subset independents1.
Proof.
  apply/subsetP => x.
  rewrite !inE => /andP [] /existsP [] s0 /andP []
                  _ /existsP [] x0 /andP [] ax Ha xn0.
  rewrite xn0 andbT; apply/existsP; exists s0.
  apply/existsP; exists x0.
  rewrite Ha andbT; move/allP: ax => ax0.
  case: x0 Ha ax0 => [][/=|? ? /= _ _ H].
   rewrite lt0n in xn0.
   by rewrite eq_sym (negPf xn0).
  by rewrite H // in_cons eqxx.
Qed.

Lemma split_sup (R : zmodType) x (f : _ -> R) (x0 : 0 < x) :
  (\sum_(i < x) f i =
   \sum_(i < size [seq x1 <- (enum 'I_x) | f x1 != 0]) 
    f (nth (Ordinal x0) (filter (fun x => f x != 0)%R (enum 'I_x)) i))%R.
Proof.
  elim: x f x0 => // x IH f x0.
  rewrite big_ord_recl /=.
  case x0e : (0 < x); last first.
  - move/negP/negP: x0e.
    rewrite enum_ordS /= -ltnNge /leq subSS subn0 => /eqP x0e {IH}.
    case: ifP => f0 /=.
    * rewrite /= big_ord_recl /=.
      congr (_ + _)%R. set T := size _.
      have->: T = 0.
       subst T; case: x x0e f f0 x0 => //= *.
       have-> //: enum 'I_0 = [::].
       by apply size0nil; rewrite size_enum_ord.
      rewrite !big_ord0 {f0 T x0}.
      move: x0e f => -> f.
      by rewrite !big_ord0.
    * move/negP/negP: f0 => /eqP ->.
      rewrite GRing.add0r.
      set T := size _.
      have->: T = 0.
       subst T; case: x x0e f x0 => //= *.
       have-> //: enum 'I_0 = [::].
       by apply size0nil; rewrite size_enum_ord.
      rewrite !big_ord0 {T x0}.
      move: x0e f => -> f.
      by rewrite !big_ord0.
  - rewrite IH // enum_ordS /=.
    case: ifP => f0.
    * rewrite /= big_ord_recl /=.
      congr (_ + _)%R. set T := size _. set T' := size _.
      have<-: T = T'.
       rewrite /T /T'.
       elim: (enum 'I_x) => //= ??.
       by case: ifP => //= ? ->.
      apply/eq_big => [//|j _].
      congr f. apply/eqP. subst T T'.
      elim: (enum 'I_x) j => /= [[]//|] ? xs IHx.
      case: ifP => //= ? j.
      case j0: (j == 0 :> nat); first by rewrite !(eqP j0).
      case: j j0 => [][]//= j j0 _.
      rewrite ltnS in j0.
      by rewrite (IHx (Ordinal j0)).
    * move/negP/negP: f0 => /eqP ->.
      rewrite GRing.add0r.
      set T := size _. set T' := size _.
      have<-: T = T'.
       rewrite /T /T'.
       elim: (enum 'I_x) => //= ??.
       by case: ifP => //= ? ->.
      apply/eq_big => [//|j _].
      congr f. apply/eqP. subst T T'.
      elim: (enum 'I_x) j => /= [[]//|] ? xs IHx.
      case: ifP => //= ? j.
      case j0: (j == 0 :> nat); first by rewrite !(eqP j0).
      case: j j0 => [][]//= j j0 _.
      rewrite ltnS in j0.
      by rewrite (IHx (Ordinal j0)).
Qed.

Lemma z2z : forall k, (iter k (H0 pm) 0 = 0)%R.
  elim => // k IH.
  rewrite iterS IH.
  have->: (H0 pm 0 = irreducible.H pm ip 0)%R by [].
  by rewrite GRing.rmorph0.
Qed. 

Lemma ind0_ind10 : #|independents| = 0 -> #|independents1| = 0.
Proof.
  move/cards0_eq; rewrite /independents => H; apply/eqP; rewrite cards_eq0.
  have E:
   forall (n : 'I_m.+1), 0 < n ->
   [exists (s : {ffun 'I_(nat_of_ord n) -> 'I_m} | true),
   [exists (t : (nat_of_ord (n : 'I_m.+1)).-tuple 'F_2 | all (fun x => x != 0)%R t),
   [forall a, (\sum_(i < n) t`_i *: (e a)`_(s i) == 0)]%R]] -> False.
   move=> n n0 Hc; have: n \in set0 by rewrite -H inE Hc n0.
   by rewrite in_set0.
  apply/negP => /negP.
  rewrite -proper0 /independents1 => /properP [] _ [] x.
  rewrite inE => /andP [] + x0 _ => /existsP [] s /andP [] _
                 /existsP [] t /andP [] hast sa.
  have st: 0 < size (filter (fun x => x != 0)%R t).
   case: t hast sa => /= + _ + _.
   elim=> //= ?? IH /orP [->//|/IH].
   by case: ifP.
  have so: size (filter (fun x => x != 0)%R t) < (size phi).-1.+1.
   rewrite size_filter; apply/(leq_trans (count_size _ _)).
   by rewrite size_tuple; case x.
  apply/(E (Ordinal so) st)/existsP.
  exists (finfun (s \o (fun y : 'I_(size [seq x1 <- t | x1 != 0%R]) =>
  (nth (0%R, Ordinal x0) (filter (fun x => x.1 != 0)%R (zip t (enum 'I_x))) y).2))).
  apply/existsP; exists (in_tuple (filter (fun x => x != 0)%R t)).
  rewrite /= filter_all /=; apply/forallP => b.
  case b0: (b == 0)%R.
   rewrite !(eqP b0).
   apply/eqP/esym/etrans/eq_big => [|//|? _]; last first.
   rewrite (nth_map 0) ?size_iota ?nth_iota => [|//|//].
   by rewrite z2z GRing.scaler0.
   rewrite big_const /=.
   set T := #| _ |.
   elim: T => // T IHt.
   by rewrite iterS -IHt GRing.addr0.
  rewrite -[X in _ == X](eqP ((forallP sa) b)) /= [X in _ == X]split_sup.
  set T := size (filter _ _). set T' := size (filter _ _).
  have<-: T = T'.
   rewrite /T /T' !size_filter {T T' x0 so st hast sa}.
   case: x t s => /= x.
   elim: x => [? [][]//= _ ?|].
    have-> //: enum 'I_0 = [::].
    by apply size0nil; rewrite size_enum_ord.
   move=> x IH.  
   rewrite ltnS.
   move=> xp t s.
   rewrite enum_ordS /=.
   case: t => [][]//= ? t.
   rewrite GRing.scaler_eq0 negb_or (nth_map 0) ?size_iota ?nth_iota //.
   set T := iter _ _ _ != _.
   have->: T.
    subst T.
    elim: (0 + _) => /= [|n IHn]; first by rewrite b0.
    by rewrite (@GRing.fmorph_eq0 (qpoly_fieldType_phi ip) _ (irreducible.H pm ip)).
   rewrite andbT eqSS => sx.
   congr (_ + _).
   rewrite (IH (leqW xp) (Tuple sx) (finfun (s \o (lift ord0)))) !count_map /=.
   by apply eq_count => y; rewrite /= ffunE.
  apply/eqP/eq_big => [//|i _].
  congr (_ *: _)%R.
   subst T T'.
   set S := [seq _ <- _ | _ ].
   set T := [seq _ <- _ | _ ].
   have->: T = [seq i <- enum 'I_x | t`_(nat_of_ord i) != 0]%R.
    subst T; elim: (enum 'I_x) => // ? l.
    rewrite /= GRing.scaler_eq0 negb_or (nth_map 0) ?size_iota ?nth_iota //.
    set T := iter _ _ _ != _.
    have->: T.
     subst T.
     elim: (0 + _) => /= [|n IHn]; first by rewrite b0.
     by rewrite (@GRing.fmorph_eq0 (qpoly_fieldType_phi ip) _ (irreducible.H pm ip)).
    by rewrite andbT; case: ifP => // + ->.
   subst S T => {hast sa st so}.
   case: t i => /= t _.
   elim: t => [[]//|? l IH /=].
   case: ifP => //= a0 i0.
    case: i0 => [][|i i0].
     case: x x0 IH s => [][]// x x0 IH s.
     by rewrite /= enum_ordS /= a0.
    move: (i0) => i1. rewrite ltnS in i0.
    rewrite /= (IH (Ordinal i0)) /=.
    
   case: ifP => /= a0 i0.
    case: i0 => [][|i i0].
     case: x x0 IH s => [][]// x x0 IH s.
     by rewrite /= enum_ordS /= a0.
    move: (i0) => i1. rewrite ltnS in i0.
    rewrite /= (IH (Ordinal i0)) /=.
    
    have: (enum 'I_x != [::]).
     case: x x0 {IH s} => [][]// *.
     by rewrite /= enum_ordS.
    case: (enum 'I_x) => //=.
    rewrite /=.
    set T := [seq _ <- _| (_ :: _)`_ _ != _]%R.
    have: T != [::].
    case: x x0 IH s => [][]// x x0 IH s.
    rewrite /= enum_ordS /= a0.
    case: l i1 i0 s => //= *.
    case: ifP => //.
    rewrite /=.
    case: i
    rewrite /=.
    move=> ? t. 
    rewrite /=.
    rewrite /=.
    rewrite /=.
    rewrite /=.
    rewrite /=.
    rewrite /=.
    rewrite /=.
   rewrite /S.
   rewrite nth_filter.
    
    rewrite /T.
   set T := [seq _ | _ <- _].
   set T' := [seq _ <- _ | _ ].
   case: t {hast sa st so} => //.
   elim: t => //.
   rewrite 
   rewrite (nth_map 0%R).
  rewrite /= ffunE /=.
  rewrite /=.
   Check 
   have: 
   Check in_tuple.
   Check IH (Tuple sx).
  have: { s' : {ffun 'I_(size (filter (fun x => x != 0)%R t)) -> 'I_m} |
    [forall a, \sum_(i < x) t`_i *: (e a)`_(s i)
    == \sum_(i < size (filter (fun x => x != 0)%R t)) t`_i *: (e a)`_(s' i)]%R }.
  exists (finfun (s \o (fun y : 'I_(size [seq x1 <- t | x1 != 0%R]) =>
   (nth (0%R, Ordinal x0) (filter (fun x => x.1 != 0)%R (zip t (enum 'I_x))) y).2))).
  apply/forallP => y; rewrite split_sup.
   case: x t s y => /= x.
   elim: x => [/= _ [][]//= _ ??|].
    have-> //: enum 'I_0 = [::].
    by apply size0nil; rewrite size_enum_ord.
   move=> x IH.  
   rewrite ltnS.
   move=> xp t s y.
   rewrite enum_ordS /=.
   case: t => [][]//= ? t.
   rewrite GRing.scaler_eq0 negb_or (nth_map 0) ?size_iota ?nth_iota //.
   rewrite /=.
    
   case: 
   
   rewrite !count_filter /=.
   rewrite /=.
  
  Check (split_sup (fun (i : 'I_x) => t`_i *: (e y)`_(s i))%R).
  apply/eqP/etrans/eq_big => [|//|z _]; last first.
   rewrite /= (nth_map 0) ?size_iota ?nth_iota ?add0n ?ffunE //=.
   rewrite /=.
  Check partition_big _.
   
   have zx: z < x.
    case: z => z /= zs.
    by rewrite (leq_trans zs) // size_filter
               (leq_trans (count_size _ _)) // size_tuple.
   set T := (_ *: _)%R.
   have: T = (t`_(nth (0, Ordinal x0) [seq x0 <- zip t (enum 'I_x) | x0.1 != 0] z).2
             *: iter (s (Ordinal zx)) (H0 pm) y)%R.
   case tz0: (t`_z == 0)%R.
    rewrite /T !(eqP tz0) !GRing.scale0r //.
    rewrite /T /=.
   
   Check x.
   
    case: x => //.
     zs.
    rewrite /=.
   
   rewrite //.
   rewrite //.
   rewrite //.
   rewrite /=.
    
   rewrite 
   (nth_map (0%R, Ordinal x0)).
  //=.
   
  rewrite /=.
  done.
  rewrite /=.
  
  Check Ordinal x0.
  Check ord0 : 'I_x.
  Check s.
  Check t.
  Check ord0 : (Zp_finZmodType (Zp_trunc (pdiv 2)).+1 * ordinal_finType x)%type.
  exists (finfun (s \o (fun y : 'I_(size [seq x1 <- t | x1 != 0%R]) =>
     (nth _ (filter (fun x => x.1 != 0)%R (zip t (enum 'I_x))) y).2))).
  exists (finfun (s \o (fun x : 'I_(size [seq x1 <- t | x1 != 0%R]) => (nth _ (filter (fun x => x.1 != 0)%R
                (zip t (enum 'I_x))) x).2))).
  
  Compute tally (iota 4 3).
  Compute index 0 (iota 4 3).
  Compute enum 'I_3.
  Compute iota_tuple 3 0.
  (filter (fun x => x != 0)%R t)
  Check all2 .
  Check zip.
   Check finfun _.
   
  Check (filter (fun x => x != 0)%R t).
  filter (fun x => x != 0)%R t
  Check (fun y => _).
   exists (in_tuple (filter (fun x => x != 0)%R t)).
  
   
  move/(E _).
  case allt: (all (fun x => x != 0)%R t).
   move=> _ s.
   by apply/(E x x0)/existsP; exists t; rewrite allt s.
   
   [] /hasP [] x0 x01 x00 H0 x0'.
  apply (E x x0').
  
  case x0: (x == 0).
   rewrite /=.
   move=> /E.
   rewrite /=.
  
  
Definition min_dim :=
foldl minn m (map (@nat_of_ord _) (enum independents)).

Lemma min_dim_in : min_dim < m.+1.
Proof.
  rewrite /min_dim.
  elim: (enum independents) => // b l IH.
  rewrite irreducible.foldl_min_cons /minn.
  by case: ifP.
Defined.

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

Lemma basis_e0 : basis_of fullv (e (pi pm 'X))%R.
Proof.
  rewrite basisEfree size_tuple -dimvm leqnn subvf !andbT.
  apply/freeP => k H i; apply/eqP/negP => /negP Hc.
  case i0: (#|independents| == 0).
   elim m => //.
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

