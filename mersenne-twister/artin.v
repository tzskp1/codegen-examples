From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
Require irreducible.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section artin.
Variable B : finFieldType.
Variable E : fieldExtType B.
Variable u : nat.
Variable Xs : u.-tuple {rmorphism E -> E}%R.
Variable a : E.
Hypothesis a_neq0 : a != 0%R.

Definition e0 := map (fun j => tnth Xs j a) (enum 'I_u).
Lemma e0_s : size e0 == u.
Proof. by rewrite /e0 size_map size_enum_ord. Qed.
Definition e := Tuple e0_s.

Definition independents :=
  [set n |
   [exists (t : (nat_of_ord (n : 'I_u.+1)).-tuple B | all (fun x => x != 0)%R t),
    (\sum_(i < n) t`_i *: e`_i == 0)%R]].

Definition min_dim :=
foldl minn u
      (filter (fun x => x > 0)%N (map (@nat_of_ord _) (enum independents))).

Lemma zero_proof : 0 < u.+1. Proof. by []. Qed.
Definition zero := Ordinal zero_proof.

Lemma zero_in_inds : zero \in independents.
Proof.
  rewrite inE.
  apply/existsP/(ex_intro _ (@Tuple _ _ [::] _)).
  by rewrite /= big_ord0.
Qed.

Lemma eE (i : 'I_u) : (e`_i = tnth Xs i a)%R.
Proof.
  case u0: (u > 0).
   rewrite (nth_map (Ordinal u0)) ?size_enum_ord //.
   have -> //: (nth (Ordinal u0) (enum 'I_u) i) = i.
   apply/val_inj.
   by rewrite /= nth_enum_ord.
  suff: false by [].
  move: u0 i.
  rewrite lt0n => /negP/negP /eqP ->.
  by case.
Qed.

Lemma e_neq0 (i : 'I_u) : (e`_i != 0)%R.
Proof.
  rewrite eE -[X in _ != X](GRing.rmorph0 (tnth Xs i)).
  apply/negP => /eqP /GRing.fmorph_inj /eqP.
  by apply/negP.
Qed.

Lemma min_dim_in : min_dim < u.+1.
Proof.
  rewrite /min_dim.
  elim: (enum independents) => //= b l IH.
  case: ifP => //.
  rewrite irreducible.foldl_min_cons /minn.
  by case: ifP.
Qed.

Lemma min_dim_in_inds y :
  y \in independents -> 0 != y ->
  Ordinal min_dim_in \in independents.
Proof.
  move=> yi y0.
  rewrite -mem_enum.
  suff: min_dim \in
      (filter (fun x => x > 0)%N (map (@nat_of_ord _) (enum independents))).
   elim: (enum independents) => //= b l IH.
   case: ifP.
    rewrite !in_cons !eqE => + /orP [/eqP /= <-|/IH ->].
     by rewrite eqxx.
    by rewrite orbC.
   by rewrite in_cons orbC => + /IH ->.
  apply/irreducible.foldl_minn_in/hasP.
  exists (nat_of_ord y) => //.
  rewrite mem_filter lt0n eq_sym y0 /= mem_map ?mem_enum //.
  move=> [] ? ? [] ? ? ?.
  by apply/val_inj.
Qed.

Lemma min_dim_eq1 y :
  0 < u -> y \in independents -> 0 != y -> min_dim == 1 = false.
Proof.
  move=> u0 Hy y0; apply/negP => /eqP mm.
  move: (min_dim_in_inds Hy y0).
  rewrite inE /= mm => /existsP [][][]// b []//= _.
  rewrite big_ord_recr big_ord0 /= GRing.add0r andbT => /andP [].
  rewrite GRing.scaler_eq0 => /negPf ->.
  set T := match e0 with | [::] => 0%R | x :: _ => x end.
  have->: T = (e`_(Ordinal u0))%R by [].
  by rewrite (negPf (e_neq0 _)).
Qed. 

Lemma min_dim_min x :
  x \in independents -> 0 < x -> min_dim <= x.
Proof.
  rewrite -mem_enum /min_dim.
  elim: (enum independents) => //= ?? IH.
  case: ifP.
   rewrite !in_cons => + /orP [/eqP <-|/IH].
    by rewrite irreducible.foldl_min_cons geq_minl.
   rewrite irreducible.foldl_min_cons /minn.
   by case: ifP => // /leq_trans H + H' /H' /H /ltnW.
  by rewrite in_cons => + /orP [/eqP ->|/IH H /H //] => ->.
Qed.

Lemma min_dim_neq0 : 0 < u -> min_dim != 0.
Proof.
  rewrite /min_dim.
  elim: (enum independents); first by rewrite /= lt0n.
  move=> x xs /=.
  case: ifP => //.
  rewrite irreducible.foldl_min_cons => + IH /IH ?.
  rewrite /minn.
  case: ifP => // ?.
  by rewrite lt0n.
Qed.
End artin.

Lemma ltn_wf : well_founded (fun x y => x < y).
Proof.
  elim => [//|? IHn]; constructor => y.
  rewrite ltnS leq_eqVlt => /orP [/eqP -> //|].
  by case: IHn => H /H.
Qed.

Section artin.
Variable B : finFieldType.
Variable E : fieldExtType B.

Lemma artin's_lemma u (Xs : u.-tuple {rmorphism E -> E}%R) :
  (forall i j, i != j -> exists t, tnth Xs i t != tnth Xs j t) ->
  forall k : 'I_u -> B, (forall a, (\sum_(i < u) k i *: (e Xs a)`_i)%R = 0%R)
  -> forall i : 'I_u, k i = 0%R.
Proof. 
move=> distXs; elim: (ltn_wf u) Xs distXs => {u} u _ IH Xs distXs.
case: u Xs distXs IH => [????? []//|u Xs distXs IH].
case: u Xs distXs IH => [Xs distXs IH k /(_ 1%R)/eqP|u Xs distXs IH].
 rewrite big_ord1 eE GRing.rmorph1
        GRing.scaler_eq0 GRing.oner_eq0 orbF => /eqP k0 [][]// ?.
  by rewrite -[RHS]k0; congr k; apply/val_inj.
 
case: u Xs distXs IH => [Xs distXs IH k H|u Xs distXs IH].

suff : exists c, c \in independents Xs.
min_dim
 set Oi := @Ordinal 2 0 erefl.
 set Ti := @Ordinal 2 1 erefl.
 case:(distXs Oi Ti _) => // t t12; move: (H t).
 rewrite !big_ord_recr big_ord0 !eE /= GRing.add0r => H1 i.
 apply/eqP/negP => /negP ki.
 move/eqP: H1.
 rewrite GRing.addr_eq0.
 case: i ki => [][|[]//] i ki.
 move/eqP/(f_equal (fun x => (k (Ordinal i))^-1 *: x))%R.
 have ->: (widen_ord (leqnSn 1) ord_max = Ordinal i) by apply/val_inj.
 rewrite GRing.scalerK // -GRing.scalerN GRing.scalerA GRing.scalerN.
 apply/eqP.
 rewrite -GRing.addr_eq0.
 apply/negP.
 
 rewrite GRing.scalerAl.
 Check GRing.divrI _.
 Check GRing.mulKr  _  _.
 Check GRing.invrK _.
 Check GRing.invr_inj _.
 Check (@GRing.scaler_injl _ _ (k (Ordinal i)) _ _).
 move/(@GRing.scaler_injl _ _ (k (Ordinal i))).
 move/(@GRing.mulrI _ (k (Ordinal i)) _).
 
  Check GRing.mulVr  _.
 
 rewrite /=.
Check GRing.mulrI _ _.


 
 rewrite eE GRing.fmorph_eq0 (negPf a_neq0).
case: u Xs distXs IH => [Xs distXs IH|u Xs distXs IH].
 apply/freeP => k /eqP.
 rewrite !big_ord_recr big_ord0 !eE /= GRing.add0r.
 set O := k _; set T := k _ => /eqP.
 set Oi := widen_ord _ _; set Ti := ord_max.
 case:(distXs Oi Ti _) => // t t12 H.
 have: (O *: (tnth Xs Oi a * tnth Xs Oi t)
      + T *: (tnth Xs Ti a * tnth Xs Ti t) = 0)%R.
  rewrite !GRing.scalerAl.
  rewrite GRing.mulrDl.
  rewrite -!GRing.rmorphM.
 
 
 
  + [][]// ?.
 
 
apply/freeP => k H i; apply/eqP/negP => /negP Hc.

 
case u0: (0 < u); last first.
 move/negP/negP: u0.
 rewrite -ltnNge /leq subSS subn0 => /eqP u0.
 by move: u0 i => -> [].
case mdu: (min_dim Xs a == u).
 
 

case indu: (has (fun x => (x \in independents Xs a) && (0 != x)) (enum 'I_u.+1));
 last first.
 move/hasPn: indu => {u0}.
 apply/hasPn.
 elim: u k i Hc Xs H => [+ [] //|] u IHu k i Hc Xs H.
 case: i Hc => i iu Hc.
  case iu': (i == u).
   move: H.
   rewrite big_ord_recr /=.
   have iu'': i < u.
  
 Check IHu (k \o lift i) _ _.
 Check lift i i.
 rewrite /=.
 apply/hasPn => y.
 rewrite /=.
 apply/negP => /negP /hasPn.
 rewrite negb_and.
 
   move=> ?.
  
  have: (min_dim > 1).
   rewrite ltnNge leq_eqVlt.
   apply/negP => /orP []; first by rewrite min_dim_eq1.
   rewrite /leq subSS subn0 => /eqP.
    rewrite /min_dim.
   rewrite ltn_neqAle.
   rewrite /min_dim.
  
  
  Check support .
  
  (forall x i, @X_neq0 (tnth Xs x) i) -> (forall x i j, @X_hom (tnth Xs x) i j) ->
  forall (cs : m.-tuple K), (\sum_(i < m) cs`_i * (tnth Xs i s) == 0)%R ->
  forall i : 'I_m, (cs`_i == 0)%R.


Check _ : @fieldOver_vectType B E [aspace of 1%VS].
Check [vectType K of _].
Check (e _) : u.-tuple [vectType K of _].


(* Lemma min_dim0E : *)
(*   min_dim == 0 -> *)
(* ~~ [exists (t : m.-tuple 'F_2 | has (fun x => x != 0)%R t), *)
(*     (\sum_(i < m) t`_i *: iter i H (pi 'X) == 0)%R]. *)
(* Proof. *)
(*   move=> Hc. *)
(*   apply/negP => /existsP [] x /andP [] /hasP [] y yx y0 t0. *)
  
  (* case hasy: (size (filter (fun x => x != 0)%R x) > 1). *)
  (*  have sm: (size (filter (fun x => x != 0)%R x) < m.+1). *)
  (*   rewrite size_filter prednK //. *)
  (*   apply/(leq_ltn_trans (count_size _ _)). *)
  (*   rewrite size_tuple. *)
  (*   by case: (size phi) m_is_prime. *)
  (*  set s := Ordinal sm. *)
  (*  have : *)
  (*  [exists (t : (nat_of_ord s).-tuple 'F_2 | all (fun x => x != 0)%R t), *)
  (*   (\sum_(i < s) t`_i *: iter i H (pi 'X) == 0)%R]. *)
  (*   apply/existsP. *)
  (*   exists (@Tuple _ _ (filter (fun x => x != 0)%R x) (eqxx _) : s.-tuple 'F_2). *)
  (*   rewrite filter_all /= -[X in _ == X](eqP t0). *)
  (*   apply/eqP/etrans. *)
  (*        apply/eq_big => [//|k _]. *)
  (*        rewrite nth_map. *)
    
  (*   elim: (size phi).-1 => //. *)
  (*   rewrite  *)
  (* (\sum_(i < s) (filter (fun x => x != 0)%R x)`_i *: iter i H (pi 'X) == 0)%R. *)
  (* case hasy: (has (fun x => (x != 0) && (x != y))%R x). *)
   

Lemma basis_e0 : basis_of fullv e0.
Proof.
  rewrite basisEfree size_tuple leqnn subvf !andbT.
  apply/freeP => k.
  set T := (\sum_(_ < _) _)%R.
  have {T} ->: T = (\sum_(i < \dim fullv) k i *: (iter i H) (pi 'X))%R.
   subst T.
   apply eq_big => //= i _.
   congr (_ *: _)%R.
   by rewrite (@nth_map _ 0 _ 0%R (fun j => iter j H0 (qpolify phi_gt1 'X)) i
                     (iota 0 (\dim fullv))) ?size_iota // nth_iota ?add0n.
  case mm: (min_dim == 0).
  
   have O: 0 < m
    by rewrite -subn1 ltn_subRL addn0.
   
   have: Ordinal O \in independents.
    rewrite -mem_enum.
    move: mm.
    rewrite /min_dim.
    elim: (enum independents) => [/= /eqP s0|a l IH].
     suff: false by [].
     by move: s0 m_is_prime => ->.
    rewrite foldl_min_cons /= /minn.
    case: ifP => [_ /eqP a0|_ /IH].
     by rewrite in_cons eqE /= a0 eqxx.
    by rewrite in_cons orbC => ->.
   rewrite inE => /existsP []. 
   case=> //.
   rewrite /=.
    rewrite 
     rewrite /=.
    /independents.
  move=> H1 i; apply/eqP/negP => /negP ki.
  
  Check enum independents.
  
  
  elim: (\dim fullv) k => [++ []//|n IHn k /eqP].
   rewrite big_ord_recr /= GRing.addr_eq0 => /eqP + i.
   case ni : (i == Ordinal (ltnSn n)).
     move/eqP: ni => -> /eqP.
   set T := k _.
   case kn: (T == 0)%R.
    move/eqP: (kn) => ->.
    rewrite /= GRing.scale0r GRing.addr0 => /IHn H i.
    case ni : (i == Ordinal (ltnSn n)).
     subst T.
     by move/eqP: ni kn => -> /eqP ->.
    have ni': i < n.
     case: i ni => i i'.
     rewrite eqE /= => ni.
     move: i'.
     by rewrite leq_eqVlt ltnS eqSS ni.
    move/H: (Ordinal ni') => <-.
    congr k.
    by apply/val_inj.
   rewrite /=.
    case:
    rewrite ltn_neqAle.
   rewrite eqE /=.

Proof.
  move=> H1 H2 cs H i.
  apply/negP => /negP Hc.
  move: m cs Xs H i Hc H1 H2.
  elim.
   case => [][]// ????.
   by rewrite /= nth_nil eqxx.
  suff H0:
    forall (m : nat) (cs : m.-tuple K) (Xs : m.-tuple (nat -> K)),
      (forall c, tnth cs c != 0)%R ->
      (\sum_(i < m) cs`_i * tnth Xs i s)%R == 0%R ->
      forall i : 'I_m, (cs`_i)%R != 0%R ->
      (forall (x : 'I_m) (i0 : nat), X_neq0 (tnth Xs x) i0)
      -> (forall (x : 'I_m) (i0 j : nat), X_hom (tnth Xs x) i0 j) -> False.
  move=> m IHm cs Xs.
  case Hcc: [forall c, tnth cs c != 0%R].
   by move/forallP/H0: Hcc; apply.
  move/negP/negP: Hcc.
  rewrite negb_forall => /existsP [] x.
  have->: ~~ (tnth cs x != 0%R) = (tnth cs x == 0%R)
   by case:(tnth cs x == 0%R).
  move=> tcsx + i.
  case ix: (x == i).
   move/eqP: ix tcsx => -> /eqP /= tcsx _. 
   have<-: (tnth cs i = cs`_i)%R
    by apply tnth_nth.
   by rewrite tcsx eqxx.
  
  
  move/eqP.
  move/negP.
  move/eqP.
  move/negP.
  move/negP.
  
  move/eqP.
  
  rewrite negb
  rewrite negb_orb
    forall cs : m.-tuple K,
    (forall c, tnth cs c != 0)%R ->
    (\sum_(i < m) cs`_i * tnth Xs i s)%R == 0%R ->
    forall i : nat, (cs`_i)%R != 0%R -> False.
  
  
   i Hc.
  apply/forallP/negP => /negP Hcc.
  rewrite  negb_forall in Hcc.
  case/existsP: Hcc.
     => /= Hc.
  (forall (x : 'I_m) (i : nat), X_neq0 (tnth Xs x) i) ->
  (forall (x : 'I_m) (i j : nat), X_hom (tnth Xs x) i j) ->
  forall cs : m.-tuple K,
  (\sum_(i < m) cs`_i * tnth Xs i s)%R == 0%R ->
  forall i : nat, (cs`_i)%R == 0%R.
  move=> H1 H2.
  (forall c : 'I_m, tnth cs c != 0%R)
  rewrite /X_neq0 /X_hom => H1 H2 cs.

End artin.
