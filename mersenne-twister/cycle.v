From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require Import polyn mt.
Require irreducible BinNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section phi.
Variables w n m r : nat.
Variable a : w.-tuple [finFieldType of 'F_2].

Local Open Scope ring_scope.
Definition phi' :=
  ('X ^+ n + 'X ^+ m) ^+ (w - r) * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ r
  + \sum_(i < r.-1) a`_i *: ('X ^+ n + 'X ^+ m) ^+ (w - r)
                     * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ (r.-1 - i)
  + \sum_(i < w - r.-1)
     a`_(r.-1 + i) *: ('X ^+ n + 'X ^+ m) ^+ (w - r - i).
End phi.

Lemma a32 : size ([:: 1; 0; 0; 1; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 1; 0; 1;
                     1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 1]: seq 'F_2)%R == 32.
Proof. by []. Qed.
Definition phi := phi' 624 397 31 (Tuple a32).
Local Definition f := companionmx phi.

Require Import Extraction.
Require Import ExtrOcamlNatInt.
Definition cphi := phi : seq 'F_2.
Extraction "phi.ml" cphi.

Section irreducible_cyclic.
Variable phi : {poly [finFieldType of 'F_2]}.
Local Notation m := (size phi).-1.
Hypothesis pm : prime (2 ^ m - 1).
Hypothesis (ip : irreducible_poly phi).

Local Lemma phi_gt1 : size phi > 1.
Proof. by case ip. Qed.

Local Canonical qpoly_ringType_phi :=
  Eval hnf in qpoly_ringType phi_gt1.
Local Canonical qpoly_comRingType_phi :=
  Eval hnf in qpoly_comRingType phi_gt1.
Local Definition pi := canon_surj phi_gt1.
Definition qpoly_fieldType_phi := Eval hnf in qpoly_fieldType ip.
Local Lemma char2_V : 2 \in [char {qpoly phi}]%R.
Proof.
by apply/(GRing.rmorph_char pi)/(GRing.rmorph_char (polyC_rmorphism _)).
Qed.
Local Definition H0 : {qpoly phi} -> {qpoly phi} := Frobenius_aut char2_V.
Local Definition rmH : rmorphism (H0 : qpoly_fieldType_phi -> _).
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
Local Definition H := RMorphism rmH.

(* Check iter . *)
(* Check <[(H (pi 'X))%R]>%VS. *)
(* Check (agenv (1%VS + <[(H (pi 'X))%R]>%VS)). *)
(* Check <<1%VS; (H (pi 'X))%R>>%VS. *)
(* map_tuple (fun x => H x) *)

Lemma dimvm : m = \dim (fullv : {vspace {qpoly phi}}).
 by rewrite /m dim_polyn.
Defined.

Lemma expHpE : iter m H (pi 'X)%R = pi ('X ^ (2 ^ m)%N)%R.
Proof.
  elim: m => // p' IHp.
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

Local Definition e0 :=
  map_tuple (fun j => (iter j H) (pi 'X))%R
            (iota_tuple (\dim (fullv:{vspace {qpoly phi}})) 0).

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
                      (iota 0 (\dim fullv))) ?size_iota // nth_iota ?add0n //.
   elim: (\dim fullv) k => [++ []//|n IHn k].
   rewrite big_ord_recr /=.
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
   move/eqP.
   rewrite GRing.addr_eq0.
   move/eqP.
   rewrite /=.
    case:
    rewrite ltn_neqAle.
   rewrite eqE /=.
   
   case: 
   rewrite dimvm.
    apply/val_inj.
    compute.
    apply/val_inj.
    rewrite /=.
    set T := 0%R.
    last by case: i => i H; rewrite size_tuple.
    rewrite /H0 !GRing.Frobenius_autE.
    case: (x i) => [][|[]//] j.
    * have->: (Ordinal j = 0)%R by apply/val_inj.
      by rewrite !GRing.scale0r GRing.expr0n.
    * have->: (Ordinal j = 1)%R by apply/val_inj.
      by rewrite !GRing.scale1r.
   set T := (\sum_(_ < _) _)%R.
   have {T} ->: T = H (\sum_(i < \dim fullv) (x i *: e1`_i))%R.
    subst T.
    apply/esym/(big_morph H).
    move=> y z.
    rewrite /H /H0 /= GRing.Frobenius_autD_comm //.
    by apply/eqP; rewrite eqE /= GRing.mulrC.
    by rewrite GRing.rmorph0.
  

Local Definition e1 :=
  map_tuple (fun j => pi 'X ^+ j)%R
            (iota_tuple (\dim (fullv:{vspace {qpoly phi}})) 0).

Lemma piZ a x : (pi (a *: x) = a *: pi x)%R.
Proof.
  apply/val_inj.
  by rewrite /= -modp_scalel.
Qed.

Lemma basis_e1 : basis_of fullv e1.
Proof.
  Admitted.
  (* rewrite basisEdim size_tuple leqnn andbT. *)
  (* rewrite span_def. *)
  (* apply/subvP => [][] /=. *)
  (* apply:poly_ind => //=. *)
  (*  move=> i ?. *)
  (*  have->: NPoly i = 0%R by apply/val_inj. *)
  (*  done. *)
  (*  rewrite //=. *)
   
  (*  move/eqP/eqP: (i). *)
  (*  rewrite size_polyC eqxx sub0n. *)
  (* rewrite inE. *)
  (*  move/eqP/eqP. *)
  (* rewrite /=. *)
  
  (*  move=> ? ?. *)
  (*  apply/eqP/eqP. *)
  (*  rewrite  *)
  (*  rewrite /= inE. *)
  (* rewrite /= -dimvm. *)
  (* elim: (size phi).-1 x => //. *)
  (* rewrite basisEfree size_tuple leqnn subvf !andbT. *)
  (* rewrite /e1 /= -dimvm freeE. *)
  (* apply/forallP => [][]x i. *)
  (* rewrite /=. *)
  (* rewrite (nth_map 0%R). *)
  (* case xs: (x == (size phi).-2). *)
  (*  move/eqP: xs => -> /= ?. *)
  (*  rewrite /=. *)
  (* rewrite /=. *)
  (* apply/freeP => k. *)
  (* rewrite map_iota. *)
  (* elim: (iota 0 (size phi).-1). *)
  (*  by rewrite /= nil_free. *)
  (* move=> x xs IHx. *)
  (* rewrite /= free_cons IHx andbT /=. *)
  (* rewrite /=. *)
  (* move eIe: (enum 'I_(size phi).-1) => eI. *)
  (* elim: eI (size phi).-1 eIe. *)
  (*  move=> /(f_equal size). *)
  (*  rewrite size_enum_ord /= => s0. *)
  (*  suff: false by []. *)
  (*  move: s0 (irreducible.m_is_prime pm). *)
  (*  by rewrite /irreducible.m => ->. *)
  (* move=> x xs. *)
  (* rewrite /=. *)
  
  (* elim: (size phi).-1 (irreducible.m_is_prime pm). *)
  
  (* set T := (\sum_(_ < _) _)%R. *)
  (* have {T} ->: T = (\sum_(i < \dim (fullv : {vspace {qpoly phi}})) k i *: pi 'X ^+ i)%R. *)
  (*  subst T. *)
  (*  apply eq_big => // i _. *)
  (*  congr (_ *: _)%R. *)
  (*  rewrite -GRing.rmorphX /=. *)
  (*  have: ([seq qpolify phi_gt1 'X ^+ j | j <- iota 0 (\dim fullv)]`_i)%R =  *)
  (*        ([seq (fun j => qpolify phi_gt1 'X ^+ j) j | j <- iota 0 (\dim fullv)]`_i)%R. *)
  (*        qpolify phi_gt1 'X ^+ j *)
  (*  apply/etrans. *)
  (*  apply (nth_map 0%R). *)
  (*  exact nth_map. *)
  (*   exprnP. *)
  (*  rewrite  *)
  (*  rewrite /=. (nth_map 0%R). *)
  (*  set T := 0%R. *)
  (* apply/andP; split. *)
  (*  have<-: *)
  (*    (map (fun j => pi 'X ^+ j)%R (iota 0 m)) =  *)
  (*  (map_tuple [eta GRing.exp (pi 'X%R)] (iota_tuple (\dim (fullv : {vspace {qpoly phi}})) 0)). *)
  (*   rewrite dimvm. *)
  (*   rewrite //=. *)
  (*  rewrite /=. *)
  (*  set T := (map _ _). *)
  (*  rewrite -!GRing.rmorphX !GRing.exprZn piZ. *)
  (*  Check  *)
  (*  apply/val_inj. *)
  (*  rewrite GRing.val_ *)
  (*  rewrite /= -modp_scalel. *)
  (*  rewrite /qpolify /= /polyn.modphi_qpolyR /=. *)
  (*  rewrite  *)
  (*  rewrite /= (nth_map 0%R). *)
  (*  apply/eqP. *)
  (*  rewrite !eqE /=. *)
  (*  rewrite GRing.linearZ. *)
  (*  rewrite (nth_map 0%R); last by case: i => i H; rewrite size_tuple. *)
  (*  rewrite /H0 !GRing.Frobenius_autE. *)
  (*  case: (x i) => [][|[]//] j. *)
  (*  * have->: (Ordinal j = 0)%R by apply/val_inj. *)
  (*    by rewrite !GRing.scale0r GRing.expr0n. *)
  (*  * have->: (Ordinal j = 1)%R by apply/val_inj. *)
  (*    by rewrite !GRing.scale1r. *)
  
  (* rewrite /=. *)
(* Local Definition e1 := vbasis (fullv : {vspace {qpoly phi}}). *)
Local Definition e2 := map_tuple H e1.

Local Lemma kerHE x : (H x = 0 -> x = 0)%R.
  have H0: (0 = H 0)%R
   by rewrite GRing.rmorph0.
  rewrite [X in H x = X]H0.
  apply GRing.fmorph_inj.
Qed.

Lemma basis_e2 : basis_of fullv e2.
Proof.
  rewrite basisEfree size_tuple leqnn subvf !andbT.
  rewrite /e2 /e1 /=.
  apply/freeP => x.
   set T := (\sum_(_ < _) _)%R.
   have {T} ->: T = (\sum_(i < \dim fullv) H (x i *: e1`_i))%R.
    subst T.
    apply eq_big => //= i _.
    rewrite (nth_map 0%R); last by case: i => i H; rewrite size_tuple.
    rewrite /H0 !GRing.Frobenius_autE.
    case: (x i) => [][|[]//] j.
    * have->: (Ordinal j = 0)%R by apply/val_inj.
      by rewrite !GRing.scale0r GRing.expr0n.
    * have->: (Ordinal j = 1)%R by apply/val_inj.
      by rewrite !GRing.scale1r.
   set T := (\sum_(_ < _) _)%R.
   have {T} ->: T = H (\sum_(i < \dim fullv) (x i *: e1`_i))%R.
    subst T.
    apply/esym/(big_morph H).
    move=> y z.
    rewrite /H /H0 /= GRing.Frobenius_autD_comm //.
    by apply/eqP; rewrite eqE /= GRing.mulrC.
    by rewrite GRing.rmorph0.
   move/kerHE; apply/freeP.
   (* move: (vbasisP (fullv:{vspace {qpoly phi}})). *)
   move: basis_e1.
   rewrite basisEfree.
   by case/andP.
Qed.

Lemma freee2 : free e2.
Proof.
  move: basis_e2.
  rewrite basisEfree.
  by case/andP.
Qed.

(* Lemma e2E : *)
(*   e2 = map_tuple (fun j => pi 'X ^+ j.+1)%R *)
(*                  (iota_tuple (\dim (fullv:{vspace {qpoly phi}})) 0). *)
(* Proof. *)
(*   rewrite /e2. *)
(*   elim: (\dim fullv) => //. *)
(*   rewrite dimvm. *)

(* Local Definition canon_fun' f (v : qpoly_ringType_phi) : qpoly_ringType_phi := *)
(*   let m := \dim (fullv : {vspace {qpoly phi}}) in *)
(*   (\sum_(i < m) (@mulmx [finFieldType of 'F_2] m m 1 f (\col_(k < m) coord e2 k v)) *)
(*     i (@Ordinal 1 0 erefl) *: e2`_i)%R. *)

(* Local Definition canon_fun: 'M[{qpoly phi}]_m -> qpoly_ringType_phi -> qpoly_ringType_phi. *)
(* move: canon_fun'. *)
(* by have->: m = \dim (fullv : {vspace {qpoly phi}}) *)
(*  by rewrite /m dim_polyn. *)
(* Defined. *)

Local Definition canon_mat' f :=
  let m := \dim (fullv : {vspace {qpoly phi}}) in
  (\matrix_(i < m , j < m) coord e2 i (f e2`_j))%R.

Local Definition mat_inj : 'M['F_2]_(\dim (fullv : {vspace {qpoly phi}}))
                           -> 'M['F_2]_m.
move=> x.
apply (castmx (esym dimvm, esym dimvm) x).
Defined.

(* Definition iI := *)
(* (fun (i : 'I_m) =>  *)
(*        match dimvm in _ = x return 'I_x with *)
(*        | erefl => i *)
(*        end). *)
Definition canon_mat := mat_inj \o canon_mat'.

Lemma step y (x : ordinal y) : ordinal y.
  apply/(@Ordinal _ (x.+1 %% y)).
  case: x => x /= xy.
  case xy': (x.+1 == y).
   move/eqP: xy' => <-.
   by rewrite modnn.
  by rewrite modn_small ltn_neqAle xy' xy.
Defined.
Check (fun j => (canon_mat H *m delta_mx j (@Ordinal 1 0 erefl))
= (canon_mat H *m delta_mx (step j) (@Ordinal 1 0 erefl)))%R.

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
   castmx (esym dimvm, erefl) (\col_(i < \dim fullv) coord e2 i (M e2`_j)))%R.
Proof.
  apply/matrixP => k [][]//= i.
  rewrite /canon_mat /canon_mat' /mat_inj !castmxE !mxE /=.
  apply/etrans.
  apply eq_big => [//| s /= _].
  rewrite !castmxE !mxE andbT (nth_map 0%R).
  apply/erefl.
  rewrite /= size_tuple -dimvm.
  by case: s.
  rewrite /= (nth_map 0%R).
  by rewrite (sum_col_delta (fun j => coord e2 (cast_ord (esym (esym dimvm)) k) (M (H0 (e1`_j)%R))) j).
  rewrite /= size_tuple -dimvm.
  by case: s.
Qed.

Lemma stepK (i j : 'I_(\dim (fullv : {vspace {qpoly phi}}))) :
  coord e2 j (H (e2`_i))%R = coord e2 (step j) e2`_i.
Proof.
  case: i.
  elim.
   move=> ? /=.
   case e1e: [seq H0 i | i <- e1].
    move: (f_equal size e1e).
    rewrite size_map size_tuple /= => m0.
    suff: false by [].
    move: m0 dimvm (irreducible.m_is_prime pm) => /= ->.
    by rewrite /irreducible.m => ->.
   rewrite /e2 /e1.
   rewrite /=.
   rewrite /=.
   rewrite /=.
   rewrite dimvm.
   filter_map.
   rewrite /= !(nth_map 0%R).

Lemma mulHE j : 
  (canon_mat H *m delta_mx j (@Ordinal 1 0 erefl)
= delta_mx (step j) (@Ordinal 1 0 erefl))%R.
Proof.
  rewrite canon_matK.
  apply/matrixP => i [][]// ?.
  rewrite !castmxE !mxE andbT /= esymK (nth_map 0%R).
  move: (coord_free (cast_ord dimvm i) (step (cast_ord dimvm j)) freee2).
  have ->: (cast_ord dimvm i == step (cast_ord dimvm j)) = (i == step j).
   by rewrite !eqE /= -dimvm.
  move=> <-.
  rewrite /= (nth_map 0%R).
  coord e2 (cast_ord dimvm i) (H0 ([seq H0 i | i <- e1]`_j)%R) = (
  rewrite !castmxE.
  !mxE andbT (nth_map 0%R).
  

Lemma compE : canon_mat H = companionmx phi.
Proof.
  rewrite /canon_mat /canon_mat' /= /mat_inj /companionmx.
  apply/matrixP => i j.
  rewrite !castmxE /= !mxE.
  case: i j => [i Hi][j ?] /=.
  case: ifP.
   move=> /eqP He.
   rewrite /e2 /e1 (nth_map 0%R) /=.
   move: He Hi => -> Hi.
   rewrite /=.
  apply/val_inj.
   move=> H'.
   
   
   rewrite /coord /=.
   rewrite /=.
   move/eqP => ->.
  rewrite /=.
  rewrite /=.
  rewrite 
  apply/val_inj.
  Check fun_of_matrix.
  rewrite /=.
  Search (((\matrix_(_, _) _) _ _)%R).
  
  rewrite cast_ordK.
  rewrite /=.
  Check map_mx_companion.
  Check map_mx H.
  Check lin1_mx.
  
  apply/row_matrixP => j.
  rewrite /= /row /companionmx /=.
  apply/val_inj.
  rewrite /=.
  
  destruct eq_rect.
  rewrite /=.
  move=> x.
  rewrite /canon_fun /e /e0 /H GRing.Frobenius_autE /=.
Check Phi _ == pi 'X.
Check (H (pi 'X) != pi 'X) && (iter p H (pi 'X) == pi 'X).
End inverse_decimation_method.
Check (fun x => x ^ 2)%R.
   (@mulmx [finFieldType of 'F_2] p p 1 f
                     (\col_(k < p) coord e k v)) i (@Ordinal 1 0 erefl) *: e`_i.
Local Definition canon_mat f := \matrix_(i < p , j < p) coord e i (f e`_j).

Local Definition canon_fun f v :=
  rVnpoly (@mulmx [finFieldType of 'F_2] m m 1 f (npoly_rV v)^T)^T.
Local Definition canon_mat f := \matrix_(i < p , j < p) coord e i (f e`_j).
  rewrite /e /e0.
  rewrite nth_map.
  cbn.
   /=.
  
  Check 3`_0.
  rewrite /=.
  nth_map.
   freeE.
  apply/forallP => [][] x.
  elim: x => //=.
  rewrite /= /e0.
  case: m => //= m _.
  rewrite /=.
  rewrite iota.
  
  rewrite /=.
  rewrite /free.
  move=> x.
  move=> x.
Admitted.

Local Lemma pos_prednK : (size phi).-1 = (size phi).-2.+1.
 by rewrite prednK // -subn1 ltn_subRL addn0.
Defined.

Check {qpoly phi}.

Local Definition comp_phi : matrix_ringType [finFieldType of 'F_2] m.-1.
move: (companionmx phi).
rewrite /m pos_prednK.
apply.
Defined.
Lemma irreducible_cyclic x :
    @mulmx _ _ m.-1.+1 1 (comp_phi ^+ m)%R x == x.
  rewrite /comp_phi /= eqE /=.
  rewrite /mx_val /=.
  
Check (comp_phi ^+ m)%R.
Check @mulmx _ _ m.-1.+1 1 (comp_phi ^+ m)%R.
    

Check matrix_ringType _ _.
Check ((companionmx phi : matrix_ringType _ _) ^+ m)%R.
Check iter m (mulmx (companionmx phi)) .
Check diag_mx.
Check (mulmx (iter m (mulmx (companionmx phi))) 1%:M).
   (mulmx (iter m (mulmx (companionmx phi))) 1%:M) *m x == x.
    mulmx (companionmx phi ^+ m)%VS x == x.
End irreducible_cyclic.

Section phi.
Variables w n m r : nat.
Variable a : w.-tuple [finFieldType of 'F_2].

Local Open Scope ring_scope.
Definition phi' :=
  ('X ^+ n + 'X ^+ m) ^+ (w - r) * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ r
  + \sum_(i < r.-1) a`_i *: ('X ^+ n + 'X ^+ m) ^+ (w - r)
                     * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ (r.-1 - i)
  + \sum_(i < w - r.-1)
     a`_(r.-1 + i) *: ('X ^+ n + 'X ^+ m) ^+ (w - r - i).
End phi.

Lemma a32 : size ([:: 1; 0; 0; 1; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 1; 0; 1;
                     1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 1]: seq 'F_2)%R == 32.
Proof. by []. Qed.
Definition phi := phi' 624 397 31 (Tuple a32).
Local Definition f := companionmx phi.

Lemma compute_irred :
('X ^ 2 %% phi != 'X %% phi)%R
   && ('X ^ (2 ^ (size phi).-1)%N %% phi == 'X %% phi)%R.
Proof. 
  apply/andP; split.
  rewrite /phi /phi'.
  native_compute.


Check random_state.
Check next_random_state (initialize_random_state 3).
Check f.

Require Extraction.
Require Import ExtrOcamlNatInt.
Extraction "test.ml" compute_irred.


Check generate_state_vector.
  (seed : N) : random_state :=
  (rest : nat) (acc : seq N) : seq N :=
(*
Section inverse_decimation_method.
Variables w n m r : nat.
(* Local Definition w := 32. *)
(* Local Definition n := 624. *)
(* Local Definition m := 397. *)
(* Local Definition r := 31. *)
Hypothesis mn : m < n.
Hypothesis r1 : 1 < r.
Hypothesis wr0 : 0 < w - r.
Hypothesis m0 : 0 < m.
Lemma pred_mN : m.-1 < n.-1.
Proof. by case: m n m0 mn => // ? []. Qed.
Lemma r0 : 0 < r.
Proof. by case: r r1. Qed.
Hint Resolve pred_mN r0 : core.
Variable a : w.-tuple [finFieldType of 'F_2].

Local Open Scope ring_scope.
Definition phi :=
  ('X ^+ n + 'X ^+ m) ^+ (w - r) * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ r
  + \sum_(i < r.-1) a`_i *: ('X ^+ n + 'X ^+ m) ^+ (w - r)
                     * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ (r.-1 - i)
  + \sum_(i < w - r.-1)
     a`_(r.-1 + i) *: ('X ^+ n + 'X ^+ m) ^+ (w - r - i).
Definition V := {qpoly phi}.
Definition f := companionmx phi.
Variable b : {linear V -> regular_vectType [finFieldType of 'F_2]}%R.
Local Definition p := (size phi).-1.

Lemma XnXmr_neq0 n' m' r' :
  (m' < n')%N -> (r' > 0)%N -> ('X^n' + 'X^m' : {poly 'F_2}) ^+ r' != 0.
Proof.
  elim: r' => // r' IHr nm _.
  rewrite GRing.exprS -size_poly_eq0.
  have nm0: size ('X^n' + 'X^m' : {poly 'F_2}) != 0%N.
   by rewrite size_addl ?size_polyXn.
  case r0': (r' == 0)%N.
   move/eqP: r0' => ->.
   by rewrite GRing.expr0 GRing.mulr1.
  rewrite size_mul ?IHr // ?lt0n ?r0' //; last by rewrite -size_poly_eq0.
  case: (size ('X^n' + 'X^m')) nm0 => // ? ?.
  by rewrite addSn addn_eq0 negb_and size_poly_eq0 orbC IHr // lt0n r0'.
Qed.
  
Lemma phi_gt1 : (1 < size phi)%N.
Proof.
  rewrite /phi !size_addl size_mul ?XnXmr_neq0 //.
  * rewrite -subn1 ltn_subRL ltn_addl // -ltn_subRL subn1
            size_exp size_addl ?size_polyXn //.
    case: n mn m0 => []//[|/= p _ _]; first by case: m.
    elim: p => [|??]; first by rewrite mul1n.
    by rewrite mulSn ltn_addl.
  * apply: (leq_ltn_trans (size_sum _ _ _)).
    Admitted.
(* Qed. *)

Local Canonical qpoly_ringType_phi :=
  Eval hnf in qpoly_ringType phi_gt1.
Local Canonical qpoly_comRingType_phi :=
  Eval hnf in qpoly_comRingType phi_gt1.
Local Definition pi := canon_surj phi_gt1.
Local Definition e0 := map (fun (x : nat) => pi ('X ^ x)) (iota 0 p).
Local Lemma size_e0_eqp : size e0 == p.
Proof. by rewrite /e0 size_map size_iota. Qed.
Local Definition e := Tuple size_e0_eqp.
Lemma basis_e : basis_of fullv e.
Admitted.

Local Definition canon_fun f v :=
  rVnpoly (@mulmx [finFieldType of 'F_2] p p 1 f (npoly_rV v)^T)^T.
Local Definition canon_mat f := \matrix_(i < p , j < p) coord e i (f e`_j).

Local Definition Phi S := \sum_(i < p) (b \o iter i (canon_fun f)) S *: e`_i.
Hypothesis bij: bijective Phi.

Local Lemma char2_V : 2 \in [char V].
Proof.
by apply/(GRing.rmorph_char pi)/(GRing.rmorph_char (polyC_rmorphism _)).
Qed.

Local Definition H : V -> V := Frobenius_aut char2_V.

Lemma expHpE : iter p H (pi 'X) = pi ('X ^ (2 ^ p)%N).
Proof.
  elim: p => // p' IHp.
  by rewrite -[X in (2 ^ X)%N]addn1 iterS IHp /H
             GRing.Frobenius_autE -GRing.rmorphX
             expnD expn1 muln2 -addnn exprzD_nat GRing.expr2.
Qed.
Lemma H1E : H (pi 'X) = pi ('X ^ 2).
Proof.
  by rewrite /H GRing.Frobenius_autE -GRing.rmorphX.
Qed.
Check Phi _ == pi 'X.
Check (H (pi 'X) != pi 'X) && (iter p H (pi 'X) == pi 'X).
End inverse_decimation_method.
*)
(* can not compute *)
(*
Compute ((('X ^ 2 %% p)%R != ('X %% p)%R)
   && (('X ^ (2 ^ (size p).-1)%N %% p)%R == ('X %% p)%R)).
*)

From infotheo Require Import f2 ssralg_ext.
Require Import BinNat.


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

Lemma a32 : size ([:: 1; 0; 0; 1; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 1; 0; 1;
                     1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 1]: seq 'F_2)%R == 32.
Proof. by []. Qed.
Definition phi := phi' (Tuple a32).
Definition compute_irred :=
('X ^ 2 %% phi != 'X %% phi)%R
   && ('X ^ (2 ^ (size phi).-1)%N %% phi == 'X %% phi)%R.

Require Extraction.
Require Import ExtrOcamlNatInt.
Extraction "test.ml" compute_irred.
