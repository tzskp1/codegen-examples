From mathcomp
Require Import all_ssreflect all_algebra all_field all_fingroup.
Require Import mt nat_word.
Require irreducible.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section mulBE.
Local Open Scope ring_scope.
Variable w r : nat.
Variable R : ringType.
Variable ul : 'M[R]_(r, w).
Variable dl : 'M[R]_(w, w).
Local Notation B := (castmx (erefl, addnC _ _) (block_mx ul 1%:M dl 0)).
Lemma mulBE_hidden (x : 'rV[R]_(r + w)) :
  x *m B = castmx (erefl, addnC _ _)
                  (row_mx (lsubmx x *m ul + rsubmx x *m dl) (lsubmx x)).
Proof.
apply/rowP => i; rewrite ?(castmxE, mxE).
apply/etrans; first by apply/eq_bigr => j _; rewrite castmxE block_mxEh mxE.
set T := cast_ord _ i; case: (splitP T) => j Tj.
+ rewrite ?(castmxE, mxE) big_split_ord /=.
  congr (_ + _); apply/eq_bigr => k _;
  rewrite ?(castmxE, mxE) !cast_ord_id.
  - case: (splitP (lshift w k)) => j0 wkj0.
    * congr (_ * ul _ _).
      apply/ord_inj.
      by rewrite -wkj0.
    * case: k wkj0 => k /= i0 krj0.
      suff: false by []; move: i0.
      by rewrite krj0 ltnNge leq_addr.
  - case: (splitP (rshift r k)) => j0 wkj0.
    * case: j0 wkj0 => j0 /= i0 rkj0.
      suff: false by []; move: i0.
      by rewrite -rkj0 ltnNge leq_addr.
    * congr (_ * dl _ _).
      apply/ord_inj; move/eqP: wkj0.
      by rewrite /= eqn_add2l eq_sym => /eqP.
+ rewrite ?(castmxE, mxE) [in RHS](matrix_sum_delta x) summxE big_ord1
          summxE !big_split_ord /= !cast_ord_id.
  congr (_ + _); apply/eq_bigr => k _.
  * by rewrite cast_ord_id col_mxEu !mxE !eqE /= eq_sym.
  * rewrite cast_ord_id col_mxEd !mxE !eqE /=.
    case jrk: (val j == r + k)%nat => //.
    case: j jrk {Tj} => j + /= /eqP jrk.
    by rewrite jrk ltnNge leq_addr.
Qed.
End mulBE.
Section mulAE.
Local Open Scope ring_scope.
Variable w r : nat.
Variable dl : 'F_2.
Variable dr : 'rV['F_2]_r.
Local Notation A :=
  (castmx (addn1 _, etrans (addnC _ _) (addn1 _)) (block_mx 0 1%:M dl%:M dr)).

Lemma Aul (i1 : 'I_r) : A (widen_ord (leqnSn r) i1) ord0 = 0.
Proof.
  rewrite ?(castmxE, mxE).
  set T := cast_ord _ _.
  case: (splitP T) => k Tk.
  + set S := cast_ord _ _.
    by rewrite mxE; case: (splitP S) => l Sl; rewrite mxE.
  + case: k Tk => [][]//= ?.
    rewrite addn0 => i1r.
    suff: (r < r)%nat by rewrite ltnn.
    by rewrite -[X in (X < _)%nat]i1r.
Qed.

Lemma Adr (j : 'I_r) : A ord_max (lift ord0 j) = dr ord0 j.
Proof.
  rewrite ?(castmxE, mxE).
  set T := cast_ord _ _.
  case: (splitP T) => k /= Tk.
  + suff: (r < r)%nat by rewrite ltnn.
    by rewrite [X in (X < _)%nat]Tk.
  + rewrite mxE.
    set S := cast_ord _ _.
    case: (splitP S) => l /= Sl.
     by case: l Sl => [][].
    congr (dr _ _); apply/ord_inj; first by case: k Tk => [][].
    by move: Sl; rewrite /bump /= !add1n; case.
Qed.

Lemma Aur i0 j :
  A (widen_ord (leqnSn r) i0) (lift ord0 j) = if i0 == j then 1 else 0.
Proof.
  rewrite castmxE mxE.
  set T := cast_ord _ _.
  case: (splitP T) => k /= Tk; last first.
   case: k Tk => [][]//= ?; rewrite addn0 => Tk.
   suff: (r < r)%nat by rewrite ltnn.
   by rewrite -[X in (X < _)%nat]Tk.
  rewrite mxE.
  set S := cast_ord _ _.
  case: (splitP S) => l /= Sl.
   by case: l Sl => [][].
  rewrite /bump /= !add1n in Sl.
  rewrite mxE !eqE /= -Tk; case: Sl => ->.
  by case: ifP.
Qed.

Lemma mulAE_hidden (x : 'rV['F_2]_(r.+1)) :
  x *m A =
  row_mx 0 (\row_i x ord0 (widen_ord (leqnSn r) i)) + (row_mx dl%:M dr) *+ (x ord0 ord_max == 1%R).
Proof.
apply/rowP => i; rewrite ?(castmxE, mxE).
case x00: (x ord0 ord_max == 1); rewrite !mxE.
- case: (@splitP 1 r i) => j /= ij.
  * case: j ij => [][]//= ? i0.
    rewrite !mxE GRing.add0r eqE /= -GRing.mulr_natr GRing.mulr1.
    have->: i = ord0 by apply/ord_inj.
    rewrite big_ord_recr /= (eqP x00) GRing.mul1r castmxE mxE.
    set T := cast_ord _ _.
    case: (splitP T) => k Tk.
     suff: (r < r)%nat by rewrite ltnn.
     by move: Tk => /= Tk; rewrite [X in (X < _)%nat]Tk.
    set S := cast_ord _ _.
    rewrite !mxE; case: (splitP S) => l Sl; last by rewrite /= add1n in Sl.
    case: k l {Tk Sl} => [][]//?[][]//? /=.
    rewrite mxE eqE /= -GRing.mulr_natr GRing.mulr1 -[RHS]GRing.add0r.
    congr (_ + _).
    apply/etrans; first by apply/eq_bigr => k _; rewrite Aul GRing.mulr0.
    rewrite /= big_const_ord.
    by elim: r => // r' IHr; rewrite iterS IHr GRing.addr0.
  * rewrite mxE big_ord_recr /=.
    have->: i = lift ord0 j by apply/ord_inj; rewrite ij.
    rewrite Adr (eqP x00) GRing.mul1r; congr (_ + _).
    apply/etrans; first by apply/eq_bigr => k _; rewrite Aur.
    rewrite [in RHS](matrix_sum_delta x) summxE big_ord1 summxE
            /= [in RHS]big_ord_recr /= !mxE -[LHS]GRing.addr0.
    congr (_ + _).
    apply eq_bigr => i0 _;
     first by rewrite !mxE eqxx /= !eqE /= eq_sym; case: ifP.
    rewrite !eqE /=; case jr: (j == r :> nat)%nat; last by rewrite GRing.mulr0.
    move/eqP: jr => jr; suff: (r < r)%nat by rewrite ltnn.
    by rewrite -[X in (X < _)%nat]jr.
- have x00': (x ord0 ord_max == 0) by case: (x ord0 ord_max) x00 => [][|[]//].
  case: (@splitP 1 r i) => j /= ij.
  * case: j ij => [][]//= ? i0.
    have->: i = ord0 by apply/ord_inj.
    rewrite big_ord_recr /= (eqP x00') GRing.mul0r GRing.addr0.
    apply/etrans; first by apply/eq_bigr => k _; rewrite Aul GRing.mulr0.
    rewrite /= mxE big_const_ord GRing.addr0.
    by elim: r => // r' IHr; rewrite iterS IHr GRing.addr0.
  * rewrite mxE big_ord_recr /=.
    have->: i = lift ord0 j by apply/ord_inj; rewrite ij.
    rewrite Adr (eqP x00') GRing.mul0r GRing.addr0.
    apply/etrans; first by apply/eq_bigr => k _; rewrite Aur.
    rewrite [in RHS](matrix_sum_delta x) summxE big_ord1 summxE
            /= [in RHS]big_ord_recr /= !mxE GRing.addr0 -[LHS]GRing.addr0.
    congr (_ + _).
    apply eq_bigr => i0 _;
     first by rewrite !mxE eqxx /= !eqE /= eq_sym; case: ifP.
    rewrite !eqE /=; case jr: (j == r :> nat)%nat; last by rewrite GRing.mulr0.
    move/eqP: jr => jr; suff: (r < r)%nat by rewrite ltnn.
    by rewrite -[X in (X < _)%nat]jr.
Qed.
End mulAE.

Section Main.
Variables w n m r : nat.
Variable a : w.-tuple [fieldType of 'F_2].
Notation p := (n * w - r).
Hypothesis pm : prime (2 ^ p - 1).
Hypothesis mn : m.+1 < n.-2.
Hypothesis m0 : 0 < m.
Hypothesis r0 : 0 < r.
Hypothesis rw : r < w.
Hypothesis p3 : 3 <= p.

Lemma n2 : 2 < n.
Proof. by case: n mn m0 => []//[]//[]//. Qed.

Lemma n2' : 2 <= n.
Proof. by apply: ltnW n2. Qed.

Lemma mn' : m < n.
Proof.
  case: n mn => []//[]//[]// n'.
  rewrite /= ltnS => H.
  apply/(leq_trans H).
  by rewrite leqW // leqW //.
Qed.

Lemma n0 : 0 < n.
Proof. by case: n n2. Qed.

Lemma npn : n.-1 < n.
Proof. by case: n n0. Qed.
  
Lemma p0 : 0 < p.
Proof. by case: p p3. Qed.

Lemma w0 : 0 < w.
Proof. by case: w rw r0 => //; rewrite leqn0 => /eqP ->. Qed.

Lemma rw' : r <= w.
by apply/ltnW.
Qed.

Lemma rnpw : r <= n.-1 * w.
Proof.
  case: n mn' m0 => []//=[|*]; first by case m.
  rewrite mulSn.
  by apply/leq_trans/leq_addr/rw'.
Qed.

Lemma rnmw : r <= (n - m) * w.
Proof.
case: n mn' => // n' ?.
by rewrite subSn // mulSn; apply/leq_trans/leq_addr/ltnW.
Qed.

Lemma rnppw : r <= n.-2 * w.
Proof.
  case: n n2 => []//[]//[]// n0 _.
  rewrite mulSn.
  by apply/leq_trans/leq_addr/rw'.
Qed.

Lemma wnpwr : w <= n.-1 * w - r.
Proof.
  case: n n2 rnppw => []//[]//[]// n0 _ ?.
  by rewrite mulSn -addnBA // leq_addr.
Qed.

Lemma tecr : r = r.-1.+1.
Proof. by case: r r0. Qed.

Lemma tecwr : w - r = (w - r).-1.+1.
Proof. by rewrite prednK // /leq subnBA ?rw' // add1n subn_eq0 rw. Qed.

Lemma tecw : (w - r).-1.+1 + r.-1.+1 = w.
Proof.
by rewrite !prednK // ?subnK ?rw' // /leq subnBA ?rw' // add1n subn_eq0 rw.
Qed.

Lemma twist : r + (w - r) = w.
Proof. by rewrite subnKC // ltnW. Qed.

Lemma tecw' : w.-1.+1 = w.
Proof. by case: w w0. Qed.

Lemma tecw'' : 1 + w.-1 = w.
Proof. by case: w w0. Qed.

Lemma rnwp : r <= n * w.-1.
Proof.
  case: n mn' m0 => []//=[|*]; first by case m.
  move: rw => rw''.
  rewrite -tecw' ltnS in rw''.
  rewrite mulSn.
  by apply/leq_trans/leq_addr/rw''.
Qed.

Lemma tecnw : w + (n.-1 * w - r) = p.
Proof. by rewrite addnBA ?rnpw // -mulSn prednK ?n0. Qed.

Lemma choose_m : m.-1 * w + w + ((n - m) * w - r) = p.
Proof.
by rewrite addnC addnA addnC addnCA -mulSn addnC addnBA
           ?rnmw // -mulnDl prednK // addnC subnK // ltnW ?mn'.
Qed.

Lemma choose_last : (n.-1 * w - r) + w = p.
Proof. by rewrite addnC tecnw. Qed.

Lemma tecpr : p + r = n * w.
Proof.
  rewrite subnK //.
  case: n mn' => // ??.
  rewrite mulSn.
  by apply/leq_trans/leq_addr/ltnW.
Qed.

Lemma tecp : p = p.-1.+1.
Proof. by case: p p3. Qed.

Lemma tecn : n = n.-2.+2.
Proof. by case: n n2' => []//[]. Qed.

Lemma wrpwr : (w - r).-1 < w - r.
Proof.
  by rewrite /leq prednK ?subnn // ltnNge /leq subn0 subn_eq0 -ltnNge.
Qed.

Lemma wrw : (w - r) < w.
Proof.
  rewrite /leq -subSn; last by apply/ltnW.
  by rewrite subnAC subSn // subnn subn_eq0.
Qed.

Lemma wrp : (w - r) < p.
Proof.
  apply/(leq_trans wrw).
  by rewrite -choose_last leq_addl.
Qed.

Lemma wr0 : 0 < w - r.
Proof. by case: (w - r) wrpwr. Qed.

Lemma pwn : p %/ w < n.
Proof.
  rewrite divnMBl ?w0 //.
  case wr: (w %| r).
   case/dvdnP: wr => [][|p rpw].
    rewrite mul0n => rn0.
    by move: rn0 r0 => ->.
   move: rpw rw => ->.
   rewrite mulSn => /(leq_ltn_trans (leq_addr _ _)).
   by rewrite ltnn.
  rewrite subn1 divn_small // subn0.
  by case: n n0.
Qed.

Hint Resolve p0 n2' n0 w0 rw' rnwp rnpw rnmw wnpwr mn' wr0 : core.
Local Open Scope ring_scope.

Definition A :=
  castmx (tecw', tecw')
  (castmx (addn1 _, etrans (addnC _ w.-1) (addn1 _))
  (block_mx 0 1%:M (nth 0 a 0)%:M (\row_i nth 0 a i.+1))).

Definition S :=
  castmx (etrans (addnC _ _) tecw, tecw)
  (block_mx 0                             (castmx (tecr, tecr) 1%:M)
            (castmx (tecwr, tecwr) 1%:M)                          0) *m A.

Definition UL : 'M['F_2]_(n.-1 * w - r, w) :=
\matrix_(i, j) (1 *+ ((j == i - (m.-1 * w) :> nat) && (i >= (m.-1 * w)))%nat).

Definition B :=
  castmx (etrans (addnC _ _) tecnw, tecnw)
 (block_mx  UL 1%:M
            S  0).

Definition phi := char_poly (castmx (tecp, tecp) B).
Lemma size_phi : (size phi).-1 = p.
Proof. by rewrite size_char_poly prednK. Qed.

Lemma X2X : 'X ^ 2 %% phi != 'X %% phi.
Proof.
  rewrite -GRing.subr_eq0 -modp_opp -modp_add.
  apply/negP => /dvdp_leq H.
  have/H: 'X ^ 2 - 'X != 0 :> {poly 'F_2}.
   rewrite GRing.subr_eq0.
   apply/negP => /eqP/(f_equal (size : {poly 'F_2} -> nat)).
   by rewrite size_polyXn size_polyX.
  case: (size phi) size_phi => //= p0' => [|->].
   by move: p0' pm => <-; rewrite expn0 subn1.
  rewrite size_addl ?size_polyXn ?size_opp ?size_polyX //.
  by apply/negP; rewrite -leqNgt.
Qed.

Lemma pm' : prime (2 ^ (size phi).-1 - 1).
Proof. by rewrite size_phi. Qed.

Hint Resolve pm' : core.

Lemma irreducibleP : reflect (irreducible_poly phi)
                             ('X ^ (2 ^ (size phi).-1)%N %% phi == 'X %% phi).
Proof.
apply/(iffP idP).
* move=> H1; apply/irreducible.irreducibleP => //.
  by rewrite X2X /=.
* by case/irreducible.irreducibleP/andP.
Qed.

Lemma phi_mxminpoly :
  irreducible_poly phi ->
  phi = mxminpoly (castmx (tecp, tecp) B).
Proof.
 case => ? H0.
 move/H0: (mxminpoly_dvd_char (castmx (tecp, tecp) B)).
 rewrite size_mxminpoly eqSS -lt0n mxminpoly_nonconstant => /implyP /= ?.
 apply/esym/eqP.
 by rewrite -eqp_monic ?char_poly_monic ?mxminpoly_monic.
Qed.

Local Open Scope quotient_scope.

Lemma cycleB_dvdP :
  irreducible_poly phi ->
  forall q, (q > 0)%nat ->
    (castmx (tecp, tecp) B ^+ q == castmx (tecp, tecp) B)
        = (2 ^ (size phi).-1 - 1 %| q - 1)%nat.
Proof.
  move=> H q q0.
  apply/eqP; case: ifP => H0; last first.
  * apply/eqP; move/negbT: H0; apply contra.
    rewrite -(horner_mx_X (castmx _ _)) -GRing.rmorphX /=.
    move/eqP/(f_equal (mx_inv_horner (castmx (tecp, tecp) B))).
    rewrite !horner_mxK -!phi_mxminpoly // => H1.
    apply/(irreducible.cycleF_dvdP' pm' H q0)/eqP.
    by rewrite -GRing.rmorphX /= exprnP -irreducible.XnE -H1.
  * rewrite -(horner_mx_X (castmx _ _)) -GRing.rmorphX
            (divp_eq 'X^q phi) GRing.rmorphD
            GRing.rmorphM /= Cayley_Hamilton GRing.mulr0 GRing.add0r.
    move/(irreducible.cycleF_dvdP' pm' H q0)/eqP : H0.
    rewrite -GRing.rmorphX /= exprnP -irreducible.XnE => /eqP ->.
    by rewrite modp_small // size_polyX size_char_poly prednK ltnW // ltnW.
Qed.

Lemma size_ord_enum q : size (ord_enum q) = q.
Proof. by rewrite -(size_map val) val_ord_enum size_iota. Qed.

Lemma nth_ord_enum i (q : nat) k : (i < q)%nat -> val (nth k (ord_enum q) i) = i.
Proof.
move=> iq.
by rewrite -(nth_map k (val k) val) ?val_ord_enum ?nth_iota // size_ord_enum.
Qed.

Lemma eq_big_cond (T : ringType) p q (pq : p = q) (F1 : 'I_p -> T)
  (F2 : 'I_q -> T) (F12 : forall i, F1 (cast_ord (esym pq) i) = F2 i) :
  \sum_(j < p) F1 j = \sum_(i < q) F2 i.
Proof.
case p0: (p > 0)%nat; last first.
 case: p p0 pq F1 F2 F12 => //= _.
 case: q => // *.
 by rewrite !big_ord0.
have dq: 'I_q.
 rewrite -pq.
 case: p p0 {F1 F12 pq} => // *.
 by apply ord0.
apply/etrans; last first.
 apply congr_big => [|//|i _]; last by rewrite -F12.
 apply: (_ : map (cast_ord pq) (index_enum (ordinal_finType p)) = _).
  apply/eq_from_nth.
  by rewrite size_map /index_enum !unlock /= -!(size_map val) !val_ord_enum !size_iota.
 rewrite size_map /index_enum !unlock /= size_ord_enum => i Hi.
 apply: (_ : nth dq [seq cast_ord pq i | i <- ord_enum p] i = nth dq (ord_enum q) i).
 apply/val_inj.
 rewrite (nth_map (cast_ord (esym pq) dq)); last by rewrite size_ord_enum.
 rewrite /= !nth_ord_enum //; last by rewrite -pq.
rewrite big_map; apply eq_bigr => i _.
by rewrite -F12; congr (F1 _); apply/val_inj.
Qed.

Lemma mulBE_hidden' (x : 'rV['F_2]_p) :
let x' := castmx (erefl, etrans (esym tecnw) (addnC _ _)) x in
x *m B = castmx (erefl, tecnw)
        (row_mx (lsubmx x' *m UL + rsubmx x' *m S) (lsubmx x')).
Proof.
move=> x'.
apply: (can_inj (castmxK (esym erefl) (esym tecnw))).
apply: (can_inj (castmxK erefl (addnC w (n.-1 * w - r)%N))).
rewrite !castmxK -mulBE_hidden castmx_comp /=; subst x'.
apply: (can_inj (castmxK (esym erefl) (esym (etrans (esym tecnw) (addnC w _))))).
rewrite castmxK; apply/rowP => k.
rewrite ?(mxE, castmxE).
apply/etrans; last first.
 apply eq_bigr => j _.
 by rewrite !castmxE !cast_ord_id !esymK.
apply: eq_big_cond => [|? i].
 by rewrite addnC tecnw.
congr (_ * _); first by congr (x 0 _); apply/val_inj.
rewrite castmxE //=.
by congr (block_mx _ _ _ _ _ _); apply/val_inj.
Qed.

Lemma mulSE (x : 'rV['F_2]_(n.-1 * w - r + w)) :
  let x' := castmx (erefl, esym tecw')
            (rsubmx x *m castmx (etrans (addnC _ _) tecw, tecw)
                         (block_mx 0 (castmx (tecr, tecr) 1%:M)
                                   (castmx (tecwr, tecwr) 1%:M) 0)) in
  rsubmx x *m S = castmx (erefl, tecw')
  (row_mx 0 (\row_i x' ord0 (widen_ord (leqnSn w.-1) i))
             + row_mx a`_0%:M (\row_i a`_i.+1) *+ (x' ord0 ord_max == 1)).
Proof.
  move=> x'; rewrite mulmxA -mulAE_hidden.
  apply/rowP => k; rewrite ?(mxE, castmxE).
  apply: eq_big_cond => [|? i]; first by rewrite prednK.
  rewrite ?(mxE, castmxE).
  congr (_ * _).
  apply/eq_bigr => j _.
  congr (rsubmx x _ _ * _); first by apply/val_inj.
  by rewrite !castmxE; congr (block_mx _ _ _ _ _ _); apply/val_inj.
  set I := cast_ord _ _; set I' := cast_ord (esym _) i.
  by have->: I = I' by apply/val_inj.
Qed.

Definition z (x : 'rV['F_2]_p) :=
  rsubmx (castmx (erefl _, etrans (esym tecnw) (addnC _ _)) x) *m
  castmx (etrans (addnC _ _) tecw, tecw)
 (block_mx 0 (castmx (tecr, tecr) 1%:M) (castmx (tecwr, tecwr) 1%:M) 0).

Definition y (x : 'rV['F_2]_p) :=
lsubmx (castmx (erefl _, etrans (esym tecnw) (addnC _ _)) x).

Lemma sum_f2_eq0 q (P : pred 'I_q) :
\big[GRing.add_comoid [ringType of 'F_2]/0]_(i0 | P i0) 0 = 0.
Proof.
rewrite big_const; set T := #|_|.
elim: T => // t IHt.
by rewrite iterS IHt /= GRing.addr0.
Qed.

Lemma ULE (x : 'rV['F_2]_p) :
  y x *m UL = rsubmx (lsubmx (castmx (erefl, esym choose_m) x)).
Proof.
apply/rowP => i.
rewrite ?(mxE, castmxE).
apply/etrans; first by apply/eq_bigr => j _; rewrite ?(mxE, castmxE).
have inwr: (i + m.-1 * w < n.-1 * w - r)%nat.
 apply: leq_trans.
  apply: (_ : (_ < w + m.-1 * w)%nat); first by rewrite ltn_add2r.
 have->: n.-1 = n.-2.+1 by case: n n2 => []//[].
 rewrite -mulSn [X in (_ <= X - _)%nat]mulSn addnC
         -[X in (X <= _)%nat]addn0 -addnBA //.
 apply leq_add.
  rewrite leq_mul2r; apply/orP; right; apply: (leq_trans _ mn).
  by case: m => []//= ?; apply ltnW.
 by rewrite /leq sub0n.
rewrite (bigD1 (Ordinal inwr)) // -[RHS]GRing.addr0.
congr (_ + _).
 rewrite /= addnK leq_addl !eqxx GRing.mulr1; congr (x _ _).
 by apply/ord_inj; rewrite /= addnC.
apply/etrans; first apply/eq_bigr => j /= P.
case mpwj : (m.-1 * w <= j)%nat.
 have->: (i == (j - m.-1 * w)%N :> nat) = false.
  apply/negP/negP; move: P; apply contra.
  rewrite !eqE /= => /eqP ->.
  by rewrite subnK //.
 by rewrite GRing.mulr0.
 by rewrite andbF GRing.mulr0.
by apply sum_f2_eq0.
Qed.

Definition twist_word (x y : 'rV['F_2]_w) :=
  castmx (erefl, etrans (addnC _ _) twist)
 (row_mx (rsubmx (castmx (erefl, esym twist) x))
         (lsubmx (castmx (erefl, esym twist) y))).

Definition z' (x : 'rV['F_2]_p) :=
  let l := rsubmx (castmx (erefl, esym choose_last) x) in
  twist_word l l.

Lemma zE (x : 'rV['F_2]_p) : z x = z' x.
Proof.
  rewrite /z'.
  set l := rsubmx (castmx (erefl, esym choose_last) x).
  apply/rowP => j.
  rewrite !(mxE, castmxE).
  apply/etrans; first by apply/eq_bigr => k _; rewrite !castmxE block_mxEh !mxE.
  set T := cast_ord _ _; set S := cast_ord _ _.
  case: (splitP T) => i Ti.
  - case: (splitP S) => k Sk; last first.
     suff: (w - r < w - r)%nat by rewrite ltnn.
     suff: (w - r + k < w - r)%nat; apply/leq_trans.
     + by rewrite ltnS leq_addr.
       rewrite /= in Ti, Sk; rewrite -Sk Ti.
     + case: i {Ti} => i /=; apply.
     + apply: wrpwr.
    apply/etrans; first by apply/eq_bigr => t _; rewrite !(castmxE, mxE).
    rewrite !(mxE, castmxE) !cast_ord_id !esymK.
    have rkw: (r + k < w)%nat.
     case: k {Sk} => k /= H.
     apply/leq_trans.
      apply: (_ : _  <  r + (w - r))%nat; by rewrite ltn_add2l.
     by rewrite addnBA // addnC addnK.
    rewrite (bigD1 (Ordinal rkw)) // -[RHS]GRing.addr0; congr (_ + _).
     set Q' := cast_ord (esym (etrans _ _)) _; set Q := cast_ord (esym (etrans _ _)) _.
     case: (splitP Q) => t Qt.
      suff: (r < r)%nat by rewrite ltnn.
      suff: (r + k < r)%nat by apply/leq_trans; rewrite ltnS leq_addr.
      rewrite /= in Qt; rewrite Qt.
      case: t {Qt} => t /=.
      by rewrite prednK //.
     rewrite castmxE mxE eqE /=.
     move/eqP: Qt; rewrite /= prednK // eqn_add2l => /eqP <-.
     rewrite -Sk -Ti eqxx GRing.mulr1.
     by congr (x _ _); apply/val_inj.
    apply/etrans; first apply/eq_bigr => q /= P.
     set Q' := cast_ord (esym (etrans _ _)) _; set Q := cast_ord (esym (etrans _ _)) _.
     case: (splitP Q) => t Qt.
      by rewrite mxE GRing.mulr0.
     rewrite /= in Qt, Sk.
     rewrite castmxE mxE eqE /= -Ti /= Sk.
     case tk: (t == k :> nat)%nat.
      case: q P Q' {Q} Qt => /= q qw.
      rewrite eqE /= (eqP tk) prednK // => qrk ? /eqP.
      by rewrite (negPf qrk).
     by rewrite GRing.mulr0.
    by apply sum_f2_eq0.
  - case: (splitP S) => k Sk.
     suff: (w - r < w - r)%nat by rewrite ltnn.
     suff: (w - r + i < w - r)%nat; apply/leq_trans.
     + by rewrite ltnS leq_addr.
     + rewrite /= prednK // in Ti; rewrite /= in Sk.
       rewrite -Ti Sk; case: k {Sk} => k; apply.
     + by rewrite leqnn.
    apply/etrans; first by apply/eq_bigr => t _; rewrite !(castmxE, mxE).
    rewrite !(mxE, castmxE) !cast_ord_id !esymK.
    have kw: (k < w)%nat.
     case: k {Sk} => k /= H; by apply/(leq_trans H).
    rewrite (bigD1 (Ordinal kw)) // -[RHS]GRing.addr0; congr (_ + _).
     set Q' := cast_ord (esym (etrans _ _)) _; set Q := cast_ord (esym (etrans _ _)) _.
     case: (splitP Q) => t Qt.
      rewrite castmxE mxE eqE /=.
      rewrite /= in Ti, Sk.
      rewrite Sk prednK // in Ti.
      move/eqP: Ti; rewrite eqn_add2l -Qt /= => ->.
      rewrite GRing.mulr1.
      by congr (x _ _); apply/val_inj.
     rewrite /= in Qt.
     suff: (r < r)%nat by rewrite ltnn.
     suff: (r + t < r)%nat by apply/leq_trans; rewrite ltnS leq_addr.
     rewrite prednK // in Qt.
     by rewrite -Qt.
    apply/etrans; first apply/eq_bigr => q /= P.
     set Q' := cast_ord (esym (etrans _ _)) _; set Q := cast_ord (esym (etrans _ _)) _.
     apply: (_ : _ = 0).
     case: (splitP Q) => t Qt.
      rewrite /= ?prednK // in Ti, Qt, Sk.
      rewrite castmxE mxE eqE /= -Qt.
      rewrite Ti in Sk; move/eqP: Sk; rewrite eqn_add2l => /eqP ->.
      case: q P Q' {Q Qt} => //= q ?.
      rewrite eqE /= => /negPf -> ?.
      by rewrite GRing.mulr0.
     by rewrite mxE GRing.mulr0.
    by apply sum_f2_eq0.
Qed.

Definition ra : 'rV_(1 + w.-1) := (row_mx a`_0%:M (\row_i a`_i.+1)).

Definition shiftr (x : 'rV['F_2]_w) : 'rV_(1 + w.-1) :=
row_mx 0 (\row_i castmx (erefl _, esym tecw') x ord0 (widen_ord (leqnSn w.-1) i)).

Definition computeB (x : 'rV['F_2]_p) :=
castmx (erefl _, tecnw)
(row_mx (rsubmx (lsubmx (castmx (erefl, esym choose_m) x)) + castmx (erefl _, tecw')
(shiftr (z' x) + ra *+ (castmx (erefl _, esym tecw') (z' x) ord0 ord_max == 1)))
        (y x)).

Lemma mulBE (x : 'rV['F_2]_p) : x *m B = computeB x.
Proof. by rewrite mulBE_hidden' mulSE ULE -/(z x) !zE. Qed.

Lemma mulBE0 (x : 'rV['F_2]_p) (k : 'I_(n.-1 * w - r)) :
  (x *m B) ord0 (cast_ord tecnw (rshift w k)) = y x ord0 k.
Proof.
  rewrite mulBE_hidden' mulSE ?(castmxE, mxE) /=.
  set T := cast_ord _ _.
  case: (splitP T) => j jT.
   suff: (j >= w)%nat.
    case: j {jT} => j H.
    by rewrite leqNgt /= H.
   by rewrite -jT /= leq_addr.
  rewrite ?(castmxE, mxE).
  congr (x _ _); apply/val_inj => //=.
  by move/eqP: jT; rewrite /= eqn_add2l eq_sym => /eqP.
Qed.

Definition row_ind (o : 'I_p) := Ordinal (ltn_pmod o w0).
Definition col_ind_prf (o : 'I_p) : (o %/ w < n)%nat.
Proof.
  case: o => o oH.
  by apply/leq_ltn_trans/pwn/(leq_div2r _ (ltnW oH)).
Qed.
Definition col_ind (o : 'I_p) :=
  Ordinal (col_ind_prf o).

Definition arr_ind_prf (x : 'I_n) (y : 'I_w) : (x * w + y < n * w)%nat.
Proof.
 case: x => x xn; case: y => y yw.
 apply/leq_ltn_trans; first apply leq_add.
  apply: (_ : _ <= n.-1 * w)%nat.
   apply leq_mul => //.
   by case: n xn n0.
  apply: (_ : _ <= w.-1)%nat.
  by case: w w0 yw.
 case: n n0 => // n' _; case: w w0 => // w' _ /=.
 by rewrite !mulSn !mulnS addnCA -!addnA ltn_add2l addnC ltn_add2r.
Qed.
Definition arr_ind_large (x : 'I_n) (y : 'I_w) := Ordinal (arr_ind_prf x y).
Definition arr_ind (x : 'I_n) (y : 'I_w) :=
match split (cast_ord (esym tecpr) (arr_ind_large x y)) with
| inl l => Some l
| inr r => None
end.

Record incomplete_matrix :=
  {
    matrix :> 'M['F_2]_(n, w);
    _ : [forall i, (w - r <= (i : 'I_w))%nat ==>  (matrix (Ordinal npn) i == 0%R)];
  }.

Lemma incomplete_matrix_eqP : Equality.axiom (fun a b => matrix a == matrix b).
Proof.
  case=> [] x Hx [] y Hy.
  apply/(iffP idP) => [|->//].
  move=> /eqP /= H; move: H Hx Hy => -> Hx Hy.
  congr Build_incomplete_matrix.
  apply bool_irrelevance.
Qed.

Canonical incomplete_matrix_eqMixin := EqMixin incomplete_matrix_eqP.
Canonical incomplete_matrix_eqType :=
   Eval hnf in EqType incomplete_matrix incomplete_matrix_eqMixin.

Definition incomplete_array (x :incomplete_matrix) :=
  \row_i x (col_ind i) (row_ind i).

Definition array_incomplete (y : 'rV['F_2]_p) : incomplete_matrix.
apply (@Build_incomplete_matrix (\matrix_(i, j) match arr_ind i j with
                                                | Some i => y ord0 i
                                                | None => 0%R
                                                end)).
apply/forallP => x; apply/implyP => rx.
rewrite mxE /arr_ind.
case: (splitP _) => k K //.
rewrite /= in K.
suff: (p <= k)%nat.
 by rewrite leqNgt; case: k K => //= ? H; rewrite H.
rewrite -K.
apply/leq_trans.
 apply: (_ : _ <= n.-1 * w + (w - r))%nat.
  by rewrite addnBA // addnC -mulSn prednK.
 by rewrite leq_add2l.
Defined.

Lemma array_incompleteK : cancel array_incomplete incomplete_array.
Proof.
move=> y; rewrite /incomplete_array /array_incomplete; apply/rowP => j.
rewrite !mxE /arr_ind.
case: (splitP _) => s /esym S; rewrite /= -divn_eq in S.
 by congr (y _ _); apply/val_inj.
suff: (p + s < p)%nat by rewrite ltnNge leq_addr.
by rewrite S.
Qed.

Lemma incomplete_arrayK : cancel incomplete_array array_incomplete.
Proof.
move=> y; apply/eqP; rewrite eqE /=; apply/eqP.
apply/matrixP => i j.
rewrite !mxE /arr_ind.
case: (splitP _) => k K.
 rewrite !mxE; congr (y _ _); apply/val_inj.
  by rewrite /= -K /= divnMDl // divn_small // addn0.
 by rewrite /= -K /= modnMDl modn_small.
case: y => y /= /forallP Hy.
case inpn : (i == Ordinal npn).
 move/eqP: inpn => inpn.
 have: (w - r <= j)%nat.
  rewrite /= inpn /= -[n]prednK // mulSn [(w + _)%nat in RHS]addnC /= -addnBA // -!addnA in K.
  move/eqP: K; rewrite eqn_add2l => /eqP ->.
  by rewrite leq_addr.
 move/implyP: (Hy j) => Hy' /Hy' /eqP <-.
 by congr (y _ _).
suff: (p + k < p)%nat by rewrite ltnNge leq_addr.
rewrite -K /= => {K y Hy}.
case: i inpn => i /= i0.
rewrite eqE /=; move: i0.
rewrite -[n]prednK // ltnS leq_eqVlt /= => + ni; move: ni => -> /= ni.
apply/leq_ltn_trans.
 apply: (_ : _ <= n.-2 * w + w)%nat.
  rewrite leq_add // ?leq_mul //; last by apply/ltnW.
  rewrite -[n.-1]prednK // in ni.
  case: (n.-1) mn => //.
 rewrite mulSn [(w + _)%nat]addnC -addnBA // addnC -mulSn prednK;
  last by case: (n.-1) mn.
 by rewrite -[X in (X < _)%nat]addn0 ltn_add2l leqNgt /leq subSS
            subn0 subn_eq0 -ltnNge.
Qed.

Lemma iw (i : 'I_(n * w - r)) : (i - w < n * w - r)%nat.
Proof.
  case: i => i H.
  apply: (leq_trans _ H).
  by rewrite /= ltnS leq_subr.
Qed.

Lemma computeBE_large (v : 'rV_(n * w - r)) (i : 'I_(n * w - r)) :
  (i >= w)%nat ->
  (v *m B)%R ord0 i = v ord0 (Ordinal (iw i)).
Proof.
  rewrite /computeB mulBE /computeB => wi.
  rewrite !castmxE !mxE.
  set R := cast_ord _ _.
  case: (splitP R) => q.
   case: q => //= q C iq.
   by rewrite leqNgt iq C in wi.
  rewrite ?(mxE, castmxE) => /= Rwq.
  congr (v _ _); apply/val_inj => //.
  by rewrite /= Rwq addnC addnK.
Qed.

Lemma mwi (i : 'I_(n * w - r)) :
  (i < w)%nat ->
  (m.-1 * w + i < n * w - r)%nat.
Proof.
  case: i => i H wi.
  by rewrite /= -choose_m -addnA ltn_add2l ltn_addr.
Qed.

Lemma computeBE_small (v : 'rV_(n * w - r)) (i : 'I_(n * w - r)) (wi : (i < w)%nat) :
  (v *m B)%R ord0 i =
  v ord0 (Ordinal (mwi wi))
+ (shiftr (z' v) + ra *+ (castmx (erefl, esym tecw') (z' v) ord0 ord_max == 1))
    ord0 (cast_ord (esym tecw'') (Ordinal wi)).
Proof.
  rewrite /computeB mulBE /computeB.
  rewrite !castmxE !mxE.
  set R := cast_ord _ _.
  case: (splitP R) => q.
   case: q => //= q C iq.
   rewrite ?(mxE, castmxE).
   congr (v _ _ + _) => //; try apply/ord_inj => //.
    by rewrite /= iq.
   set A := cast_ord _ _.
   set B := cast_ord (esym tecw'') _.
   have->: A = B by apply/ord_inj.
   by rewrite !cast_ord_id.
  move=> /= iq.
  suff: false by [].
  by rewrite iq ltnNge leq_addr in wi.
Qed.

Lemma break_if (T : 'F_2) :
  (if T == 1%R then 1%R else 0%R) = T.
Proof.
  case: ifP => [/eqP/esym //|].
  case: T => [][|[]]// *.
  by apply/val_inj.
Qed.

Lemma if_xorb (T1 T2 : bool)  :
  (if xorb T1 T2 then 1%R else 0%R : 'F_2) =
  ((if T1 then 1%R : 'F_2 else 0%R) + (if T2 then 1%R else 0%R))%R.
Proof.
  case: T1 T2 => [][]//=.
   by rewrite GRing.addrr_char2.
  by rewrite GRing.addr0.
Qed.

Lemma nth_rot T y i z (d : T) :
  (y + i < size z)%nat ->
  nth d (rot y z) i = nth d z (y + i).
Proof.
  move=> H.
  rewrite nth_cat size_drop.
  case: ifP.
   by rewrite nth_drop.
  by rewrite ltnNge /leq -subnDA subn_eq0 -ltnNge H.
Qed.

Local Notation ai := array_incomplete.
Local Notation ia := incomplete_array.
Import BinNat.
Record valid_random_state :=
  {
    state :> random_state;
    _ : size (state_vector state) == n;
    _ : ((index state) < n)%nat;
    _ : [forall i, (((i : 'I_n) < size (state_vector state)) ==>
                        (nth 0%N (state_vector state) i <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w)))))%nat];
    _ : [forall x, ((w - r <= (x : 'I_w))%nat ==>  ((rev (word_of_N w (nth 0%N (state_vector state) (index state))))`_x == 0))];
  }.

Record vector_with_counter :=
  {
    vector :> 'rV['F_2]_p;
    counter : nat;
    _ : (counter < n)%nat;
  }.

(* Definition with_count (cv : (nat * ) * 'rV['F_2]_p) := *)
(*    ((cv.1.1.+1 %% n)%nat, (cv.2 *m B)%R). *)

Definition array_of_state (y : valid_random_state) : vector_with_counter.
  apply: (@Build_vector_with_counter (ia _) (nat_of_bin (index y)));
   last by case: y.
  apply: (@Build_incomplete_matrix 
  (\matrix_(i, j) nth 0%R (nth (word_of_N w 0)
      [seq (@rev_tuple _ _ \o word_of_N w) i 
           | i <- rev (rot (index y) (state_vector y))] i) j)%R).
  apply/forallP => x; apply/implyP => H.
  case: y => state0 /= /eqP i i0 i1 /forallP /(_ x) /implyP /(_ H) i2.
  rewrite mxE (nth_map 0%N) ?size_rev ?size_rot; last
   by rewrite i npn.
  rewrite nth_rev ?size_rot; last
   by rewrite i npn.
  by rewrite /= prednK // i subnn nth_rot ?i addn0.
Defined.

Definition state_of_array (cy : vector_with_counter) : valid_random_state.
  apply: (@Build_valid_random_state 
  {| index:=bin_of_nat (counter cy);
     state_vector:=rev (rot (counter cy) (map (@N_of_word w \o (@rev_tuple _ _))
      (mktuple (fun j => mktuple (fun x => ai cy j x))))); |}).
  + by rewrite /= size_rev size_rot 2!size_map size_enum_ord.
  + case: cy => /= *.
    by rewrite bin_of_natK.
  + apply/forallP => x; apply/implyP => H.
    rewrite /= nth_rev size_rot 2!size_map size_enum_ord; last first.
     by rewrite /= size_rev size_rot 2!size_map size_enum_ord in H.
  + rewrite nth_cat.
    case: ifP.
     rewrite nth_drop.
     case cyn: (counter cy + (n - x.+1) < n)%nat.
      rewrite (nth_map (word_of_N w 0)); last 
       by rewrite size_map size_enum_ord.
      by rewrite bound_N_of_word.
     by rewrite nth_default // 2!size_map size_enum_ord leqNgt cyn.
    case cyx: (n - x.+1 - (n - counter cy) < counter cy)%nat.
     rewrite nth_take size_drop 2!size_map size_enum_ord //.
     rewrite (nth_map (word_of_N w 0)); last first.
      rewrite size_map size_enum_ord.
      by apply/(leq_trans cyx); case: cy {cyx H} => /= *; apply/ltnW.
     by rewrite bound_N_of_word.
    rewrite nth_default // size_take size_drop 2!size_map size_enum_ord.
    case: ifP => H0.
     by rewrite leqNgt cyx.
    rewrite ltnNge leq_eqVlt negb_or -ltnNge ltnS ltnW ?andbT in H0;
      last by case: cy {cyx H}.
    move/negP/negP: H0 => /eqP cny.
    by rewrite leqNgt [X in (_ < X)%nat]cny cyx.
  + apply/forallP => x; apply/implyP => wrx.
    case: cy => vector0 counter0 i.
    rewrite /=.
    rewrite /= rev_rot.
    rewrite 
    rewrite 
     rewrite 
      rewrite 
     rewrite subKn.
     rewrite 
     rewrite 
      rewrite /=.
     Search (_ - _  + _)%nat.
      rewrite addnBA.
      -addnBA. subKn.
    Check rev_ord_
     
    rewrite nth_rot; last first.
     rewrite 2!size_map size_enum_ord.
    

Lemma state_of_arrayK : cancel state_of_array array_of_state.
Proof.
  case=> c x.
  rewrite /array_of_state /state_of_array.
  rewrite /= rev_rot revK bin_of_natK rotK.
  set T := (\matrix_(_, _) _)%R; have->: T = (ai x)%R.
   apply/matrixP => i j; subst T.
   rewrite !mxE !revK (nth_map 0%N) /=.
   ; last
    by rewrite 2!size_map size_enum_ord.
   rewrite (nth_map (word_of_N w 0)) /=; last by rewrite size_tuple card_ord.
   by rewrite N_of_wordK ?revK ?nth_mktuple ?(castmxE, mxE).
  by rewrite array_incompleteK /= bin_of_natK.
Qed.

Lemma array_of_stateK : cancel array_of_state state_of_array.
Proof.

size (state_vector x) = n ->
(index x < size (state_vector x))%nat ->
(forall i, i < size (state_vector x) ->
 nth 0%N (state_vector x) i <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))))%nat ->

Lemma ltP' i p : reflect ([Num of i] < [Num of p])%N (i < p)%nat.
Proof.
  apply/(iffP idP).
   elim: p i => // p IH []// i.
   rewrite ltnS -!Num_succ => {}/IH H.
   by apply/N.add_lt_le_mono.
  elim: p i => [[]//|p IH []// i].
  by rewrite -!Num_succ -N.add_lt_mono_r ltnS; apply IH.
Qed.

Lemma rw'' : (bin_of_nat r <= bin_of_nat w)%nat.
Proof.
  apply/ltnW/ltP'.
  rewrite !bin_of_natK.
  by apply/ltP'.
Qed.

Local Notation next_random_state :=
  (@next_random_state
     (bin_of_nat n) (bin_of_nat n - bin_of_nat m)
     (bin_of_nat r) (N_of_word (rev_tuple a)) (bin_of_nat w) rw'').
Lemma size_next_random_state v :
size (state_vector (next_random_state (state_of_array v)).2) = n.
Proof.
rewrite /next_random_state size_set_nth size_tuple.
by case: n mn => []//[].
Qed.

Lemma size_next_random_state' v :
(index v < size (state_vector v))%nat ->
size (state_vector (next_random_state v).2) = size (state_vector v).
Proof.
move=> H.
rewrite /next_random_state size_set_nth /maxn.
case: ifP => //.
by rewrite ltnNge leq_eqVlt ltnNge H orbF => /negP/negP/eqP ->.
Qed.

Lemma mod_1_l x : (x > 1)%N -> 1 mod x = 1%N.
Proof. case: x => //. by elim. Qed.

Lemma index_next_random_state v :
index (next_random_state (state_of_array v)).2 = 1%N.
Proof.
  have: n != 1%N.
   apply/eqP => n1.
   move: n1 mn => ->.
   by rewrite ltn0.
  move=> n1.
  rewrite /= mod_1_l //.
  case: n n1 mn => []//[]// n' _ _.
  rewrite ?succ_nat /=.
  apply/N.gt_lt_iff.
  elim: n' => // n' IH.
  apply/N.lt_trans; first by apply IH.
  rewrite -!N.add_1_r -!N.add_lt_mono_r succ_nat.
  apply N.lt_succ_diag_r.
Qed.

Lemma nth_next_random_state v i :
  nth 0%N (state_vector (next_random_state (state_of_array v)).2) i.+1%N
= nth 0%N (state_vector (state_of_array v)) i.+1.
Proof. by rewrite nth_set_nth. Qed.

Lemma nth_state_vector v (i : 'I_n) :
  nth 0%N (state_vector (state_of_array v)) i =
  N_of_word (rev_tuple (mktuple (ai v (rev_ord i)))).
Proof.
rewrite nth_rev; last by rewrite 2!size_map size_enum_ord.
rewrite (nth_map (word_of_N w 0)) size_map size_tuple ; last by rewrite rev_ord_proof.
have ord0n: 'I_n.
 case: n mn => // *.
 by apply ord0.
have ord0w: 'I_w.
 case: w w0 => // *.
 by apply ord0.
rewrite (nth_map ord0n) ?size_tuple ?rev_ord_proof //.
congr N_of_word.
apply/eq_from_tnth => j.
rewrite !(tnth_nth ord0) !nth_rev ?size_tuple //
        !(nth_map ord0w) ?size_tuple ?rev_ord_proof
        ?(esym (enumT _), size_enum_ord, rev_ord_proof) //.
by congr (ai _ _); apply/ord_inj; rewrite /= nth_enum_ord ?rev_ord_proof.
Qed.

Lemma testbit_N_of_word a' w' v : (a' < w')%nat ->
  N.testbit (@N_of_word w' v) (bin_of_nat a') = (nth 1%R v a' == 1%R).
Proof.
move=> aw.
rewrite -[in RHS](N_of_wordK v).
have -> : a' = Ordinal aw by [].
rewrite nth_word_of_N.
by case: ifP.
Qed.

Local Lemma tns v b a' (Ha : (a' < w)%nat) (Hb : (b < n)%nat) :
  N.testbit (nth 0%N (state_vector (state_of_array v)) b) [Num of a']
= (ai v (rev_ord (Ordinal Hb)) (rev_ord (Ordinal Ha)) == 1%R).
Proof.
  have ord0w: 'I_w.
   case: w w0 => // *.
   by apply ord0.
  have H: b = val (Ordinal Hb) by [].
  rewrite [in LHS]H nth_state_vector.
  have {H} H : a' = val (Ordinal Ha) by [].
  rewrite [in LHS]H testbit_N_of_word //  nth_rev ?size_tuple //
          (nth_map ord0w) ?size_tuple ?rev_ord_proof //.
  congr (_ == _); congr (ai _ _); apply/ord_inj.
  by rewrite nth_enum_ord ?rev_ord_proof.
Qed.

Lemma testbita i x :
  (i < w)%nat ->
  (if N.testbit (@N_of_word w x) [Num of i] then 1%R else 0%R) = nth 0%R x i.
Proof.
  move=> iw.
  rewrite -[x]N_of_wordK.
  have ->: i = Ordinal iw by [].
  by rewrite (nth_word_of_N (N_of_word x) 0%R) N_of_wordK.
Qed.

Lemma mod_small x y : (x < y)%N -> x mod y = x.
Proof.
  move=> xy.
  apply N.Private_NZDiv.mod_small.
  split => //.
  by elim: x {xy}.
Qed.

Lemma size_state_vector_random_state y :
(index y < size (state_vector y))%nat ->
size (state_vector (next_random_state y).2) = size (state_vector y).
Proof.
  case: y => y z H.
  by rewrite /= size_set_nth maxnE addnBA // addnC addnK.
Qed.

Lemma bin_of_nat_mn :
 (bin_of_nat m < bin_of_nat n)%N.
Proof.
by apply/ltP'.
Qed.

Hint Resolve bin_of_nat_mn : core.

Lemma mod1n : (1 mod bin_of_nat n = 1)%N.
Proof.
  rewrite mod_small //.
  case: n mn => []//[]// *.
  rewrite -addn2 -bin_of_add_nat.
  by apply N.lt_lt_add_l.
Qed.

Lemma rot_succ T (y : N) (z : seq T) :
  (y <= size z)%nat ->
  rot (N.succ y mod bin_of_nat (size z)) z = rot 1 (rot y z).
Proof.
  move=> yz.
  case sz: (size z == 0)%nat.
   by case: z sz yz.
  rewrite rot_add_mod //; last by rewrite lt0n sz.
  case: ifP => H.
   rewrite leq_eqVlt in H.
   case/orP: H => [/eqP|] C.
    rewrite -C add1n bin_succ nat_of_binK N.Private_NZDiv.mod_same.
     by rewrite -bin_succ -add1n C rot0 rot_size.
    by case: y yz C.
   rewrite mod_small.
    by rewrite -bin_succ add1n.
   move/ltP': C.
   by rewrite -Num_succ /= nat_of_binK N.add_1_r.
  move/negP/negP: H.
  rewrite -ltnNge add1n ltnS => zy.
  have yze: (size z = y)%nat.
   apply/eqP.
   by rewrite eqn_leq yz zy.
  case so: (size z == 1)%nat.
   case: z so yz sz zy yze => // ? []// so yz sz zy yze.
   by rewrite N.mod_1_r subSS subn0 -yze rot_size rot0.
  congr (rot _ _).
  rewrite yze nat_of_binK subSn // subnn.
  rewrite -N.add_1_r N.Private_NZDiv.add_mod //; last first.
   case: (size z) zy sz => // n' H _.
   move/ltP': H.
   rewrite !nat_of_binK /=.
   apply/N.le_lt_trans.
   by move: (@pos_Num n').
   move: (@pos_Num y).
   by rewrite nat_of_binK.
  rewrite N.mod_same; last first.
   rewrite yze in sz.
   by case: y sz yz zy yze.
  have ?: (y > 1)%N.
   rewrite yze in so.
   case: y so yz zy yze sz => //.
    by move=> + + + /eqP ->.
    by case.
  by rewrite N.add_0_l !mod_1_l.
Qed.

Lemma rot_set_nth T y z (d v : T) :
  (y < size z)%nat ->
  rot y (set_nth d z y v) = set_nth d (rot y z) 0 v.
Proof.
  move=> H.
  apply/(@eq_from_nth _ d).
   rewrite !(size_rot, size_set_nth) /maxn.
   case: ifP; case: ifP => //.
   + by case: (size z) H => []//[].
   + move=> ? /negP/negP.
     by rewrite -ltnNge ltnS leq_eqVlt ltnNge H orbF => /eqP ->.
   + by case: z y H => []//?[]//[].
  move=> i H0.
  rewrite nth_set_nth /= !nth_cat.
  rewrite !size_drop size_set_nth.
  case: ifP => H1.
   case: ifP => H2.
    move/eqP: H2 => ->.
    by rewrite nth_drop addn0 nth_set_nth /= eqxx.
   case: ifP => H3.
    rewrite !nth_drop nth_set_nth /=.
    case: ifP => //.
    by rewrite -[X in _ == X]addn0 eqn_add2l H2.
   move: H1; rewrite /maxn.
   case: ifP; first by rewrite H3.
   rewrite subSn // subnn.
   by case: i H0 H2 H3 => //.
  case: ifP => H2.
   move/negP/negP: H1.
   rewrite -ltnNge (eqP H2) /leq subSS subn0 subn_eq0 leqNgt.
   suff ->: (y < maxn y.+1 (size z))%nat by [].
   rewrite /maxn.
   by case: ifP.
  case: ifP => H3.
   move: H1; rewrite /maxn.
   case: ifP; first by rewrite H3.
   rewrite ltnNge leq_eqVlt ltnNge H orbF => /negP/negP/eqP zy.
   rewrite zy subSn // subnn in H3.
   by case: i H0 H2 H3.
  have C: maxn y.+1 (size z) = size z.
   rewrite /maxn.
   case: ifP => //.
   rewrite ltnNge leq_eqVlt ltnNge H orbF.
   by move/negP/negP/eqP ->.
  rewrite C.
  case izyy: (i - (size z - y) < y)%nat.
   rewrite !nth_take // nth_set_nth /=.
   case: ifP => // /eqP iy.
   by rewrite iy ltnn in izyy.
  by rewrite ?nth_default // !size_take ?size_set_nth ?C !H leqNgt izyy.
Qed.

Lemma nmn : (bin_of_nat n - bin_of_nat m < n)%nat.
Proof.
  case: n m mn m0 => []// n' []// m' ? _.
  by rewrite ltnS !bin_of_natK subSS leq_subr.
Qed.

Lemma nmn' : (bin_of_nat n - bin_of_nat m < bin_of_nat n)%N.
Proof.
  move/ltP' : nmn; apply: N.le_lt_trans.
  apply N.eq_le_incl.
  elim: n m => // n' IHn [|m'].
   rewrite subn0 N.sub_0_r nat_of_binK.
   by elim: n'.+1.
  by rewrite !succ_nat !N.sub_succ IHn /= -!bin_succ subSS.
Qed.

Lemma nat_of_sub_bin x y : (nat_of_bin x - nat_of_bin y)%nat = nat_of_bin (x - y).
Proof.
  rewrite -[y]nat_of_binK -[x]nat_of_binK.
  set X := (nat_of_bin x).
  elim: (nat_of_bin y) X.
   move=> {x} x.
   by rewrite /= N.sub_0_r subn0.
  move=> {x y} y IHy []// x.
  by rewrite !succ_nat !N.sub_succ -!bin_succ subSS IHy.
Qed.

Hint Resolve nmn nmn' : core.

Lemma next_random_stateE v :
  (array_of_state \o snd \o next_random_state \o state_of_array) v = (v *m B)%R.
Proof.
  apply/rowP => i.
* case wi: (i >= w)%nat.
  rewrite computeBE_large // !mxE ?castmxE ?mxE (nth_map 0%N)
          ?nth_rev ?size_tuple ?size_rot ?ltn_pmod //
          ?size_rev ?size_rot ?size_next_random_state //.
  set R := row_ind _.
  have<-: (rev_ord R = w - R.+1 :> nat)%nat by [].
  rewrite nth_word_of_N index_next_random_state
          ?size_rot ?size_next_random_state ?nth_drop //
          nth_cat size_drop ?size_next_random_state.
  set B := (n - _ < _)%nat.
  case: (ifP B) => Bt.
  + rewrite nth_drop add1n nth_next_random_state tns.
    - subst B R.
      case: (col_ind i) Bt => ?.
      case: n => // n' ?.
      by rewrite /= ltnS subn1.
    - by case: (rev_ord R).
    - move=> Hyp0 Hyp1.
      rewrite break_if mxE.
      congr (v _ _); apply/val_inj => //.
      have->: Ordinal Hyp1 = rev_ord R by apply/val_inj.
      rewrite rev_ordK /= /arr_ind /=.
      set A := cast_ord _ _.
      have vA: (val A = i - w)%nat.
       rewrite /= 3!subnS -!subn1 -!subnDA !addn1 subnDA subKn ?col_ind_prf //.
       rewrite subSS mulnBl addnBAC.
        by rewrite -divn_eq  mul1n.
       apply leq_mul => //; apply/leq_trans/leq_div2r/wi.
       rewrite divnn; by case: w rw.
      case: (splitP A) => j.
       by move=> <-; rewrite vA.
      rewrite vA => C3.
      have C1: (i < n * w - r + j)%nat by rewrite ltn_addr.
      have : (i - w < n * w - r + j)%nat.
       apply: (leq_trans _ C1).
       by rewrite ltnS leq_subr.
      by rewrite C3 ltnn.
  + subst B.
    rewrite /= in Bt.
    rewrite (divn_eq i w) in wi.
    have wi': (i %/ w = 0)%nat.
     have: (n > i %/ w)%nat.
      apply: (leq_trans _ pwn).
      rewrite ltnS leq_div2r //.
      case: i {R Bt wi} => *; by apply /ltnW.
     case: (i %/ w)%nat Bt wi => // m'.
     rewrite subnS -subn1 subnAC ltn_subrL subn1 => H.
     suff: false by [].
     by case: n mn {v i R} H => []//[].
    rewrite wi' mul0n add0n leqNgt ltn_mod in wi.
    suff: false by []. by case: w wi rw.

* move/negP/negP: wi; rewrite -ltnNge => wi.
  rewrite computeBE_small // !mxE ?castmxE ?mxE (nth_map 0%N)
          ?nth_rev ?size_tuple ?size_rot ?ltn_pmod //
          ?size_rev ?size_rot ?size_next_random_state //.
  set R := row_ind _.
  have<-: (rev_ord R = w - R.+1 :> nat)%nat by [].
  rewrite nth_word_of_N index_next_random_state
          ?size_rot ?size_next_random_state ?nth_drop //
          nth_cat size_drop ?size_next_random_state.
  set B := (n - _ < _)%nat.
  have iw0: (i %/ w = 0)%nat by rewrite divn_small.
  case: (ifP B) => Bt.
   subst B.
   by rewrite /= iw0 ltnn in Bt.
  rewrite nth_take; last by rewrite /= iw0 subnn.
  rewrite subn1 ?(mxE, castmxE) nth_set_nth.
  set A := (n - _ - _)%nat.
  have->: A = 0%nat by rewrite /A /= iw0 subn1 subnn.
  rewrite !N.lxor_spec // N.shiftr_spec //; last by apply/pos_Num.
  rewrite !N.lor_spec !N.land_spec !if_xorb !tns.
  + rewrite /= mod_small //.
    apply/ltP'.
    by rewrite /= !nat_of_binK.
  + by case: (rev_ord R).
  + move=> Hyp0 Hyp1.
    rewrite !break_if ?(cast_mxE, mxE) -!GRing.addrA.
    have->: Ordinal Hyp1 = rev_ord R by apply/val_inj.
    have ord0n: (0 < n)%nat by case: n mn.
    have <-: val (Ordinal ord0n) = index (state_of_array v) by [].
    have ord1n: (1 < n)%nat by case: n mn => []//[].
    have <-: val (Ordinal ord1n) = N.succ (index (state_of_array v)) mod bin_of_nat n.
     rewrite /= mod_1_l //.
     apply/N.gt_lt_iff.
     apply/ltP': ord1n.
    rewrite ?rev_ordK !nth_state_vector ?(mxE, castmxE).
    congr (_ + _)%R; first congr (v _ _); apply/ord_inj => //.
    - rewrite /= /arr_ind.
      case: (splitP _) => [j <- |j].
       rewrite /= mod_small // subnS -nat_of_sub_bin !bin_of_natK subKn; last by apply/ltnW.
       by rewrite modn_small.
      rewrite /= mod_small // subnS -nat_of_sub_bin !bin_of_natK subKn; last by apply/ltnW.
      rewrite modn_small // => C.
      suff: (p + j < p)%nat by rewrite ltnNge leq_addr.
      rewrite -C.
      apply/leq_trans.
       apply: (_ : (_ < m.-1 * w + w)%nat).
       by rewrite ltn_add2l.
      rewrite addnC -mulSn prednK //.
      apply/leq_trans.
       apply: (_ : (_  <= n.-1 * w)%nat).
       apply /leq_mul => //.
       case: n mn => []//[]//= n' mn'.
       by apply/leq_trans/leqW/mn'/leqW.
      by rewrite -[n]prednK // mulSn prednK // addnC -addnBA // leq_addr.
    - have ->: 0%N = [Num of (val (Ordinal w0))] by [].
      rewrite ?testbit_N_of_word ?nth_rev ?size_tuple ?nth_cat ?size_rep //; try by (apply/ltP'; rewrite bin_of_natK; apply/ltP').
      have <-: val (rev_ord (Ordinal w0)) = (w - (Ordinal w0).+1)%nat by [].
      have c: (val (Ordinal w0) < bin_of_nat r)%nat
       by apply/ltP'; rewrite bin_of_natK; apply/ltP'.
      rewrite !c !nth_rep // nth_mktuple mxE andbF andbT orFb.
      set X := (ra *+ _) _ _.
      set Y := (if N.testbit _ [Num of val _] then 1 else 0)%R.
    - have->: X = Y.
      subst X Y.
      case: (splitP _) => j /= C.
       suff: (w - 1 < w - r)%nat by rewrite ltnNge leq_sub2l.
       by rewrite subn1 C.
      rewrite (nth_map (Ordinal wi) (1%R : 'F_2)) ?(mxE, castmxE)
              ?size_enum_ord; last by (rewrite subn1; case: w w0).
      set X := v _ _.
      set Y := v _ _.
      have->: X = Y.
       subst X Y.
       congr (v _ _); apply/val_inj => //.
       rewrite /= -[n.-1]prednK; last by case: n mn => []//[].
       rewrite mulSn [(w + _)%nat]addnC -addnBA // -addnA -C.
       rewrite /arr_ind /=.
       case: (splitP _) => [k <-|k].
        rewrite /= nth_enum_ord ?subn1 ?subn2 //.
        by case: w w0.
       rewrite /= subn2 subn1 => {C} C.
       suff: (p + k < p)%nat by rewrite ltnNge leq_addr.
       rewrite -C nth_enum_ord; last by case: w w0.
       case: n mn => []//[]// n' mn'.
       rewrite mulSn [(w + _)%nat]addnC -addnBA //= mulSn.
       apply/leq_trans/leq_addr.
       rewrite addnC.
       by case: w rw.
      case: (Y == 1)%R; last by rewrite GRing.mulr0n /= mxE.
      rewrite testbita // GRing.mulr1n mxE.
      have ->: (w - (i %% w).+1 = rev_ord (Ordinal wi))%nat.
       by rewrite /= modn_small.
      have ->: (rev_tuple a)`_(rev_ord (Ordinal wi)) = a`_i.
       rewrite nth_rev size_tuple /= subnS ?subKn //.
       case: i {R Hyp1 B Bt iw0 A Y} wi.
       case: w rw => //= *.
       by rewrite ltnS subSn //= leq_subr.
      case: (splitP _) => [k|k /= ->].
       case: k => []//[]// k /= ->.
       case: a => [][]//= *; by rewrite mxE.
      rewrite mxE add1n.
      case: a => [][]//= *; by rewrite mxE.
    - case: (splitP _) => [[][]//= ? ->|k C].
       by rewrite mod0n subn1 Num_succ !prednK // ?N_of_word_last /= ?mxE.
      have x: ((val (rev_ord R)).+1 < w)%nat.
       rewrite /= in C.
       rewrite /= modn_small // -subSn // subSS C add1n.
       case: k {C} => /= k.
       case: w rw => // w'.
       by rewrite subSS !ltnS leq_subr.
      rewrite Num_succ ?(mxE, castmxE) !testbit_N_of_word ?nth_rev ?size_tuple ?nth_cat //;
              try by apply/ltP'; rewrite !bin_of_natK; apply/ltP'.
      rewrite !size_rep.
      have->: (w - (val (rev_ord R)).+2 = rev_ord (Ordinal x))%nat by [].
      case Rr: ((val (rev_ord R)).+1 < bin_of_nat r)%nat.
       rewrite !nth_rep // andbT andbF orFb nth_mktuple break_if.
       rewrite /= in C.
       case: (splitP _) => l; last first.
        rewrite ?(mxE, castmxE) !cast_ord_id /= => kl.
        set Z := arr_ind _ _.
        set W := cast_ord _ _.
        suff->: Z = W by [].
        subst Z W.
        apply/val_inj.
        rewrite /arr_ind.
        case: (splitP _) => [? /= <-|].
         rewrite modn_small // -!subSn //; last by apply/ltnW.
         rewrite subSS subSn; last by apply/ltnW.
         rewrite !subnS subKn; last by apply/ltnW.
         rewrite subn0.
         case: (n.-1) mn => // n' _.
         by rewrite mulSn [(w + _)%nat]addnC -addnBA // -addnA -kl C add1n.
        rewrite /= modn_small // -!subSn //; last by apply/ltnW.
        rewrite subSS subSn; last by apply/ltnW.
        rewrite !subnS subKn; last by apply/ltnW.
        rewrite subn0 => o C'.
        suff: (p + o < p)%nat by rewrite ltnNge leq_addr.
        rewrite -C' C add1n.
        case: n mn => []//[]// n' mn'.
        rewrite mulSn [(w + _)%nat]addnC -addnBA //= mulSn.
        apply/leq_trans/leq_addr.
        rewrite addnC ltn_add2r.
        case: k {C kl} => /=.
        by case: w => // *; apply/ltnW.
       rewrite /= modn_small // -subSn // subSS C add1n in Rr.
       rewrite /= => kl.
       have ?: (l < w)%nat.
        case: l {kl} => l /= lwr.
        apply/leq_trans; first apply lwr.
        by rewrite leq_subr.
       rewrite kl -subSn // ?subSS in Rr.
       have: (w - (w - r) < w - l)%nat.
        apply ltn_sub2l => //.
       rewrite subKn // => rwl.
       move/ltP': (leq_trans rwl Rr).
       rewrite bin_of_natK => /ltP'.
       by rewrite ltnn.
      rewrite !nth_rep // ?ltn_sub2r //;
              try by apply/ltP'; rewrite !bin_of_natK; apply/ltP'.
      rewrite andbT andbF orbF nth_mktuple break_if.
      rewrite /= in C.
      case: (splitP _) => l.
       rewrite ?(mxE, castmxE) !cast_ord_id /= => kl.
       set Z := arr_ind _ _.
       set W := cast_ord _ _.
       suff->: Z = W by [].
       subst Z W.
       apply/val_inj.
       rewrite /arr_ind.
       case: (splitP _) => [? /= <-|].
        rewrite modn_small // -!subSn //; last by apply/ltnW.
        rewrite subSS subSn; last by apply/ltnW.
        rewrite !subnS subKn; last by apply/ltnW.
        by rewrite subn0 addnA subnK // C add1n kl.
       rewrite /= modn_small // -!subSn //; last by apply/ltnW.
       rewrite subSS subSn; last by apply/ltnW.
       rewrite !subnS subKn; last by apply/ltnW.
       rewrite subn0 => o C'.
       suff: (p + o < p)%nat by rewrite ltnNge leq_addr.
       rewrite -C' C add1n.
       case: n mn => []//[]// n' mn'.
       rewrite mulSn [(w + _)%nat]addnC -addnBA //= mulSn.
       by rewrite kl ltn_add2l.
      rewrite /= modn_small // -subSn // subSS C add1n in Rr.
      rewrite /= => kwrl.
      rewrite kwrl -subSn // ?subSS in Rr; last first.
       apply/leq_trans.
        apply: (_ : _ < w - r + r)%nat.
        rewrite ltn_add2l //.
       by rewrite subnK.
      rewrite subnDA subKn // in Rr.
      move/negP/negP: Rr.
      rewrite -ltnNge => /ltP'.
      rewrite bin_of_natK => /ltP'.
      by rewrite ltnNge leq_subr.
Qed.
End Main.
