From mathcomp
Require Import all_ssreflect all_algebra all_field all_fingroup.
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
    case jrk: (val j == r + k)%N => //.
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
| inl l => l
| inr r => cast_ord (esym tecp) ord0
end.

Definition incomplete_array (x : 'M['F_2]_(n, w)) :=
  \row_i x (col_ind i) (row_ind i).

Definition array_incomplete (y : 'rV['F_2]_p) : 'M_(n, w) :=
  \matrix_(i, j) y ord0 (arr_ind i j).

Lemma array_incompleteK : cancel array_incomplete incomplete_array.
Proof.
move=> y; rewrite /incomplete_array /array_incomplete; apply/rowP => j.
rewrite !mxE; congr (y _ _); apply/ord_inj.
rewrite /arr_ind; set T := cast_ord _ _.
case: (splitP T) => s Ts; rewrite /= -divn_eq in Ts.
 by rewrite Ts.
suff: (p < p)%nat by rewrite ltnn.
suff: (p + s < p)%nat; first by apply/leq_trans; rewrite ltnS leq_addr.
by rewrite -Ts.
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

Require Import mt BinNat BinPos nat_word.

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

Local Notation ai := array_incomplete.
Local Notation ia := incomplete_array.

Definition array_of_state (y : random_state) :=
  ia (\matrix_(i, j) nth 0%R (nth (word_of_N w 0)
      [seq (@rev_tuple _ _ \o word_of_N w) i | i <- rev (rot (index y) (state_vector y))] i) j)%R.

Definition state_of_array (y : 'rV['F_2]_(n * w - r)) :=
  {| index:=0;
     state_vector:=rev (map (@N_of_word w \o (@rev_tuple _ _))
      (mktuple (fun j => mktuple (fun x => ai y j x))));|}.

Lemma state_of_arrayK : cancel state_of_array array_of_state.
Proof.
  move=> x.
  rewrite /array_of_state /state_of_array rot0.
  set T := (\matrix_(_, _) _)%R; have->: T = (ai x)%R.
   apply/matrixP => i j; subst T.
   rewrite !mxE !revK (nth_map 0) /=; last by rewrite 2!size_map size_enum_ord.
   rewrite (nth_map (word_of_N w 0)) /=; last by rewrite size_tuple card_ord.
   by rewrite N_of_wordK ?revK ?nth_mktuple ?(castmxE, mxE).
  by rewrite array_incompleteK.
Qed.

Lemma size_next_random_state v :
size (state_vector (next_random_state (state_of_array v)).2) = n.
Proof.
rewrite /next_random_state size_set_nth size_tuple.
by case: n mn => []//[].
Qed.

Lemma index_next_random_state v :
index (next_random_state (state_of_array v)).2 = 1.
Proof.
  have: n != 1.
   apply/eqP => n1.
   move: n1 mn => ->.
   by rewrite ltn0.
  by case: n => []//[]//.
Qed.

Lemma nth_next_random_state v i :
  nth 0 (state_vector (next_random_state (state_of_array v)).2) i.+1%N
= nth 0 (state_vector (state_of_array v)) i.+1.
Proof. by rewrite nth_set_nth. Qed.

Lemma nth_state_vector v (i : 'I_n) :
  nth 0 (state_vector (state_of_array v)) i =
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

Lemma testbit_N_of_word v a' :
  N.testbit (@N_of_word w v) [Num of val a'] = (tnth v a' == 1%R).
Proof.
rewrite (tnth_nth 0%R) -[in RHS](N_of_wordK v) nth_word_of_N.
by case: ifP.
Qed.

Local Lemma tns v b a' (Ha : (a' < w)%nat) (Hb : (b < n)%nat) :
  N.testbit (nth 0 (state_vector (state_of_array v)) b) [Num of a']
= (ai v (rev_ord (Ordinal Hb)) (rev_ord (Ordinal Ha)) == 1%R).
Proof.
  have ord0w: 'I_w.
   case: w w0 => // *.
   by apply ord0.
  have H: b = val (Ordinal Hb) by [].
  rewrite [in LHS]H nth_state_vector.
  have {H} H : a' = val (Ordinal Ha) by [].
  rewrite [in LHS]H testbit_N_of_word (tnth_nth ord0) nth_rev ?size_tuple //
          (nth_map ord0w) ?size_tuple ?rev_ord_proof //.
  congr (_ == _); congr (ai _ _); apply/ord_inj.
  by rewrite nth_enum_ord ?rev_ord_proof.
Qed.

Local Lemma tnsw v b (Hb : (b < n)%nat) :
  N.testbit (nth 0 (state_vector (state_of_array v)) b) [Num of w] = false.
Proof.
  by rewrite /state_of_array /= nth_rev ?(size_enum_ord, size_map) //
          (nth_map (word_of_N w 0%N)) ?(size_enum_ord, size_map)
          ?(rev_ord_proof (Ordinal Hb)) // N_of_word_last.
Qed.

Notation upper_mask := (N.shiftl 1 (bin_of_nat r)).
Notation lower_mask := (upper_mask - 1).

Lemma ltP' i p : reflect ([Num of i] < [Num of p]) (i < p)%nat.
Proof.
  apply/(iffP idP).
   elim: p i => // p IH []// i.
   rewrite ltnS -!Num_succ => {}/IH H.
   by apply/N.add_lt_le_mono.
  elim: p i => [[]//|p IH []// i].
  by rewrite -!Num_succ -N.add_lt_mono_r ltnS; apply IH.
Qed.

Lemma upper_maskF i : (i < r)%nat -> N.testbit upper_mask [Num of i] = false.
Proof.
  move=> ir.
  rewrite N.shiftl_spec_low //.
  by apply/ltP'.
Qed.

Lemma double_predE x : x > 0 -> N.double x - 1 = N.double (x - 1) + 1.
Proof.
  case: x => // x _.
  by elim: x.
Qed.

Lemma lower_maskT i : (i < r)%nat -> N.testbit lower_mask [Num of i] = true.
Proof.
  elim: r i => // r' IH i.
  rewrite succ_nat N.shiftl_succ_r double_predE //.
  case: i => [|i ir].
   by rewrite N.testbit_odd_0.
  rewrite -Num_succ N.double_spec [[Num of i] + 1]N.add_1_r
          N.testbit_odd_succ ?IH //.
  by elim: i {ir}.
Qed.

Lemma testbita i :
  (i < r)%nat ->
  (if N.testbit (N_of_word a) [Num of i] then 1%R else 0%R) = nth 0%R a i.
Proof.
  move=> ir.
  rewrite -[a]N_of_wordK.
  have iw : (i < w)%nat by apply/ltn_trans/rw.
  have ->: i = Ordinal iw by [].
  by rewrite (nth_word_of_N (N_of_word a) 0%R) N_of_wordK.
Qed.

Lemma next_random_stateE v :
  (array_of_state \o snd \o next_random_state \o state_of_array) v = (v *m B)%R.
Proof.
  rewrite /computeB mulBE /cycle.computeB.
  apply/rowP => i.
  rewrite !mxE ?castmxE ?mxE (nth_map 0)
          ?nth_rev ?size_tuple ?size_rot ?ltn_pmod //
          ?size_rev ?size_rot ?size_next_random_state //.
  set R := row_ind _ _ _.
  have<-: (rev_ord R = w - R.+1 :> nat)%nat by [].
  set I := (cast_ord _ i); subst R.
  rewrite nth_word_of_N /cycle.B index_next_random_state
          ?size_rot ?size_next_random_state ?nth_drop //
          nth_cat size_drop ?size_next_random_state.
  set I' := col_ind _ _ _ _ _.
  case: (splitP I) => j Ij; rewrite /= in Ij; last first.
   have I'0: (I' > 0)%nat.
    by rewrite /= Ij divnDl.
   have->: (n - I'.+1 < n - 1%N)%nat.
    rewrite /leq subn1 subnS.
    case H: (n - I' > 0)%nat.
     by rewrite prednK // subnAC -subn1 subnBA.
    rewrite lt0n in H.
    by move/negP/negP/eqP: H => ->.
   rewrite nth_drop add1n nth_next_random_state tns => *.
     rewrite /leq -!subSn //;last by apply/leqW.
     by rewrite subnAC subSn //.
    by rewrite (rev_ord_proof (Ordinal (@ltn_pmod i w erefl))).
   rewrite break_if !mxE !castmxE.
   congr (v _ _); apply/ord_inj => //.
   rewrite /arr_ind /=.
   set T := cast_ord _ _.
   case: (splitP T) => k /=.
    rewrite Ij 3!subnS -!subn1 -!subnDA !addn1 subnDA subKn.
     rewrite subn2 /= !divnDl // divnn add1n modnDl // -subSn
             ?ltn_mod // subSS subKn; last by rewrite ltnW // ltn_mod.
     by rewrite -divn_eq => ->.
    rewrite divnDl // add1n /leq !subSS subn_eq0.
    case: j {Ij} => j H.
    apply/leq_trans.
     apply leq_div2r.
     by apply H.
    by [].
   rewrite Ij 3!subnS -!subn1 -!subnDA !addn1 subnDA subKn.
    rewrite subn2 /= !divnDl // divnn add1n modnDl // -subSn
            ?ltn_mod // subSS subKn; last by rewrite ltnW // ltn_mod.
    rewrite -divn_eq => jnwr.
    case: j {Ij} jnwr => j H jnwr.
    suff: (n.-1 * w - r < n.-1 * w - r)%nat by rewrite ltnn.
     apply/leq_trans.
      apply: (_ : _ < n * w - r)%nat; first by rewrite ltn_sub2r.
     apply/leq_trans.
      apply: (_ : _ <= n * w - r + k)%nat; first by rewrite leq_addr.
     apply/ltnW.
     by rewrite -jnwr.
    rewrite divnDl // add1n /leq !subSS subn_eq0.
    case: j {Ij} => j H.
    apply/leq_trans.
     apply leq_div2r.
     by apply H.
    by [].

   have->: val I' = 0 by rewrite /= Ij divn_small.
   rewrite subn1 ltnn ?(mxE, castmxE) subnn nth_take // nth_set_nth.
   rewrite !N.lxor_spec // N.shiftr_spec // N.lor_spec !N.land_spec.
   rewrite !if_xorb tns ?(rev_ord_proof (Ordinal (@ltn_pmod i w erefl))) // => Hp.
   rewrite !break_if.
   rewrite mxE -!GRing.addrA.
   congr (_ + _)%R; first congr (v _ _); apply/ord_inj => //.
   rewrite /= /arr_ind; set P := cast_ord _ _.
   case: (splitP P) => l Pl.
    by rewrite /= modn_small ?Ij // 2!subSS subKn // -ltnS in Pl.
   move/eqP: Pl; rewrite /= modn_small ?Ij //.
   have H: (n = n - m.+1 + m.+1)%nat by rewrite subnK.
   rewrite [X in _ == (X * _ - _ + _)%nat]H mulnDl eqn_add2l => /eqP je.
   suff: (w < w)%nat by rewrite ltnn.
   apply/leq_trans/(_ : j < w)%nat => //.
   rewrite 2!subSS // subKn // in je; last by rewrite -ltnS.
   by rewrite ltnS je.

   set R := cast_ord _ _.
   case: (splitP (R : 'I_(1 + w.-1))) => r Rr.
    rewrite /= in Rr.
    case: r Rr => [][]// ? Rr.
    rewrite Num_succ.
    set T := (val (rev_ord _)).+1.
    have->: T = w by rewrite /T /= Ij Rr mod0n subn1.
    rewrite ?tnsw // ?mxE !GRing.add0r.
    set S := cast_ord _ _; case: (splitP S) => s Ss; first by case: s Ss => [][].
    rewrite ?(mxE, castmxE).
    rewrite ?N.lor_spec ?N.land_spec.
    have->: 0 = [Num of 0] by [].
    rewrite ?tns // !mxE /= andbF andbT.
    set L := v _ _; set R0 := v _ _; have<-: L = R0.
     congr (v _ _); apply/ord_inj => //.
     rewrite /arr_ind.
     set T' := cast_ord _ _.
     case: (splitP T') => t //= T't.
     rewrite /= in T't, Ss.
     have-> //: val s = 30.
     rewrite subSn // subnn add1n in Ss.
     by case: Ss.
    rewrite /= Ij Rr mod0n subn1 /=.
    case L1: (L == 1%R).
     rewrite mxE.
     case: (splitP (R : 'I_(1 + w.-1))) => r' Rr'.
      case: r' Rr' => [][]// *.
      by rewrite mxE -GRing.mulr_natr.
     by rewrite /= Rr in Rr'.
    by rewrite mxE.
   (**)
   rewrite !Num_succ !tns.
    rewrite /= in Rr.
    by rewrite /= Ij Rr add1n modn_small ?subSS ?ltnS ?leq_subr // -ltnS //.
    rewrite /= in Rr.
    by rewrite /= Ij Rr add1n modn_small ?subSS ?ltnS ?leq_subr // -ltnS //.
   move=> ? ?.
   rewrite ?N.lor_spec ?N.land_spec.
   have->: 0 = [Num of 0] by [].
   rewrite ?tns // !mxE andbF andbT ?(castmxE, mxE).
   set P := cast_ord _ _; set Q' := cast_ord (esym _) _; set Q := cast_ord (esym _) _.
   case: (splitP Q) => q Qq.
    by case: q Qq => [][]//.
   rewrite /= in Qq.
   case: (splitP P) => p Pp.
    case: p Pp => [][]// p Pp.
    rewrite /= in Pp, Rr.
    set TT := val (rev_ord _).
    have TT30: TT = 30.
     subst TT.
     by rewrite /= Ij Rr Pp addn0 modn_small //.
    have->: N.testbit lower_mask [Num of TT.+1] = false by rewrite TT30.
    have->: N.testbit upper_mask [Num of TT.+1] = true by rewrite TT30.
    rewrite ?(mxE, castmxE) andbT andbF orbF.
    set X := v _ _; set Y := v _ _; set Z := v _ _; set W := v _ _.
    have->: X = Z.
     congr (v _ _); apply/ord_inj => //.
     rewrite /arr_ind /=.
     set Tmp := cast_ord _ _.
     case: (splitP Tmp) => t Tmpt.
      by rewrite -Tmpt /= TT30.
     by rewrite /= TT30 in Tmpt.
    have q30: val q = 30.
     rewrite /= subSn // subnn add1n in Qq.
     by case: Qq.
    have->: Y = W.
     congr (v _ _); apply/ord_inj => //.
     rewrite /arr_ind /=.
     set Tmp := cast_ord _ _.
     case: (splitP Tmp) => t Tmpt //.
     by rewrite -Tmpt /= q30.
    case: (W == 1)%R.
     rewrite mxE.
     case: (splitP (R : 'I_(1 + w.-1))) => r' Rr';
      rewrite /= in Rr'.
      case: r' Rr' => [][]//= ? Rr'.
      by rewrite Rr' in Rr.
     rewrite Rr' !add1n in Rr.
     case: Rr => Rr.
     rewrite TT30 /= mxE /= Rr Pp /=.
     case ZE: (Z == 1)%R.
      by move/eqP: ZE => ->.
     by case: Z ZE => [][]//[]//.
    rewrite mxE TT30 /=.
    by case: Z => [][]//[]//.
   rewrite /= in Pp, Rr.
   have q30: val q = 30.
    rewrite /= subSn // subnn add1n in Qq.
    by case: Qq.
   rewrite ?(mxE, castmxE).
   set A := v _ _.
   set X := v _ _; set Y := v _ _; set Z := v _ _; set W := v _ _.
   have->: X = Z.
    congr (v _ _); apply/ord_inj => //.
    rewrite /= /arr_ind.
    set Tmp := cast_ord _ _.
    case: (splitP Tmp) => t Tmpt.
     rewrite -Tmpt /= Ij Rr Pp.
     rewrite modn_small; last by rewrite -Pp add1n ltnS.
     by rewrite 3!subSS !subnDA subn1 -subnDA subKn subSn // -Pp -ltnS.
    rewrite /= Ij Rr Pp modn_small in Tmpt; last by rewrite -Pp add1n ltnS.
    rewrite 3!subSS !subnDA subn1 -subnDA subKn subSn // -Pp in Tmpt;
     last by rewrite -ltnS.
    suff: (n.-2 * w + r < n.-2 * w + r)%nat by rewrite ltnn.
    rewrite [X in (_ < X)%nat]Tmpt.
    apply/leq_trans.
     apply: (_ : _ < n.-2 * w + w.-1)%nat; first by rewrite ltn_add2l.
    by [].
   have->: W = Y.
    congr (v _ _); apply/ord_inj => //.
    rewrite /= /arr_ind.
    set Tmp := cast_ord _ _.
    case: (splitP Tmp) => t Tmpt //.
    by rewrite -Tmpt /= q30.
   set TT := val (rev_ord _).
   have TTwp2: (TT = gluing.r - p.+2)%nat.
    subst TT.
    by rewrite /= Ij modn_small // Rr Pp subSS.
   have->: N.testbit lower_mask [Num of TT.+1] = true.
    rewrite add1n in Pp.
    rewrite lower_maskT // TTwp2 -subSn.
     by rewrite subSS ?rev_ord_proof.
    by rewrite -Pp.
   have->: N.testbit upper_mask [Num of TT.+1] = false.
    rewrite add1n in Pp.
    rewrite upper_maskF // TTwp2 -subSn.
     by rewrite subSS ?rev_ord_proof.
    by rewrite -Pp.
   rewrite andbF andbT /= break_if.
   case YE: (Y == 1%R).
    rewrite TTwp2 mxE.
    case: (splitP (R : 'I_(1 + w.-1))) => r' Rr';
     rewrite /= in Rr'.
     case: r' Rr' => [][]// ? Rr'.
     by rewrite Rr' in Rr.
    rewrite Rr' !add1n in Rr.
    case: Rr => Rr.
    have->: r' = r by apply/ord_inj.
    have->: p.+1 = r by rewrite Pp.
    rewrite mxE nth_rev ?size_tuple // ?subSS; last by rewrite ltnS.
    rewrite testbita //.
    apply/leq_ltn_trans.
     apply leq_subr.
    by [].
   by rewrite mxE /=.
Qed.

End Main.
