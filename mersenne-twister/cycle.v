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

Lemma mpn : m <= n.-1.
Proof.
  case: n mn => []//[]//[]// n'.
  rewrite /= ltnS => H.
  by apply/(leq_trans (ltnW H))/leqW.
Qed.

Lemma n0 : 0 < n.
Proof. by case: n n2. Qed.

Lemma pn0 : 0 < n.-1.
Proof. by case: n n2 => []//[]. Qed.

Lemma n1 : 1 < n.
Proof. by case: n mn => []//[]. Qed.

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

Lemma rnw : r < n * w.
Proof.
  case: n n0 => // n' _.
  rewrite mulSn.
  by apply/leq_trans/leq_addr.
Qed.

Lemma wnw : w < n * w.
Proof.
  case: n n2 => []//[]//[]// n' _.
  rewrite mulSn -[X in (X < _)%nat]addn0 ltn_add2l.
  by rewrite mulSn ltn_addr // w0.
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

Lemma eqn_sub2r x y z : x > y -> x > z -> x - y == x - z = (y == z).
Proof.
  move=> yx zx.
  apply/eqP.
  case: ifP => [/eqP -> //|C C0].
  suff: false by []; rewrite -{}C.
  elim: x y z yx zx C0 => // x IH y z.
  rewrite ltnS leq_eqVlt => /orP [/eqP ->|yx].
   rewrite subSn // subnn ltnS leq_eqVlt => /orP [/eqP ->//|zx].
   rewrite subSn; last by apply/ltnW.
   by move/eqP; rewrite eqSS eq_sym subn_eq0 leqNgt zx.
  rewrite ltnS leq_eqVlt => /orP [/eqP ->|zx /eqP].
   rewrite subSn; last by apply/ltnW.
   rewrite subSn // subnn // => /eqP.
   by rewrite eqSS subn_eq0 leqNgt yx.
  rewrite !subSn // ?eqSS; try by apply/ltnW.
  by move=> /eqP /IH ->.
Qed.

Hint Resolve p0 n2' n0 w0 rw' rnwp rnpw rnmw wnpwr mn' wr0 rnw pn0 mpn : core.
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

Lemma valid_random_state_eqP : Equality.axiom (fun a b => state a == state b).
Proof.
  case=> [] x Hx1 Hx2 Hx3 Hx4 [] y Hy1 Hy2 Hy3 Hy4.
  apply/(iffP idP) => [/eqP /= H|->//].
  move: H Hx1 Hx2 Hx3 Hx4 Hy1 Hy2 Hy3 Hy4 => -> *.
  by congr Build_valid_random_state; apply bool_irrelevance.
Qed.

Canonical valid_random_state_eqMixin := EqMixin valid_random_state_eqP.
Canonical valid_random_state_eqType :=
   Eval hnf in EqType valid_random_state valid_random_state_eqMixin.

Record vector_with_counter :=
  {
    vector :> 'rV['F_2]_p;
    counter : nat;
    _ : (counter < n)%nat;
  }.

Lemma vector_with_counter_eqP :
  Equality.axiom
  (fun a b => (vector a == vector b) && (counter a == counter b)).
Proof.
  case=> [] x cx Hx [] y cy Hy.
  apply/(iffP idP) => [/andP [] /= /eqP -> /eqP H|->].
   move: H Hx Hy => -> *.
   by congr Build_vector_with_counter; apply bool_irrelevance.
  by rewrite !eqxx.
Qed.

Canonical vector_with_counter_eqMixin := EqMixin vector_with_counter_eqP.
Canonical vector_with_counter_eqType :=
   Eval hnf in EqType vector_with_counter vector_with_counter_eqMixin.

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
    rewrite /= rev_rot nth_cat size_drop size_rev 2!size_map subKn;
      last by rewrite size_enum_ord ltnW.
    rewrite bin_of_natK ltnn take_rev 2!size_map subnn subKn;
      last by rewrite size_enum_ord ltnW.
    rewrite !nth_rev; last first.
     by rewrite size_drop 2!size_map size_enum_ord leqNgt /leq subSS subn0 subn_eq0 -ltnNge i.
     by rewrite size_tuple.
     by rewrite size_drop 2!size_map size_enum_ord leqNgt /leq subSS subn0 subn_eq0 -ltnNge i.
    rewrite size_drop 2!size_map size_enum_ord.
    rewrite size_tuple.
    have->: (w - x.+1 = rev_ord x)%nat by [].
    rewrite nth_drop addnBA; last
     by rewrite leqNgt /leq subSS subn0 subn_eq0 -ltnNge i.
    rewrite addnC subnK; last by apply/ltnW.
    rewrite subn1 (nth_map (word_of_N w 0)); last
     by rewrite size_map size_enum_ord npn.
    rewrite N_of_wordK nth_rev size_tuple //.
    rewrite (nth_map (Ordinal n0)) ?size_enum_ord ?npn //.
    have ->: (w - (rev_ord x).+1  = (rev_ord (rev_ord x)))%nat by [].
    rewrite rev_ordK nth_mktuple mxE.
    have <-: Ordinal npn = (nth (Ordinal n0) (enum 'I_n) n.-1).
     apply/ord_inj.
     by rewrite nth_enum_ord // npn.
    rewrite /arr_ind.
    case: (splitP _) => k K //.
    suff: (k >= p)%nat
     by rewrite leqNgt; case: k {K} => /= ? k; rewrite k.
    rewrite -K /=.
    apply/leq_trans.
     apply: (_ : _ <= n.-1 * w + (w - r))%nat.
     by rewrite addnBA // addnC -mulSn prednK.
    by rewrite leq_add2l.
Defined.

Lemma state_of_arrayK : cancel state_of_array array_of_state.
Proof.
  move=> x.
  apply/eqP; rewrite eqE /=.
  apply/andP; split; last
   by rewrite bin_of_natK eqxx.
  apply/eqP/matrixP => i j.
  rewrite !mxE.
  rewrite /= rev_rot revK bin_of_natK rotK.
  have ?: (j %/ w < n)%nat.
   apply/leq_ltn_trans.
    by apply/leq_div2r/(_ : _ <= p)%nat/ltnW.
   by rewrite divnMBl // divn_small // subn0 /dvdn modn_small
              // lt0n_neq0 // subn1 npn.
  rewrite -2!map_comp (nth_map (Ordinal n0))
          ?size_enum_ord //= N_of_wordK revK.
  have ->: (j %% w)%nat = Ordinal (ltn_pmod j w0) by [].
  rewrite nth_mktuple mxE /arr_ind.
  case: (splitP _) => k K.
   congr (x _ _); apply/ord_inj.
   + by case: i => [][]//.
   + by rewrite -K /= nth_enum_ord // -divn_eq.
  rewrite /= nth_enum_ord // -divn_eq in K.
  suff: (p > p + k)%nat by rewrite ltnNge leq_addr.
  by rewrite -K.
Qed.

Lemma size_enum_ord' x : size (Finite.enum (ordinal_finType x)) = x.
Proof.
  move: (size_enum_ord x).
  by rewrite size_map.
Qed.

Lemma array_of_stateK : cancel array_of_state state_of_array.
Proof.
  move=> x.
  apply/eqP; rewrite eqE.
  case: x => x i i0 i1 i2.
  apply/andP; split; last
   by rewrite /= nat_of_binK eqxx.
  apply/eqP/(@eq_from_nth _ 0%N).
   rewrite /= size_rev size_rot 2!size_map size_enum_ord.
   by apply/esym/eqP.
  move=> i3 H.
  rewrite /= rev_rot nth_cat size_rev.
  rewrite 2!size_map size_drop size_rev 2!size_map.
  rewrite size_enum_ord subKn; last by apply/ltnW.
  case: ifP => ix.
   rewrite nth_drop nth_rev; last first.
    rewrite 2!size_map size_enum_ord addnC addnBA; last by apply/ltnW.
    rewrite addnC -subnBA; last by apply/ltnW.
    rewrite ltnNge /leq in ix.
    case: (index x - i3)%nat ix => // q _.
    case: n n0 => // n' _.
    by rewrite subSS ltnS leq_subr.
  have xi3: ((index x - i3).-1 < index x)%nat.
   rewrite ltnNge /leq in ix.
   apply/leq_trans.
    apply: (_ : _ < (index x - i3))%nat.
     by case: (index x - i3)%nat ix.
   by apply/leq_subr.
  have nnn : (n - (n - index x + i3).+1 < n)%nat.
   rewrite subnS subnDA subKn; last by apply/ltnW.
   by apply/(leq_trans xi3)/ltnW.
  rewrite -!map_comp size_map (nth_map (Ordinal n0)) !size_enum_ord' //.
  rewrite /= -[RHS](word_of_NK w0); last first.
   rewrite /= size_rev size_rot 2!size_map size_enum_ord in H.
   move/forallP: (i1) => /(_ (Ordinal H)) /implyP /=; apply.
   by rewrite (eqP i).
  congr N_of_word.
  apply/eq_from_tnth => k.
  rewrite (tnth_nth 0%R) /= nth_rev; last by rewrite size_map size_enum_ord.
  rewrite size_map size_enum_ord (nth_map (Ordinal w0)); last
   by rewrite size_enum_ord (rev_ord_proof k).
  rewrite !mxE /arr_ind.
  case: (splitP _) => l L.
   rewrite !mxE /= rev_rot.
   rewrite (nth_map 0%N); last first.
    rewrite /rotr size_rev size_rot -L /=.
    have ->: (n - (n - index x + i3).+1)%nat = Ordinal nnn by [].
    by rewrite -enumT !nth_enum_ord ?(rev_ord_proof k) // size_rev (eqP i)
               divnMDl // divn_small ?(rev_ord_proof k) // addn0.
   rewrite /= nth_cat size_drop size_rev -L.
   have ->: (n - (n - index x + i3).+1)%nat = Ordinal nnn by [].
   rewrite -!enumT /= !nth_enum_ord ?(rev_ord_proof k) //
           divnMDl // divn_small ?(rev_ord_proof k) // addn0.
   rewrite subnS subnDA subKn; last by apply/ltnW.
   rewrite subKn (eqP i); last by apply/ltnW.
   rewrite xi3 modnMDl modn_small ?(rev_ord_proof k) //.
   rewrite /= size_rev size_rot 2!size_map size_enum_ord in H.
   rewrite nth_drop -subnS addnBA // subnK; last by apply/ltnW.
   rewrite !nth_rev ?(eqP i) ?size_tuple
           ?(rev_ord_proof k) ?(rev_ord_proof (Ordinal H)) //.
   rewrite -!subSn // !subSS !subKn; try by apply/ltnW.
   by rewrite -tnth_nth.
  move: L.
  have ->: (n - (n - index x + i3).+1)%nat = Ordinal nnn by [].
  rewrite -!enumT /= !nth_enum_ord ?(rev_ord_proof k) //.
  rewrite subnS subnDA subKn; last by apply/ltnW.
  rewrite addnBA // addnC -mulSn prednK; last
   by rewrite ltnNge leqn0 subn_eq0 -ltnNge.
  rewrite -[n]prednK // mulSn [(w + _)%nat]addnC -addnBA // => C.
  suff: (n.-1 * w > n.-1 * w + (w - r) + l)%nat.
   by rewrite ltnNge -addnA leq_addr.
  rewrite -C.
  apply/leq_trans.
   apply: (_: _ < (index x - i3) * w)%nat.
    rewrite subnS.
    apply/leq_trans.
     apply: (_ : (_ <= (index x - i3) * w - k)%nat).
      have: (((index x - i3) * w - k) > 0)%nat.
       rewrite ltnNge /leq in ix.
       case: (index x - i3)%nat ix => // ? _.
       rewrite mulSn addnC -addnBA; last by apply/ltnW.
       by rewrite ltn_addl // ltnNge leqn0 subn_eq0 -ltnNge.
      by case: ((index x - i3) * w - k)%nat.
     by apply/leq_subr.
  apply/leq_mul => //.
  apply/(leq_trans (leq_subr _ _)).
  by case: n i0 n0 {H}.


 rewrite /= size_rev size_rot 2!size_map size_enum_ord in H.
 have i3x : (i3 - index x < n)%nat.
  by apply/leq_trans/(leq_subr (index x))/ltn_sub2r.
 rewrite nth_take; last first.
  by rewrite ltn_sub2r.
 rewrite nth_rev;last first.
  by rewrite 2!size_map size_enum_ord.
 rewrite !size_map size_enum_ord' -!map_comp.
 rewrite (nth_map (Ordinal n0)) ?size_enum_ord'; last first.
  case: n n0 => // n' _.
  by rewrite subSS ltnS leq_subr.
 rewrite /= -[RHS](word_of_NK w0); last first.
  move/forallP: (i1) => /(_ (Ordinal H)) /implyP /=; apply.
  by rewrite (eqP i).
 congr N_of_word.
 apply/eq_from_tnth => k.
 rewrite (tnth_nth 0%R) /= nth_rev; last by rewrite size_map size_enum_ord.
 rewrite size_map size_enum_ord (nth_map (Ordinal w0)); last
  by rewrite size_enum_ord (rev_ord_proof k).
 rewrite !mxE /arr_ind.
 case: (splitP _) => l L.
  rewrite !mxE /= rev_rot.
  rewrite (nth_map 0%N); last first.
   rewrite /rotr size_rev size_rot -L /=.
   have ->: (n - (i3 - index x).+1)%nat = rev_ord (Ordinal i3x) by [].
   by rewrite -enumT !nth_enum_ord ?(rev_ord_proof k) // size_rev (eqP i)
              divnMDl // divn_small ?(rev_ord_proof k) // addn0.
  rewrite /= nth_cat size_drop size_rev -L.
  have ->: (n - (i3 - index x).+1)%nat = rev_ord (Ordinal i3x) by [].
  rewrite -!enumT /= !nth_enum_ord ?(rev_ord_proof (Ordinal i3x))
          ?(rev_ord_proof k) // divnMDl // divn_small ?(rev_ord_proof k)
          // addn0.
  rewrite subnS subKn; last by rewrite (eqP i) ltnW.
  rewrite subnBA; last by rewrite leqNgt ix.
  have->: ((n + index x - i3).-1 < index x)%nat = false.
   rewrite addnC -addnBA; last by apply/ltnW.
   rewrite ltnNge /leq in H.
   case: (n - i3)%nat H => // n' _.
   by rewrite addnS /= ltnNge leq_addr.
  rewrite modnMDl modn_small ?(rev_ord_proof k) //.
  rewrite nth_take //; last first.
   rewrite ltn_sub2r ?(eqP i) // -subnBA; last by rewrite leqNgt ix.
   rewrite -subnS.
   case: n n0 => // n' _ //.
   by rewrite subSS ltnS leq_subr.
  have ?: ((n + index x - i3).-1 - index x < n)%nat.
   rewrite -subnS subnAC addnK.
   case: n n0 => // n' _ //.
   by rewrite subSS ltnS leq_subr.
  rewrite !nth_rev ?(eqP i) ?size_tuple
          ?(rev_ord_proof k) ?(rev_ord_proof (Ordinal H)) //.
  rewrite -subnS subnAC addnK -!subSn // !subSS !subKn; try by apply/ltnW.
  by rewrite -tnth_nth.
 move: L.
 have ->: (n - (i3 - index x).+1)%nat = rev_ord (Ordinal i3x) by [].
 rewrite -!enumT /= !nth_enum_ord ?(rev_ord_proof k) ?(rev_ord_proof (Ordinal i3x)) //.
 rewrite addnBA // addnC -mulSn -subSn // subSS => C.
 case xi0: ((i3 - index x) == 0)%nat.
  rewrite (eqP xi0) subn0 addnBAC in C; try by apply/ltnW.
  rewrite -subnBA in C; try by apply/ltnW.
  rewrite subn_eq0 leq_eqVlt ix orbF in xi0.
  move/eqP: C.
  rewrite eqn_sub2r; last first.
   + apply/leq_trans/rnw.
     by rewrite ltnS leq_subr.
   + apply/leq_trans/wnw.
     by rewrite ltnS.
  move=> krl.
  have wrlw: (w - (r - l) < w)%nat by rewrite -(eqP krl) (rev_ord_proof k).
  move/forallP: i2 => /(_ (Ordinal wrlw)).
  rewrite /= subnBA; last by apply/ltnW.
  rewrite addnC -addnBA // leq_addl nth_rev ?size_tuple; last
   by rewrite addnBA // addnC -subnBA; last by apply/ltnW.
  rewrite /= subnS addnC subnDA subKn // (tnth_nth 0%R) -(eqP krl) /= => /eqP.
  by rewrite (eqP xi0) => ->.
 suff: (p > p + l)%nat by rewrite ltnNge leq_addr.
 rewrite -C; apply/leq_trans.
 apply: (_ : _ < (n - (i3 - index x)) * w)%nat.
  have C1: (0 < (n - (i3 - index x)))%nat.
   by rewrite ltnNge leqn0 subn_eq0 -ltnNge i3x.
  have : (0 < (n - (i3 - index x)) * w)%nat.
   case: (n - (i3 - index x))%nat C1 => // ? _.
   by rewrite mulSn ltn_addr.
  case: ((n - (i3 - index x)) * w)%nat => // ? _.
  by rewrite subSS ltnS leq_subr.
 rewrite -[n]prednK // mulSn addnC -addnBA //.
 apply/leq_trans/leq_addr.
 case: (i3 - index x)%nat xi0 => // ? _.
 by rewrite subSS leq_mul // leq_subr.
Qed.

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
case: v => v c cn.
by rewrite maxnE addnBA /= bin_of_natK // addnC addnK.
Qed.

Lemma mod_1_l x : (x > 1)%N -> 1 mod x = 1%N.
Proof. case: x => //. by elim. Qed.

Lemma index_next_random_state v :
  index (next_random_state (state_of_array v)).2
= bin_of_nat (counter v).+1 mod bin_of_nat n.
Proof. by rewrite /= -succ_nat. Qed.

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

Hint Resolve nmn nmn' : core.

(* Lemma nth_state_vector v (i : 'I_n) : *)
(*   nth 0%N (state_vector (state_of_array v)) i = *)
(*   N_of_word (rev_tuple (mktuple (ai v (rev_ord i)))). *)
(* Proof. *)
(* rewrite nth_rev; last by rewrite 2!size_map size_enum_ord. *)
(* rewrite (nth_map (word_of_N w 0)) size_map size_tuple ; last by rewrite rev_ord_proof. *)
(* have ord0n: 'I_n. *)
(*  case: n mn => // *. *)
(*  by apply ord0. *)
(* have ord0w: 'I_w. *)
(*  case: w w0 => // *. *)
(*  by apply ord0. *)
(* rewrite (nth_map ord0n) ?size_tuple ?rev_ord_proof //. *)
(* congr N_of_word. *)
(* apply/eq_from_tnth => j. *)
(* rewrite !(tnth_nth ord0) !nth_rev ?size_tuple // *)
(*         !(nth_map ord0w) ?size_tuple ?rev_ord_proof *)
(*         ?(esym (enumT _), size_enum_ord, rev_ord_proof) //. *)
(* by congr (ai _ _); apply/ord_inj; rewrite /= nth_enum_ord ?rev_ord_proof. *)
(* Qed. *)

Lemma testbit_N_of_word a' w' v : (a' < w')%nat ->
  N.testbit (@N_of_word w' v) (bin_of_nat a') = (nth 1%R v a' == 1%R).
Proof.
move=> aw.
rewrite -[in RHS](N_of_wordK v).
have -> : a' = Ordinal aw by [].
rewrite nth_word_of_N.
by case: ifP.
Qed.

Definition next_random_state' : valid_random_state -> N * valid_random_state.
  move=> v.
  apply: ((next_random_state v).1,
          @Build_valid_random_state (fil0 rw'' (next_random_state v).2) _ _ _ _).
  + case: v => v i i0 i1 i2.
    rewrite /= !size_set_nth (eqP i)
            [maxn (index v).+1 n]maxnE addnBA // addnC addnK.
    apply/eqP/maxn_idPr/ltP'.
    rewrite /= nat_of_binK; apply N.mod_lt.
    by case: n n0.
  + apply/ltP'.
    rewrite nat_of_binK; apply N.mod_lt.
    by case: n n0.
  + case: v => v i i0 i1 i2.
    apply/forallP => x.
    apply/implyP => xn.
    rewrite nth_set_nth /=.
    case: ifP => H.
     rewrite nth_set_nth /=.
     set T := _ == _.
     have Tf: T = false.
      apply/negP => /eqP /(f_equal bin_of_nat).
      rewrite !nat_of_binK -N.add_1_r.
      apply/eqP/negP.
      rewrite lem2 //; first by case: n n0.
      by rewrite N.mod_1_l; move/ltP': n1.
     rewrite Tf bound_land //.
     move/forallP: (i1) => /(_ _)/implyP i1'.
     have vn: (N.succ (index v) mod bin_of_nat n < n)%nat.
      apply/ltP'.
      rewrite /= nat_of_binK; apply N.mod_lt.
      by case: n n0.
     have->: nat_of_bin (N.succ (index v) mod bin_of_nat n) = Ordinal vn by [].
     apply/i1'.
     by rewrite (eqP i).
    rewrite nth_set_nth /=.
    case: ifP => H0; last first.
     move/forallP: (i1) => /(_ _)/implyP i1'.
     by apply/i1'; rewrite (eqP i).
    move/forallP: (i1) => /(_ _)/implyP i1'.
    apply/bound_lxor => //.
     apply/bound_lxor => //.
      set T := _ mod _.
      have vn: (T < n)%nat.
       apply/ltP'.
       rewrite /= nat_of_binK; apply N.mod_lt.
       by case: n n0.
      have->: nat_of_bin T = Ordinal vn by [].
      by apply/i1'; rewrite (eqP i).
     apply/leq_trans.
      set T := N.lor _ _.
      apply: (_ : _ <= T)%nat.
       case: T => []//.
       elim => //= p *.
        by rewrite natTrecE leqW // -addnn leq_addr.
       by rewrite natTrecE -addnn leq_addr.
     apply bound_lor => //; apply bound_land.
      rewrite -(eqP H0).
      by apply/i1'; rewrite (eqP i).
     have vn: (N.succ (index v) mod bin_of_nat n < n)%nat.
      apply/ltP'.
      rewrite /= nat_of_binK; apply N.mod_lt.
      by case: n n0.
     have->: nat_of_bin (N.succ (index v) mod bin_of_nat n) = Ordinal vn by [].
     apply/i1'.
     by rewrite (eqP i).
    case: ifP => // ?.
    by apply/bound_N_of_word.
  + case: v => v i i0 i1 i2.
    apply/forallP => x; apply/implyP => wrx.
    apply/eqP; rewrite /= nth_set_nth /= eqxx nth_set_nth /=.
    set T := _ == _.
    have Tf: T = false.
     apply/negP => /eqP /(f_equal bin_of_nat).
     rewrite !nat_of_binK -N.add_1_r.
     apply/eqP/negP.
     rewrite lem2 //; first by case: n n0.
     by rewrite N.mod_1_l; move/ltP': n1.
    rewrite Tf nth_rev ?size_tuple //.
    have->: (w - x.+1 = rev_ord x)%nat by [].
    rewrite nth_word_of_N N.land_spec testbit_N_of_word; last first.
     apply/ltP'; rewrite !bin_of_natK; apply/ltP'.
     by case: (rev_ord x).
    have xr: (val (rev_ord x) < bin_of_nat r)%nat.
     apply/leq_trans.
     apply: (_ : _ < w - (w - r))%nat.
      rewrite /= ltn_sub2l //.
      case: w r w0 r0 => []// w' []// r' _ _.
      by rewrite subSS ltnS leq_subr.
     by rewrite subnBA // addnC // addnK bin_of_natK.
    by rewrite nth_cat size_rep xr nth_rep // andbF.
Defined.

Lemma size_next_random_state' v :
size (state_vector (next_random_state' v).2) = n.
Proof.
case: v => v i i0 i1 i2.
rewrite !size_set_nth [maxn (index v).+1 _]maxnE (eqP i) addnBA // addnC addnK.
rewrite maxnE addnBA; last first.
 apply/ltP'.
  rewrite nat_of_binK.
   apply/N.mod_lt.
   by case: n n0.
by rewrite addnC addnK.
Qed.

(* Lemma nth_state_vector v (i : 'I_n) : *)
(*   nth 0%N (state_vector (state_of_array v)) i = *)
(*   N_of_word (rev_tuple (mktuple (ai v (rev_ord i)))). *)
(* Proof. *)
(* rewrite nth_rev size_rot 2!size_map size_enum_ord //. *)
(* rewrite /ai /=. *)
(* rewrite nth_cat size_drop size_map size_tuple. *)
(* rewrite (nth_map (word_of_N w 0)) size_map size_tuple; last by rewrite rev_ord_proof. *)
(* have ord0n: 'I_n. *)
(*  case: n mn => // *. *)
(*  by apply ord0. *)
(* have ord0w: 'I_w. *)
(*  case: w w0 => // *. *)
(*  by apply ord0. *)
(* rewrite (nth_map ord0n) ?size_tuple ?rev_ord_proof //. *)
(* congr N_of_word. *)
(* apply/eq_from_tnth => j. *)
(* rewrite !(tnth_nth ord0) !nth_rev ?size_tuple // *)
(*         !(nth_map ord0w) ?size_tuple ?rev_ord_proof *)
(*         ?(esym (enumT _), size_enum_ord, rev_ord_proof) //. *)
(* by congr (ai _ _); apply/ord_inj; rewrite /= nth_enum_ord ?rev_ord_proof. *)
(* Qed. *)

(* Local Lemma tns v b a' (Ha : (a' < w)%nat) (Hb : (b < n)%nat) : *)
(*   N.testbit (nth 0%N (state_vector (state_of_array v)) b) [Num of a'] *)
(* = (ai v (rev_ord (Ordinal Hb)) (rev_ord (Ordinal Ha)) == 1%R). *)
(* Proof. *)
(*   have ord0w: 'I_w. *)
(*    case: w w0 => // *. *)
(*    by apply ord0. *)
(*   have H: b = val (Ordinal Hb) by []. *)
(*   rewrite [in LHS]H. nth_state_vector. *)
(*   have {H} H : a' = val (Ordinal Ha) by []. *)
(*   rewrite [in LHS]H testbit_N_of_word //  nth_rev ?size_tuple // *)
(*           (nth_map ord0w) ?size_tuple ?rev_ord_proof //. *)
(*   congr (_ == _); congr (ai _ _); apply/ord_inj. *)
(*   by rewrite nth_enum_ord ?rev_ord_proof. *)
(* Qed. *)

Lemma testbita i x :
  (i < w)%nat ->
  (if N.testbit (@N_of_word w x) [Num of i] then 1%R else 0%R) = nth 0%R x i.
Proof.
  move=> iw.
  rewrite -[x]N_of_wordK.
  have ->: i = Ordinal iw by [].
  by rewrite (nth_word_of_N (N_of_word x) 0%R) N_of_wordK.
Qed.

(* Lemma mod_small x y : (x < y)%N -> x mod y = x. *)
(* Proof. *)
(*   move=> xy. *)
(*   apply N.Private_NZDiv.mod_small. *)
(*   split => //. *)
(*   by elim: x {xy}. *)
(* Qed. *)

(* Lemma size_state_vector_random_state y : *)
(* (index y < size (state_vector y))%nat -> *)
(* size (state_vector (next_random_state y).2) = size (state_vector y). *)
(* Proof. *)
(*   case: y => y z H. *)
(*   by rewrite /= size_set_nth maxnE addnBA // addnC addnK. *)
(* Qed. *)

Lemma bin_of_nat_mn :
 (bin_of_nat m < bin_of_nat n)%N.
Proof.
by apply/ltP'.
Qed.

Lemma n0' : (bin_of_nat n <> 0)%N.
Proof. by case: n n0. Qed.

Hint Resolve bin_of_nat_mn n0' : core.

Lemma mod1n : (1 mod bin_of_nat n = 1)%N.
Proof.
  rewrite N.mod_small //.
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
   rewrite N.mod_small.
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

Lemma rot1 (v : valid_random_state) :
  nth 0%N (rot (index v) (state_vector v)) (size (state_vector v) - n.-1) =
  nth 0%N (state_vector v) (N.succ (index v) mod bin_of_nat n).
Proof.
  case: v => state0 i i0 i1 i2.
  rewrite !(eqP i) -[n]prednK //= subSn // subnn
          nth_cat size_drop ltnNge /leq subn1 -subnS subn_eq0 leq_eqVlt negb_or
          -ltnNge ltnS (eqP i) i0 andbT.
  case: ifP => [H|/negP/negP H].
   rewrite nth_drop N.mod_small; last first.
    have/ltP': ((index state0).+1 < n)%nat by rewrite ltn_neqAle eq_sym H i0.
    by rewrite succ_nat /= nat_of_binK -[n]prednK.
   by congr nth; rewrite addn1 bin_succ.
  rewrite subnBA; last by apply/ltnW.
  rewrite add1n -(eqP H) subnn nth_take; last first.
   case: (nat_of_bin (index state0)) H i0 => //= /eqP n1.
   by move: n1 mn => ->.
  congr nth.
  rewrite -[LHS]bin_of_natK.
  congr nat_of_bin.
  rewrite /= -(N.mod_same (bin_of_nat n)) //.
  congr (_ mod _).
   by rewrite -[RHS]nat_of_binK -bin_succ -(eqP H).
  by rewrite -[n]prednK.
Qed.

Definition mulBwc (v : vector_with_counter) : vector_with_counter.
  apply (@Build_vector_with_counter (vector v *m B)%R
                                    (bin_of_nat (counter v).+1 mod bin_of_nat n)).
  apply/ltP'.
  rewrite !nat_of_binK.
  apply N.mod_lt.
  by case: n n0.
Defined.

Lemma ltn_subnS x y : (x > y -> x - y.+1 < x - y)%nat.
Proof. move=> xy. by apply ltn_sub2l. Qed.

Lemma vnn v : (v mod bin_of_nat n < n)%nat.
  apply/ltP'.
  rewrite nat_of_binK.
  apply/N.mod_lt.
  by case: n n0.
Qed.

Lemma col_val i (v : valid_random_state) :
 (col_ind i < size (state_vector v))%nat.
Proof.
  case: v => v i0 i1 i2 i3.
  by rewrite (eqP i0).
Qed.

Lemma niw (i : 'I_p) : (0 < n - i %/ w)%nat.
Proof.
  rewrite ltnNge leqn0 subn_eq0 -ltnNge.
  apply col_ind_prf.
Qed.

Lemma divn_large m' d :
  (d > 0)%nat -> (m' >= d)%nat -> ((m' %/ d) > 0)%nat.
Proof.
  move=> d0 dm'.
  apply/leq_trans/leq_div2r/dm'.
  by rewrite divnn d0.
Qed.

Lemma wkw k : (w - k.+1 < w)%nat.
Proof.
  case: w w0 => // ? _.
  by rewrite subSS ltnS leq_subr.
Qed.

Lemma wnwrw (l : 'I_r) :
 ((w - ((n.-1 * w - (r - l)) %% w).+1) = (r - l).-1)%nat.
Proof.
     rewrite -[n.-1]prednK // mulSn addnC -addnBA;
      last by apply/leq_trans/rw/leqW/leq_subr.
     rewrite modnMDl modn_small; last first.
      have: (r - l != 0)%nat by rewrite subn_eq0 -ltnNge.
      case: (r - l)%nat => // *.
      by rewrite wkw.
     by rewrite // !subnS subKn;
      last by apply/leq_trans/rw/leqW/leq_subr.
Qed.

Lemma npmnp : (n.-1 - m < n.-1)%nat.
Proof.
     case: (n.-1) pn0 => // ? _.
     case: m m0 => // ? _.
     by rewrite subSS ltnS leq_subr.
Qed.

Lemma w1 : (w > 1)%nat.
Proof.
  case: w rw => // w'.
  case: r r0 => // r' _.
  by case: w'.
Qed.

Lemma rkw k : (r - k < w)%nat.
Proof. by apply/leq_trans/rw/leq_subr. Qed.

Lemma rkw' k : (r - k <= w)%nat.
Proof. by apply/ltnW/rkw. Qed.

Lemma kwp (k : 'I_r) :
  w.-1 = (w - r + k)%nat -> k = r.-1 :> nat.
Proof.
  move/eqP.
  rewrite -subn1 addnBAC // -subnBA; last by apply/ltnW.
  rewrite eqn_sub2r ?w1 ?rkw // -[X in (X - k)%nat]prednK //.
  have kr : (k <= r.-1)%nat.
   case: k => k.
   by rewrite /= -[r]prednK.
  by rewrite subSn // eqSS eq_sym subn_eq0 leq_eqVlt ltnNge kr orbF eq_sym
     => /eqP.
Qed.

Lemma subnpn l : (l > 0 -> l - l.-1 = 1)%nat.
Proof.
  case: l => //= l _.
  by rewrite subSnn.
Qed.

Lemma rev_rev_ord i x : (i < x -> x - (x - i.+1).+1 = i)%nat.
Proof.
  move=> ix.
  by rewrite -subSn // subSS subKn // ltnW.
Qed.

Lemma mod_leq x : (x mod bin_of_nat n <= n.-1)%nat.
Proof.
  rewrite -ltnS prednK //.
  apply/ltP'.
  rewrite nat_of_binK.
  by apply/N.mod_lt.
Qed.

Lemma mod_pos x :
  (0 < nat_of_bin x < n -> x mod bin_of_nat n > 0)%nat.
Proof.
  case/andP=> x0 xn.
  rewrite N.mod_small //.
  move/ltP': xn.
  by rewrite nat_of_binK.
Qed.

Lemma succ_pos x : (0 < N.succ x)%nat.
Proof.
  apply/ltP'.
  by rewrite /= -bin_succ.
Qed.

Lemma eqnnS x : (x == x.+1 = false)%nat.
Proof. by elim: x. Qed.

Hint Resolve vnn col_val niw wkw npmnp rkw rkw' mod_leq succ_pos : core.

Lemma next_random_stateE v :
  (array_of_state \o snd \o next_random_state') v = (mulBwc \o array_of_state) v.
Proof.
  apply/eqP/andP; split; last first.
   move: (succ_nat (index v)) => /= ->.
   by rewrite !nat_of_binK.
  apply/eqP/rowP => i.
  rewrite 2!mxE (nth_map 0%N) ?size_rev ?size_rot //.
  have nvn : size (state_vector (next_random_state' v).2) = n.
   case: (next_random_state' v).2 => state0 i0 i1 i2 i3.
   by rewrite (eqP i0).
  have vn : size (state_vector v) = n.
   case: (v) => state0 i0 i1 i2 i3.
   by rewrite (eqP i0).
* case wi: (i >= w)%nat; last first.
  move/negP/negP: wi; rewrite -ltnNge => wi.
  rewrite computeBE_small // !mxE ?castmxE ?mxE (nth_map 0%N)
          ?nth_rev ?size_tuple ?size_rot ?ltn_pmod //
          ?size_rev ?size_rot ?size_next_random_state //.
  have->: col_ind i = Ordinal n0.
   apply/val_inj.
   by rewrite /= divn_small.
  have->: (w - (row_ind (Ordinal (mwi wi))).+1)%nat
        = rev_ord (row_ind (Ordinal (mwi wi))) by [].
  rewrite nvn vn subn1 nth_cat size_drop nvn nth_word_of_N.
  case: ifP => nn.
   rewrite nth_drop.
   have->: (w - (row_ind i).+1)%nat = rev_ord (Ordinal wi) by rewrite /= modn_small.
   rewrite nth_word_of_N /=.
   rewrite nth_set_nth /=.
   rewrite -[X in (_ == X)%nat]addn0.
   rewrite eqn_add2l.
   have->: (n.-1 == 0)%nat = false by case: n.-1 pn0.
   rewrite nth_set_nth /=.
   have vpn: index v = bin_of_nat n.-1.
    case: v {vn nvn} nn => state0 i0 + i2 i3 /= nn.
    rewrite -[n]prednK // ltnS leq_eqVlt prednK //.
    case/orP => [/eqP <-| H];first by rewrite nat_of_binK.
    move/ltP': nn.
    rewrite /= -bin_of_sub_nat nat_of_binK.
    rewrite -[N.succ _]nat_of_binK -bin_succ.
    rewrite N.mod_small; last first.
     rewrite -[n]prednK //.
     suff/ltP': ((nat_of_bin (index state0)).+1 < n.-1.+1)%nat by [].
     by rewrite ltnS.
    rewrite bin_of_sub_nat -addn1 addnC subnDA subn1 => /ltP'.
    by rewrite ltnNge leq_subr.
   set T := _ == _.
   have-> : T = true
    by rewrite /T vpn -succ_nat prednK // N.mod_same // add0n bin_of_natK eqxx.
   rewrite !N.lxor_spec !if_xorb.
   rewrite modnMDl modn_small // divnMDl // divn_small // addn0.
   rewrite -!GRing.addrA; congr (_ + _).
    congr (if _ then _ else _).
    rewrite vpn nth_cat size_drop vn prednK // bin_of_natK ltnNge leq_sub2l //=.
    rewrite -[X in (X - n.-1)%nat]prednK // subSn // subnn -subnDA addnC subnDA subn1.
    rewrite nth_take //.
    rewrite bin_of_sub_nat bin_of_add_nat addnBA; last by apply/ltnW.
    rewrite addnC -addnBA // -bin_of_add_nat -bin_of_sub_nat.
    rewrite N.add_mod // N.mod_same // N.add_0_l N.mod_mod // N.mod_small //; last first.
     rewrite -[n]prednK // bin_of_sub_nat.
     suff/ltP': (n.-1 - m < n.-1.+1)%nat by [].
     by rewrite ltnS leq_subr.
    by rewrite bin_of_sub_nat bin_of_natK.
    rewrite N.div2_spec N.shiftr_spec; last by apply N.le_0_l.
    rewrite N.lor_spec !N.land_spec.
    congr (_ + _).
     case: (splitP _).
      case => [][]//= ? ->.
      rewrite subn1 N.add_1_r -succ_nat prednK //.
      have ww: (bin_of_nat w) = [Num of bin_of_nat w] by rewrite bin_of_natK.
      rewrite [X in N.testbit (upper_mask _) X]ww
                 [X in N.testbit (lower_mask _) X]ww
                 !N_of_word_last ?bin_of_natK //.
       by rewrite !andbF mxE.
     move=> k K.
     rewrite !(mxE, castmxE).
     case: (splitP _) => l L.
      rewrite !(mxE, castmxE).
      rewrite (nth_map 0%N) ?size_rev ?size_rot ?vn //.
      rewrite nth_rev size_rot vn // nth_rev size_tuple // {T}.
      set T := (row_ind _)%nat.
      have->: (w - T.+1)%nat = rev_ord T by [].
      rewrite nth_word_of_N.
      rewrite nth_cat size_drop vn.
      rewrite /= addnA subnK // divnMDl // divn_small; last first.
       by apply/leq_trans/(leq_subr r).
      rewrite addn0 prednK // subnn vpn bin_of_natK.
      have ->: (n - n.-1 = 1)%nat
       by rewrite -[X in (X - _)%nat]prednK // subSn // subnn.
      rewrite nth_drop /= addn0 modnMDl modn_small; last first.
       by apply/leq_trans/(leq_subr r).
      rewrite /= add1n in K.
      rewrite -L /= -K N.add_1_r -succ_nat -subSn // subSS.
      rewrite !testbit_N_of_word ?bin_of_natK ?K //.
      rewrite nth_cat size_rep.
      have wkr: (w - k.+1 < bin_of_nat r)%nat = false.
       rewrite /= in K, L.
       rewrite L bin_of_natK ltnNge.
       apply/negP/negP.
       apply/leq_trans/(_ : w - (w - r) <= _)%nat.
        by rewrite subnBA // addnC addnK.
       by rewrite leq_sub2l.
      rewrite wkr nth_rep ?bin_of_natK; last by rewrite ltn_sub2r.
      rewrite eqxx nth_cat size_rep wkr nth_rep ?bin_of_natK; last by rewrite ltn_sub2r.
      by rewrite andbF orbF andbT.
     rewrite !(mxE, castmxE).
     rewrite (nth_map 0%N) ?size_rev ?size_rot ?vn //.
     rewrite nth_rev size_rot vn // nth_rev size_tuple // {T}.
     set T := (row_ind _)%nat.
     have->: (w - T.+1)%nat = rev_ord T by [].
     rewrite nth_word_of_N.
     rewrite nth_cat size_drop vn.
     rewrite /= in K, L.
     rewrite /= addnBAC // -subnBA; last by apply/ltnW.
     rewrite divnMBl // divn_small; last by apply/leq_trans/rw/leq_subr.
     rewrite /dvdn modn_small; last by apply/leq_trans/rw/leq_subr.
     rewrite subn_eq0 -ltnNge ltn_ord subn1 subn0 prednK //
             vpn bin_of_natK ltnn subnn.
     rewrite nth_take //.
     rewrite wnwrw !subnS N.add_1_r -succ_nat prednK; last by rewrite ltnNge leqn0 subn_eq0 -ltnNge.
     rewrite -succ_nat prednK // K L add1n !subnS.
     rewrite addnBAC // -subnBA; last by apply/ltnW.
     rewrite subKn; last by apply/leq_trans/rw/leqW/leq_subr.
     have rlprl: ((r - l).-1 < r - l)%nat.
      have: (r - l != 0)%nat by rewrite subn_eq0 -ltnNge.
      by case: (r - l)%nat.
     have rlw: ((r - l).-1 < w)%nat
      by apply/(leq_trans rlprl)/leq_trans/rw/leqW/leq_subr.
     rewrite !testbit_N_of_word ?bin_of_natK //.
     rewrite !nth_cat !size_rep ![X in (_ < X)%nat]bin_of_natK.
     rewrite (leq_trans rlprl (leq_subr _ _))
             !nth_rep ?bin_of_natK ?(leq_trans rlprl (leq_subr _ _)) //.
     by rewrite andbF andbT N.mod_same.
    rewrite !N.lor_spec !N.land_spec.
    case: (splitP _) => k K.
     rewrite /= in K.
     have C: (w - r <= w.-1)%nat by rewrite -subn1 leq_sub2l.
     by rewrite leqNgt K ltn_ord in C.
    rewrite !(mxE, castmxE).
    rewrite (nth_map 0%N) ?size_rev ?size_rot ?vn //.
    rewrite nth_rev size_rot vn // nth_rev size_tuple // {T}.
    set T := (row_ind _)%nat.
    have->: (w - T.+1)%nat = rev_ord T by [].
    rewrite nth_word_of_N nth_cat size_drop vn.
    rewrite /= addnBAC // -subnBA; last by apply/ltnW.
    rewrite divnMBl // divn_small; last by apply/leq_trans/rw/leq_subr.
    rewrite /dvdn modn_small; last by apply/leq_trans/rw/leq_subr.
    rewrite subn_eq0 -ltnNge ltn_ord subn1 subn0 prednK //
            vpn bin_of_natK ltnn subnn.
    rewrite nth_take // wnwrw.
    have->: (0 = bin_of_nat 0%nat)%N by [].
    rewrite !testbit_N_of_word ?bin_of_natK //.
    rewrite !nth_cat !size_rep ![X in (_ < X)%nat]bin_of_natK !r0.
    rewrite !nth_rep ?bin_of_natK //.
    rewrite -succ_nat prednK // N.mod_same // andbF andbT orFb.
    rewrite kwp // subnpn // {T}.
    set T := N.testbit (nth _ _ _) _.
    case: T.
     rewrite testbit_N_of_word // nth_rev ?size_tuple // rev_rev_ord //.
     rewrite eqxx GRing.mulr1n mxE.
     case: (splitP _) => [[][]// ? /= -> /=|l L].
      have: tval a != [::].
       apply/negP => /eqP /(f_equal size).
       rewrite size_tuple /=.
       by case: w w0.
      case: (tval a) => []//[]//[|[]//] *.
       rewrite mxE GRing.mulr1n /=.
       by apply/val_inj.
      rewrite mxE GRing.mulr1n /=.
      by apply/val_inj.
     rewrite /= add1n in L.
     rewrite mxE break_if -L.
     have->: i = Ordinal wi :> nat by [].
     by rewrite -!tnth_nth.
    by rewrite /= GRing.mulr0n mxE.
  have Svn : (N.succ (index v) < n)%nat.
   move/negP/negP: nn.
   rewrite -ltnNge prednK // => nn.
   rewrite ltnNge leq_eqVlt; apply/negP.
   case/orP => [/eqP /(f_equal bin_of_nat) nS|].
    rewrite nat_of_binK in nS.
    by rewrite /= -nS N.mod_same // subn0 ltnn in nn.
   rewrite -bin_succ ltnS leqNgt.
   by case: (v) => // ? ? /= ->.
  have nvn0: (N.succ (index v) mod bin_of_nat n > 0)%nat.
   by apply/mod_pos/andP.
  rewrite nth_take; last first.
   rewrite -[n]prednK //= subSn // subnS subKn //.
   case: (nat_of_bin (N.succ (index v) mod bin_of_nat n)) nvn0 => //.
  have->: (w - (row_ind i).+1)%nat = rev_ord (Ordinal wi) by rewrite /= modn_small.
  rewrite nth_word_of_N.
  rewrite nth_set_nth -[X in (_ - (X - _))%nat]prednK //.
  rewrite /= subSn // subnS subKn //.
  rewrite N.mod_small; last first.
   move/ltP': Svn.
   by rewrite nat_of_binK.
  rewrite -bin_succ eqnnS nth_set_nth.
  rewrite /= eqxx
          ?(N.lxor_spec, N.div2_spec, N.shiftr_spec, N.lor_spec, N.land_spec);
          last first.
   by apply N.le_0_l.
  rewrite !if_xorb //.
  rewrite modnMDl modn_small // divnMDl // divn_small // addn0.
  rewrite -!GRing.addrA; congr (_ + _).
   congr (if _ then _ else _).
   rewrite nth_cat size_drop vn prednK //.
   case: ifP => H.
    rewrite nth_drop N.mod_small; last first.
     suff/ltP': (nat_of_bin (index (state v)) + (n - m) < n)%nat
      by rewrite /= -bin_of_add_nat -bin_of_sub_nat nat_of_binK.
     rewrite addnBA; last by apply/ltnW.
     rewrite leqNgt ltnS /leq subnBA in H; last by apply/ltnW.
     rewrite addnC addnBA in H; last by apply/ltnW; case: (v).
     rewrite subnAC addnK subn_eq0 -ltnNge in H.
     rewrite addnC -subnBA; last by apply/ltnW.
     rewrite ltnNge /leq in H.
     case: (m - index v)%nat H => // ? _.
     case: n n0 => // ? _.
     by rewrite subSS ltnS leq_subr.
    by rewrite bin_of_sub_nat nat_of_add_bin bin_of_natK.
   rewrite nth_take; last first.
    rewrite subnBA; last by apply/ltnW; case: (v).
    rewrite addnC addnBA; last by apply/ltnW.
    rewrite subnAC addnK.
    move/negP/negP: H.
    case: (nat_of_bin (index v)) => [|? _].
     rewrite subn0.
     case: n n0 => // n' _.
     case: m m0 => // m' _.
     by rewrite subSS ltnS leq_subr.
    case: m m0 => // m' _.
    by rewrite subSS ltnS leq_subr.
   rewrite subnBA; last by apply/ltnW; case: (v).
   rewrite addnC addnBA; last by apply/ltnW.
   rewrite subnAC addnK.
   rewrite -[index v]nat_of_binK.
   rewrite bin_of_sub_nat bin_of_add_nat.
   rewrite addnBA; last by apply/ltnW.
   rewrite addnC -addnBA; last first.
    rewrite leqNgt.
    apply/negP => C.
    rewrite ltn_sub2l // in H.
    by case: (v).
   rewrite -bin_of_add_nat.
   rewrite N.add_mod // N.mod_same // N.add_0_l N.mod_mod //.
   rewrite N.mod_small; last first.
    apply/ltP'/leq_ltn_trans.
     apply (leq_subr m).
    by case: (v).
   by rewrite !bin_of_natK.
  congr (_ + _).
   case: (splitP _).
    case => [][]//= ? ->.
    rewrite subn1 N.add_1_r -succ_nat prednK //.
    have ww: (bin_of_nat w) = [Num of bin_of_nat w] by rewrite bin_of_natK.
    rewrite [X in N.testbit (upper_mask _) X]ww
               [X in N.testbit (lower_mask _) X]ww
               !N_of_word_last ?bin_of_natK //.
     by rewrite !andbF mxE.
   move=> k K.
   rewrite !(mxE, castmxE).
   case: (splitP _) => l L.
    rewrite !(mxE, castmxE).
    rewrite (nth_map 0%N) ?size_rev ?size_rot ?vn //.
    rewrite nth_rev size_rot vn // nth_rev size_tuple //.
    set T := (row_ind _)%nat.
    have->: (w - T.+1)%nat = rev_ord T by [].
    rewrite nth_word_of_N.
    rewrite nth_cat size_drop vn.
    rewrite /= addnA subnK // divnMDl // divn_small; last first.
     by apply/leq_trans/(leq_subr r).
    rewrite addn0 prednK // subnn ltnNge leqn0 subn_eq0 -ltnNge.
    have->: (index v < n)%nat by case v.
    rewrite nth_drop /= addn0 modnMDl modn_small; last first.
     by apply/leq_trans/(leq_subr r).
    rewrite /= add1n in K.
    rewrite -L /= -K N.add_1_r -succ_nat -subSn // subSS.
    rewrite !testbit_N_of_word ?bin_of_natK ?K //.
    rewrite nth_cat size_rep.
    have wkr: (w - k.+1 < bin_of_nat r)%nat = false.
     rewrite /= in K, L.
     rewrite L bin_of_natK ltnNge.
     apply/negP/negP.
     apply/leq_trans/(_ : w - (w - r) <= _)%nat.
      by rewrite subnBA // addnC addnK.
     by rewrite leq_sub2l.
    rewrite wkr nth_rep ?bin_of_natK; last by rewrite ltn_sub2r.
    rewrite eqxx nth_cat size_rep wkr nth_rep ?bin_of_natK; last by rewrite ltn_sub2r.
    by rewrite andbF orbF andbT.
   rewrite !(mxE, castmxE).
   rewrite (nth_map 0%N) ?size_rev ?size_rot ?vn //.
   rewrite nth_rev size_rot vn // nth_rev size_tuple //.
   set T := (row_ind _)%nat.
   have->: (w - T.+1)%nat = rev_ord T by [].
   rewrite nth_word_of_N.
   rewrite nth_cat size_drop vn.
   rewrite /= in K, L.
   rewrite /= addnBAC // -subnBA; last by apply/ltnW.
   rewrite divnMBl // divn_small; last by apply/leq_trans/rw/leq_subr.
   rewrite /dvdn modn_small; last by apply/leq_trans/rw/leq_subr.
   rewrite subn_eq0 -ltnNge ltn_ord subn1 subn0 prednK //.
   have ->: (n - n.-1 = 1)%nat
    by rewrite -[X in (X - _)%nat]prednK // subSn // subnn.
   have vnp : (index v < n.-1)%nat.
    move/ltP': Svn.
    rewrite /= -bin_succ => /ltP'.
    by rewrite -[n]prednK // ltnS /=.
   rewrite -[X in (1 < X - _)%nat]prednK // subSn ?(ltnW vnp) // ltnS ltnNge.
   rewrite leqn0 subn_eq0 -ltnNge vnp nth_drop.
   rewrite wnwrw !subnS N.add_1_r -succ_nat prednK; last by rewrite ltnNge leqn0 subn_eq0 -ltnNge.
   rewrite addn1 /= K L add1n !subnS.
   rewrite addnBAC // -subnBA; last by apply/ltnW.
   rewrite subKn; last by apply/leq_trans/rw/leqW/leq_subr.
   have rlprl: ((r - l).-1 < r - l)%nat.
    have: (r - l != 0)%nat by rewrite subn_eq0 -ltnNge.
    by case: (r - l)%nat.
   have rlw: ((r - l).-1 < w)%nat
    by apply/(leq_trans rlprl)/leq_trans/rw/leqW/leq_subr.
   rewrite !testbit_N_of_word ?bin_of_natK //.
   rewrite !nth_cat !size_rep ![X in (_ < X)%nat]bin_of_natK.
   rewrite (leq_trans rlprl (leq_subr _ _))
           !nth_rep ?bin_of_natK ?(leq_trans rlprl (leq_subr _ _)) //.
   by rewrite andbF andbT.
  case: (splitP _) => k K.
   rewrite /= in K.
   have C: (w - r <= w.-1)%nat by rewrite -subn1 leq_sub2l.
   by rewrite leqNgt K ltn_ord in C.
  rewrite !(mxE, castmxE).
  rewrite (nth_map 0%N) ?size_rev ?size_rot ?vn //.
  rewrite nth_rev size_rot vn // nth_rev size_tuple //.
  set T := (row_ind _)%nat.
  have->: (w - T.+1)%nat = rev_ord T by [].
  rewrite nth_word_of_N nth_cat size_drop vn.
  rewrite /= addnBAC // -subnBA; last by apply/ltnW.
  rewrite divnMBl // divn_small; last by apply/leq_trans/rw/leq_subr.
  rewrite /dvdn modn_small; last by apply/leq_trans/rw/leq_subr.
  rewrite subn_eq0 -ltnNge ltn_ord subn1 subn0 prednK //.
  have ->: (n - n.-1 = 1)%nat
   by rewrite -[X in (X - _)%nat]prednK // subSn // subnn.
  have vnp : (index v < n.-1)%nat.
   move/ltP': Svn.
   rewrite /= -bin_succ => /ltP'.
   by rewrite -[n]prednK // ltnS /=.
  rewrite -[X in (1 < X - _)%nat]prednK // subSn ?(ltnW vnp) // ltnS ltnNge.
  rewrite leqn0 subn_eq0 -ltnNge vnp nth_drop.
  rewrite wnwrw addn1 /= kwp // subnpn //.
  have->: (0 = bin_of_nat 0%nat)%N by [].
  rewrite !testbit_N_of_word ?bin_of_natK //.
  rewrite !nth_cat !size_rep ![X in (_ < X)%nat]bin_of_natK !r0.
  rewrite !nth_rep ?bin_of_natK //.
  rewrite andbF andbT orFb {T}.
  set T := N.testbit _ (bin_of_nat 0).
  case: T.
   rewrite testbit_N_of_word // nth_rev ?size_tuple // rev_rev_ord //.
   rewrite eqxx GRing.mulr1n mxE.
   case: (splitP _) => [[][]// ? /= -> /=|l L].
    have: tval a != [::].
     apply/negP => /eqP /(f_equal size).
     rewrite size_tuple /=.
     by case: w w0.
    case: (tval a) => []//[]//[|[]//] *.
      rewrite mxE GRing.mulr1n /=.
      by apply/val_inj.
     rewrite mxE GRing.mulr1n /=.
     by apply/val_inj.
    rewrite /= add1n in L.
    rewrite mxE break_if -L.
    have->: i = Ordinal wi :> nat by [].
    by rewrite -!tnth_nth.
   by rewrite /= GRing.mulr0n mxE.
* rewrite computeBE_large // !mxE ?castmxE ?mxE (nth_map 0%N)
          ?nth_rev ?size_tuple ?size_rev ?size_rot ?ltn_pmod
          ?size_next_random_state' //.
  have->: (w - (row_ind i).+1)%nat = rev_ord (row_ind i) by [].
  have->: (w - (row_ind (Ordinal (iw i))).+1)%nat = rev_ord (row_ind (Ordinal (iw i))) by [].
  rewrite !nth_word_of_N; congr (if _ then _ else _).
  rewrite /= -[X in rot (N.succ (index v) mod bin_of_nat X) _]nvn rot_succ;
   last by apply/ltnW; rewrite nvn; case: (v).
  rewrite nth_cat size_drop size_rot nvn.
  rewrite ltn_sub2l //; last by rewrite ltnS divn_large //.
  rewrite nth_drop subnS add1n divnB // divnn modnn w0 ltn0 subn1 subn0.
  rewrite prednK // prednK ?divn_large // vn.
  rewrite !nth_cat !size_drop !nvn !vn.
  case: ifP => ninv.
   rewrite !nth_drop nth_set_nth /=.
   rewrite nth_set_nth /=.
   set T := _ == nat_of_bin (index v).
   have Tf: T = false.
    apply/negP => /eqP /(f_equal bin_of_nat).
    rewrite !nat_of_binK -N.add_1_r.
    apply/eqP/negP.
    rewrite lem2 //.
    by rewrite N.mod_1_l; move/ltP': n1.
   rewrite Tf nth_set_nth /=.
   case: ifP => H.
    rewrite N.land_spec -(eqP H).
    rewrite modnB // modnn ltn0 mul0n add0n subn0.
    have->: (w - (i %% w).+1)%nat = rev_ord (Ordinal (ltn_pmod i w0)) by [].
    rewrite testbit_N_of_word ?bin_of_natK // nth_cat size_rep.
    case: ifP => C; last by rewrite nth_rep ?andbT // ltn_sub2r ?bin_of_natK.
    rewrite /= bin_of_natK in C.
    have C' : (w - r <= i %% w)%nat.
     rewrite /leq subnS prednK in C; last by rewrite ?ltnNge ?leqn0 ?subn_eq0 leqNgt ?ltn_pmod.
     by rewrite /leq subnAC C.
    have Svn: (N.succ (index v) < n)%nat.
     rewrite -bin_succ ltn_neqAle.
     apply/andP; split; last by case v.
     apply/negP => /eqP vn'.
     rewrite bin_succ in vn'.
     rewrite -[N.succ _]nat_of_binK vn' N.mod_same // addn_eq0 in H.
     case/andP: H => /eqP v0.
     rewrite -bin_succ in vn'.
     move: v0 vn' => -> + _.
     by case: n n1 => []//[].
    rewrite N.mod_small in H; last first.
     move/ltP': Svn.
     by rewrite nat_of_binK.
    rewrite -bin_succ -addn1 eqn_add2l in H.
    have iwn: (i %/ w = n.-1)%nat.
     by rewrite -subn1 -(eqP H) subKn // ltnW // col_ind_prf.
    have: (i < p)%nat by [].
    rewrite (divn_eq i w) iwn => ip.
    have nwwr: (n.-1 * w + (w - r) <= n.-1 * w + i %% w)%nat by rewrite leq_add2l.
    move: (leq_ltn_trans nwwr ip).
    by rewrite addnBA // addnC -mulSn prednK // ltnn.
   rewrite -[X in _ == X]addn0 eqn_add2l subn_eq0 leqNgt col_ind_prf /=.
   by rewrite modnB // modnn ltn0 mul0n add0n subn0.
  have niwnv : (n - i %/ w - (n - index v) < index v)%nat.
   rewrite subnBA; last by apply/ltnW; case v.
   rewrite addnC addnBA; last by apply/ltnW/col_ind_prf.
   rewrite subnAC addnK.
   case: (nat_of_bin (index (state v))) ninv.
    rewrite subn0.
    move: (divn_large w0 wi).
    case: n (i %/ w)%nat n0 => // ? []// ? _ _.
    by rewrite subSS ltnS leq_subr.
   move: (divn_large w0 wi).
   case: (i %/ w)%nat => // ? _ *.
   by rewrite subSS ltnS leq_subr.
  rewrite !nth_take // subnBA; last by apply/ltnW; case v.
  rewrite addnC addnBA; last by apply/ltnW/col_ind_prf.
  rewrite subnAC addnK modnB // modnn ltn0 mul0n add0n subn0.
  rewrite !nth_set_nth /=.
  set T := _ == nat_of_bin (index v).
  have Tf: T = false.
   apply/negP => /eqP /(f_equal bin_of_nat).
   rewrite !nat_of_binK -N.add_1_r.
   apply/eqP/negP.
   rewrite lem2 //.
   by rewrite N.mod_1_l; move/ltP': n1.
  rewrite Tf !nth_set_nth /=.
  case: ifP => H.
   rewrite N.land_spec -(eqP H).
   have->: (w - (i %% w).+1)%nat = rev_ord (Ordinal (ltn_pmod i w0)) by [].
   rewrite testbit_N_of_word ?bin_of_natK // nth_cat size_rep.
   case: ifP => C; last first.
    rewrite nth_rep; last
     by rewrite ltn_sub2r //; apply/ltP'; rewrite !nat_of_binK; apply/ltP'.
    by rewrite andbT.
   rewrite /= bin_of_natK in C.
   have C' : (w - r <= i %% w)%nat.
    rewrite /leq subnS prednK in C; last by rewrite ?ltnNge ?leqn0 ?subn_eq0 leqNgt ?ltn_pmod.
    by rewrite /leq subnAC C.
   case Svn: (N.succ (index v) < n)%nat.
    rewrite N.mod_small in H; last first.
     move/ltP': Svn.
     by rewrite nat_of_binK.
    rewrite -bin_succ in H.
    have: (index v - i %/ w <= index v)%nat.
     case: (nat_of_bin (index (state v))) ninv => //.
      move: (divn_large w0 wi).
      case: (i %/ w)%nat => // *.
      by rewrite subSS leqW // leq_subr.
    by rewrite (eqP H) ltnn.
   move/negP/negP: Svn.
   rewrite -leqNgt leq_eqVlt -bin_succ.
   case/orP; last first.
    rewrite ltnNge.
    by case: (v) => ?? /= ->.
   move=> /eqP nv.
   rewrite bin_succ in nv.
   rewrite -[N.succ _]nat_of_binK -nv N.mod_same // subn_eq0 leq_eqVlt in H.
   case/orP: H => H; last first.
    rewrite ltn_sub2l // in ninv.
    by case v.
   rewrite -bin_succ -[n]prednK // in nv; case: nv => nv.
   rewrite -nv in H.
   have: (i < p)%nat by [].
   rewrite (divn_eq i w) -(eqP H) => ip.
   have nwwr: (n.-1 * w + (w - r) <= n.-1 * w + i %% w)%nat by rewrite leq_add2l.
   move: (leq_ltn_trans nwwr ip).
   by rewrite addnBA // addnC -mulSn prednK // ltnn.
  case: ifP => C //.
  suff: (index v < index v)%nat by rewrite ltnn.
  rewrite -[X in (X < _)%nat](eqP C).
  case: (nat_of_bin (index (state v))) ninv.
   rewrite subn0.
   move: (divn_large w0 wi).
   case: n (i %/ w)%nat n0 => // ? []// ? _ _.
   by rewrite subSS ltnS leq_subr.
  move: (divn_large w0 wi).
  case: (i %/ w)%nat => // ? _ *.
  by rewrite subSS ltnS leq_subr.
Qed.

Definition upto_rot_eq v1 v2 :=
  rot (index v1) (state_vector v1) == rot (index v2) (state_vector v2).

Lemma pres_eq v1 v2 :
(vector (array_of_state v1) == vector (array_of_state v2)) = upto_rot_eq v1 v2.
Proof.
  apply/eqP; case: ifP.
* move=> H.
  congr ia.
  apply/eqP.
  rewrite eqE /=.
  apply/eqP.
  apply/matrixP => i j.
  rewrite !mxE.
  rewrite !(nth_map 0%N) ?size_rev ?size_rot.
  by rewrite (eqP H).
  case: (v2) => state0 i0 i1 i2 i3.
  by rewrite (eqP i0).
  case: (v1) => state0 i0 i1 i2 i3.
  by rewrite (eqP i0).
* move=> H /(f_equal ai) /eqP H0.
  suff: false by [].
  rewrite -{}H.
  rewrite !incomplete_arrayK !eqE /= in H0.
  move/eqP/matrixP: H0 => H0.
  apply/eqP/(@eq_from_nth _ 0%N).
   rewrite !size_rot.
   case: (v2) => state0 i0 i1 i2 i3.
   rewrite (eqP i0).
   case: (v1) => state1 i i4 i5 i6.
   by rewrite (eqP i).
  move=> i isr.
  have ni : (i < n)%nat.
   case: (v1) isr => state0 i0 i1 i2 i3.
   by rewrite size_rot (eqP i0).
  rewrite -[LHS](word_of_NK w0); last first.
   case: v1 H0 isr => state0 i0 i1 i2 i3 H0 isr.
   move/forallP: (i2) => /(_ _) /implyP i2'.
   rewrite nth_cat; case: ifP => ?.
    rewrite nth_drop /=.
    case H : (index state0 + i < size (state_vector state0))%nat.
     move: (H) => H'.
     rewrite (eqP i0) in H'.
     by rewrite (i2' (Ordinal H') H).
    by rewrite nth_default // leqNgt H.
   rewrite size_drop /=.
   case H: (i - (size (state_vector state0) - index state0) < index state0)%nat.
    rewrite nth_take //.
    case H': (i - (size (state_vector state0) - index state0) < size (state_vector state0))%nat.
     move: (H') => H''; rewrite (eqP i0) in H''.
     by rewrite (eqP i0) (i2' (Ordinal H'')) //= (eqP i0).
    by rewrite nth_default // leqNgt H'.
   by rewrite nth_default // size_take (eqP i0) i1 leqNgt -(eqP i0) H.
  rewrite -[RHS](word_of_NK w0); last first.
   case: v2 H0 isr => state0 i0 i1 i2 i3 H0 isr.
   move/forallP: (i2) => /(_ _) /implyP i2'.
   rewrite nth_cat; case: ifP => ?.
    rewrite nth_drop /=.
    case H : (index state0 + i < size (state_vector state0))%nat.
     move: (H) => H'.
     rewrite (eqP i0) in H'.
     by rewrite (i2' (Ordinal H') H).
    by rewrite nth_default // leqNgt H.
   rewrite size_drop /=.
   case H: (i - (size (state_vector state0) - index state0) < index state0)%nat.
    rewrite nth_take //.
    case H': (i - (size (state_vector state0) - index state0) < size (state_vector state0))%nat.
     move: (H') => H''; rewrite (eqP i0) in H''.
     by rewrite (eqP i0) (i2' (Ordinal H'')) //= (eqP i0).
    by rewrite nth_default // leqNgt H'.
   by rewrite nth_default // size_take (eqP i0) i1 leqNgt -(eqP i0) H.
  congr N_of_word.
  apply/eq_from_tnth => j.
  move: (H0 (rev_ord (Ordinal ni)) (rev_ord j)).
  rewrite !mxE !(nth_map 0%N) ?size_rev ?size_rot; last first.
    case: (v1) => state0 i0 i1 i2 i3.
    by rewrite (eqP i0).
   case: (v2) => state0 i0 i1 i2 i3.
   by rewrite (eqP i0).
  rewrite !nth_rev ?size_rot ?size_tuple //; last first.
    case: (v1) => state0 i0 i1 i2 i3.
    by rewrite (eqP i0).
   case: (v2) => state0 i0 i1 i2 i3.
   by rewrite (eqP i0).
  rewrite !(tnth_nth 0%R) /= -!subSn // !subSS !subKn; last by apply/ltnW.
  case: v1 H0 isr => state0 i0 i1 i2 i3 H0 isr.
  case: v2 H0 => state1 i4 i5 i6 i7 H0.
  by rewrite /= (eqP i0) (eqP i4) !subKn // ltnW.
Qed.

Lemma next_random_stateEq q x :
  array_of_state (iter q (snd \o next_random_state') x)
= iter q mulBwc (array_of_state x).
Proof.
  elim: q x => // q IH x.
  rewrite !iterS.
  move: (next_random_stateE (iter q (snd \o next_random_state') x)).
  rewrite /comp => ->.
  by rewrite IH.
Qed.

Lemma itermulBwcE q x :
  vector (iter q mulBwc x)
  = x *m (castmx (esym tecp, esym tecp) (castmx (tecp, tecp) B ^+ q)).
Proof.
  elim: q x => [x|q IH x].
   rewrite /= GRing.expr0 .
   have->: castmx (esym tecp, esym tecp) 1 = (1 : 'F_2)%:M.
    apply/matrixP => i j.
    by rewrite castmxE !mxE !eqE.
   by rewrite mulmx1.
  rewrite iterSr IH -mulmxA.
  congr (x *m _).
  rewrite GRing.exprS.
  apply/matrixP => i j.
  rewrite !(mxE, castmxE).
  apply: eq_big_cond.
   by rewrite prednK.
  move=> ? k.
  rewrite !(castmxE, mxE) /=.
  set A := cast_ord _ _.
  apply/esym.
  set B := cast_ord _ _.
  apply/esym.
  have->: A = B by apply/val_inj.
  set K := cast_ord (esym (esym tecp)) (cast_ord _ k).
  have->: K = k by apply/val_inj.
  set K1 :=  cast_ord (esym tecnw) _.
  set K2 :=  cast_ord (esym tecnw) _.
  by have->: K1 = K2 by apply/val_inj.
Qed.

Lemma eq_from_mulmx x y (A B : 'M['F_2]_(x, y)) :
  (forall z : 'rV__ , z *m A = z *m B) -> A = B.
Proof.
  move=> H; apply/matrixP => i j.
  move/matrixP: (H (delta_mx 0 i)) => /(_ ord0 j).
  rewrite !mxE (bigD1 i) //=.
  under eq_bigr => ? /negPf H0.
   rewrite mxE eqxx H0 andbF GRing.mul0r.
  over.
  move/esym.
  rewrite (bigD1 i) //=.
  under eq_bigr => ? /negPf H0.
   rewrite mxE eqxx H0 andbF GRing.mul0r.
  over.
  by rewrite !sum_f2_eq0 !GRing.addr0 !mxE !eqxx !GRing.mul1r => ->.
Qed.

Lemma cycle_next_random_state :
  irreducible_poly phi ->
  forall q, (q > 0)%nat ->
       reflect (forall x, upto_rot_eq (iter q (snd \o next_random_state') x) ((snd \o next_random_state') x))
               (2 ^ (size phi).-1 - 1 %| q - 1)%nat.
Proof.
  move=> irp q q0.
  rewrite -cycleB_dvdP //.
  apply/(iffP idP) => [H x|].
* rewrite -pres_eq next_random_stateEq.
  move: (next_random_stateE x); rewrite /comp => ->.
  by rewrite itermulBwcE (eqP H) castmxK.
* move=> H; apply/eqP/eq_from_mulmx => z.
  set x := state_of_array
             (Build_vector_with_counter (castmx (erefl, esym tecp) z) n0).
  move: (H x).
  rewrite -pres_eq next_random_stateEq.
  move: (next_random_stateE x); rewrite /comp => ->.
  rewrite !state_of_arrayK itermulBwcE => /eqP/matrixP H0.
  apply/matrixP => i j; move: (H0 i (cast_ord (esym tecp) j)) => {H0}.
  rewrite !mxE /=.
  set L := \sum_(j0 < p) _.
  have->: L = \sum_(j0 < p.-1.+1) z i j0 * (castmx (tecp, tecp) B ^+ q) j0 j.
   apply/eq_big_cond => *.
    by rewrite prednK.
   rewrite !(castmxE, mxE) /=.
   congr (z _ _ * (castmx (tecp, tecp) B ^+ q) _ _); by apply/val_inj.
  set R := \sum_(j0 < p) _.
  suff->: R = \sum_(j0 < p.-1.+1) z i j0 * castmx (tecp, tecp) B j0 j by [].
  apply/eq_big_cond => *.
   by rewrite prednK.
  rewrite 2!castmxE /=.
  congr (z _ _ * B _ _); by apply/val_inj.
Qed.
End Main.
