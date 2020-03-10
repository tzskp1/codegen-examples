From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require irreducible.
Require Import polyn.

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
apply/rowP => i.
rewrite ?(castmxE, mxE).
apply/etrans; first by apply/eq_bigr => j _; rewrite castmxE block_mxEh mxE.
set T := cast_ord _ i.
case: (splitP T) => j Tj.
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

Section phi.
Variables w n m r : nat.
Variable a : w.-tuple [fieldType of 'F_2].
Notation p := (n * w - r).
Hypothesis pm : prime (2 ^ p - 1).
Hypothesis mn : m < n.
Hypothesis m0 : 0 < m.
Hypothesis r0 : 0 < r.
Hypothesis rw : r < w.
Hypothesis p3 : p >= 3.

Lemma n2 : 2 <= n.
Proof. by case: n mn m0 => //; case: m => []//[]// ?? + _; apply ltn_trans. Qed.

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
  case: n mn m0 => []//=[|*]; first by case m.
  rewrite mulSn.
  by apply/leq_trans/leq_addr/rw'.
Qed.

Lemma tecr : r = r.-1.+1.
Proof. by case: r r0. Qed.

Lemma tecwr : w - r = (w - r).-1.+1.
Proof. by rewrite prednK // /leq subnBA ?rw' // add1n subn_eq0 rw. Qed.

Lemma tecw : (w - r).-1.+1 + r.-1.+1 = w.
Proof.
by rewrite !prednK // ?subnK ?rw' // /leq subnBA ?rw' // add1n subn_eq0 rw.
Qed.

Lemma tecnw : w + (n.-1 * w - r) = p.
Proof. by rewrite addnBA ?rnpw // -mulSn prednK ?n0. Qed.

Lemma tecpr : p + r = n * w.
Proof.
  rewrite subnK //.
  case: n mn => // ??.
  rewrite mulSn.
  by apply/leq_trans/leq_addr/ltnW.
Qed.

Lemma tecp : p = p.-1.+1.
Proof. by case: p p3. Qed.

Lemma tecn : n = n.-2.+2.
Proof. by case: n n2 => []//[]. Qed.

Hint Resolve p0 n2 n0 w0 rw' rnpw : core.
Local Open Scope ring_scope.

Definition shiftr : 'M['F_2]_w :=
  \matrix_(i, j) (1 *+ (i == j.+1 :> nat)).

Definition A := \matrix_j (\row_i a`_i *+ (j == w.-1 :> nat)) + shiftr.

Definition S :=
  castmx (etrans (addnC _ _) tecw, tecw)
  (block_mx 0                             (castmx (tecr, tecr) 1%:M)
            (castmx (tecwr, tecwr) 1%:M)                          0) *m A.

Definition UL : 'M['F_2]_(n.-1 * w - r, w) :=
\matrix_(i, j) (1 *+ ((i == j - m :> nat) && (j >= m))%nat).
Definition B :=
  (* castmx (erefl _, addnC _ _) *)
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

Lemma cycleB_dvdP :
  irreducible_poly phi ->
  forall q, (castmx (tecp, tecp) B ^+ (2 ^ q) == castmx (tecp, tecp) B)
        = (2 ^ (size phi).-1 - 1 %| 2 ^ q - 1)%nat.
Proof.
  move=> H q.
  apply/eqP; case: ifP => H0.
  * rewrite -(horner_mx_X (castmx _ _)) -GRing.rmorphX
            (divp_eq 'X^(2 ^ q) phi) GRing.rmorphD
            GRing.rmorphM /= Cayley_Hamilton GRing.mulr0 GRing.add0r.
    move/(irreducible.cycleH_dvdP pm' H q)/(_ (irreducible.pi pm' 'X)) : H0.
    rewrite irreducible.expXpE -GRing.rmorphX => /(f_equal val) /= ->.
    by rewrite modp_small // size_polyX size_char_poly prednK ltnW // ltnW.
  * move=> H1.
    suff: (2 ^ (size phi).-1 - 1 %| 2 ^ q - 1)%N by rewrite H0.
    rewrite -(horner_mx_X (castmx _ _)) -GRing.rmorphX /= in H1.
    move/(f_equal (mx_inv_horner (castmx (tecp, tecp) B))): H1.
    rewrite !horner_mxK -!phi_mxminpoly // => H1.
    by apply/(irreducible.cycleH_dvdP pm' H q)/irreducible.expand_H/eqP.
Qed.

Record array := { content :> 'rV['F_2]_p; garbage : 'rV['F_2]_r; }.

Lemma eq_array_ax :
  Equality.axiom (fun a b => (content a == content b) && (garbage a == garbage b)).
Proof.
  case=> c1 g1 [] c2 g2.
  apply/(iffP idP) => /= [|[] -> ->].
  * by case/andP => /eqP -> /eqP ->.
  * by rewrite !eqxx.
Qed.

Canonical array_eqMixin := EqMixin eq_array_ax.
Canonical array_eqType := EqType _ array_eqMixin.

Definition pull_ord (o : 'I_p) := cast_ord tecpr (lshift r o).
Definition push_ord (o : 'I_r) := cast_ord tecpr (rshift p o).

Definition incomplete_array (x : 'M['F_2]_(n, w)) : array :=
  {| content := \row_i (mxvec x) ord0 (pull_ord i);
     garbage := \row_i (mxvec x) ord0 (push_ord i); |}.

Definition array_incomplete (y : array) : 'M_(n, w) :=
  vec_mx (castmx (erefl, tecpr) (row_mx y (garbage y))).

Lemma array_incompleteK : cancel array_incomplete incomplete_array.
Proof.
case=> c g; rewrite /incomplete_array /array_incomplete.
apply/eqP; rewrite eqE /=; apply/andP; split; apply/eqP/rowP => j;
by rewrite mxE vec_mxK castmxE cast_ordK ?row_mxEl ?row_mxEr cast_ord_id.
Qed.

Lemma incomplete_arrayK : cancel incomplete_array array_incomplete.
Proof.
move=> y; rewrite /incomplete_array /array_incomplete; apply/matrixP => j k.
rewrite ?(mxE, castmxE) /=.
set T := cast_ord _ _.
case: (splitP T) => j0 /= j0H.
* have j1: (nat_of_ord (enum_rank (j, k)) < p)%nat by rewrite j0H.
  have<-: Ordinal j1 = j0 by apply/val_inj.
  rewrite ?(mxE, castmxE).
  set S := cast_ord _ _; have->: S = enum_rank (j, k) by apply/val_inj.
  by rewrite !enum_rankK.
* have j1: (nat_of_ord (enum_rank (j, k)) - p < r)%nat by rewrite j0H addnC addnK.
  have<-: Ordinal j1 = j0 by apply/val_inj; rewrite /= j0H addnC addnK.
  rewrite ?(mxE, castmxE).
  set S := cast_ord _ _; have->: S = enum_rank (j, k).
    by apply/val_inj; rewrite /= addnC subnK // j0H leq_addr.
  by rewrite !enum_rankK.
Qed.

Lemma size_ord_enum q : size (ord_enum q) = q.
Proof. by rewrite -(size_map val) val_ord_enum size_iota. Qed.

Lemma nth_ord_enum i (q : nat) k : (i < q)%nat -> val (nth k (ord_enum q) i) = i.
Proof.
move=> iq.
by rewrite -(nth_map k (val k) val) ?val_ord_enum ?nth_iota // size_ord_enum.
Qed.

Lemma eq_big_cond (T : ringType) p q (F1 : 'I_p -> T) (F2 : 'I_q -> T) :
  forall (pq : p = q), (forall i, F1 (cast_ord (esym pq) i) = F2 i) ->
  \sum_(j < p) F1 j = \sum_(i < q) F2 i.
Proof.
move=> pq F12.
case p0: (p > 0)%nat; last first.
 case: p p0 pq F1 F2 F12 => //= _.
 case: q => // *.
 by rewrite !big_ord0.
have dq: 'I_q.
 rewrite -pq.
 case: p p0 {F1 F12 pq} => // *.
 by apply ord0.
apply/etrans; last first.
 apply congr_big => [|//|].
 apply: (_ : map (cast_ord pq) (index_enum (ordinal_finType p)) = _).
  apply/eq_from_nth.
  by rewrite size_map /index_enum !unlock /= -!(size_map val) !val_ord_enum !size_iota.
 rewrite size_map /index_enum !unlock /= size_ord_enum => i Hi.
 apply: (_ : nth dq [seq cast_ord pq i | i <- ord_enum p] i = nth dq (ord_enum q) i).
 apply/val_inj.
 rewrite (nth_map (cast_ord (esym pq) dq)).
 rewrite /= !nth_ord_enum //.
by rewrite -pq.
by rewrite size_ord_enum.
move=> i _.
by rewrite -F12.
rewrite big_map.
apply eq_bigr => i _.
rewrite -F12.
congr (F1 _).
by apply/val_inj.
Qed.

Lemma mulBE (x : 'rV['F_2]_p) :
let x' := castmx (erefl, etrans (esym tecnw) (addnC _ _)) x in
x *m B = castmx (erefl, tecnw)
        (row_mx (lsubmx x' *m (\matrix_(i, j) (1 *+ ((i == j - m :> nat) && (j >= m))%nat))
               + rsubmx x' *m S) (lsubmx x')).
Proof.
move=> x'.
apply: (can_inj (castmxK (esym erefl) (esym tecnw))).
apply: (can_inj (castmxK erefl (addnC w (n.-1 * w - r)%N))).
rewrite !castmxK -mulBE_hidden castmx_comp /=; subst x'.
apply: (can_inj (castmxK (esym erefl) (esym (etrans (esym tecnw) (addnC w (n.-1 * w - r)%N))))).
rewrite castmxK.
apply/rowP => k.
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

Definition significant (x : 'M['F_2]_(n, w)) :=
  \row_i x (Ordinal n0) i *m pid_mx (w - r) *m A +
  \row_i x (Ordinal (@ltn_pmod m n n0)) i +
  \row_i x (Ordinal (@ltn_pmod 1 n n0)) i *m copid_mx r *m A.

Definition shift_array (x : 'M['F_2]_(n, w)) : 'M['F_2]_(n, w) :=
  \matrix_(k, i) x (Ordinal (@ltn_pmod k.+1 n n0)) i.

Definition mapB (x : 'M['F_2]_(n, w)) :=
  \matrix_(k, i) (shift_array x k i *+ (k != cast_ord (esym tecn) (lift ord0 (@ord_max n.-2)))
  + significant x ord0 i *+ (k == cast_ord (esym tecn) (lift ord0 (@ord_max n.-2)))).

Lemma eq_from_garbage g (y z : 'rV['F_2]_p) :
  {|content:=y; garbage:=g|} = {|content:=z; garbage:=g|} -> y = z.
Proof. by case. Qed.

(* Lemma mapBE x : *)
(*    (content \o incomplete_array \o mapB \o array_incomplete) x = x *m B. *)
(* Proof. *)
(*   apply (@eq_from_garbage ((garbage \o incomplete_array \o mapB \o array_incomplete) x)). *)
(*   apply (can_inj array_incompleteK). *)
(*   rewrite incomplete_arrayK. *)
(*   apply/matrixP => s t. *)
(*   rewrite ?(mxE, castmxE). *)
(*   case sn: (s == cast_ord (esym tecn) (lift ord0 ord_max)). *)
(*    rewrite -GRing.mulr_natl GRing.mul1r /=. *)
(*    rewrite -GRing.mulr_natl GRing.mul0r GRing.add0r. *)
(*    set T := cast_ord _ _. *)
(*    set S := cast_ord (esym _) _. *)
(*    case: (splitP S) => j Sj. *)
(*     rewrite /B /=. *)
(*     case: (splitP T) => k Tk. *)
(*      rewrite ?(mxE, castmxE). *)
(*      apply/etrans; last first. *)
(*       apply/eq_bigr => l _. *)
(*       by rewrite ?(castmxE, mxE). *)
(*      rewrite /=. *)
(*    have: (nat_of_ord S < p)%nat. *)
(*     rewrite /S /= (eqP sn). *)
(*     case: t {S T} => // t. *)
End phi.
