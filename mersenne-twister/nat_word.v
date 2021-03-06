From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
Require Import BinNat BinPos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope N_scope.

Section nat_word.
Variable w : nat.
Variable w0 : (w > 0)%nat.

Definition N_of_word (t : w.-tuple 'F_2) :=
  foldr (fun x y => 2*y + x) 0
        (map_tuple (fun x => if (x == 1 :> 'F_2)%R then 1%N else 0) t).

Fixpoint word_of_N_iter (fuel : nat) (p : positive) : seq 'F_2 :=
  match fuel, p with
  | f.+1, xI p0 => 1%R :: word_of_N_iter f p0
  | f.+1, xO p0 => 0%R :: word_of_N_iter f p0
  | f.+1, xH => 1%R :: map (fun _ => 0%R) (iota 0 f)
  | 0%nat, _ => [::]
  end.

Definition zero_size : size (map (fun _ => (0%R : 'F_2)) (iota 0 w)) == w.
Proof. by rewrite size_map size_iota. Qed.
Definition zero := Tuple zero_size.

Lemma word_of_N_iter0 p : size (word_of_N_iter 0 p) == 0.
Proof. by []. Qed.

Lemma size_word_of_N_iter p : size (word_of_N_iter w p) == w.
Proof.
  elim: w p => // w' IH p.
  case: p => [p|p|].
    by rewrite /= (eqP (IH _)).
   by rewrite /= (eqP (IH _)).
  by rewrite /= size_map size_iota.
Defined.

Definition word_of_N (n' : N) :=
  match n' with
  | N0 => zero
  | N.pos p => Tuple (size_word_of_N_iter p)
  end.

Lemma word_of_N0 d (i : 'I_w) : nth d (word_of_N 0) i = 0%R.
Proof.
  case: i => //= i iw.
  by rewrite nth_map // size_iota.
Qed.

Lemma bin_of_add_nat n1 n2 :
  bin_of_nat n1 + bin_of_nat n2 = bin_of_nat (n1 + n2)%nat.
Proof.
  apply: (can_inj nat_of_binK).
  by rewrite bin_of_natK nat_of_add_bin !bin_of_natK.
Qed.

Lemma succ_nat i : bin_of_nat i.+1 = N.succ (bin_of_nat i).
Proof.
  elim: i => // i IH.
  by rewrite -addn1 -bin_of_add_nat IH N.add_1_r.
Qed.

Lemma bin_succ y :
(nat_of_bin y).+1 = nat_of_bin (N.succ y).
Proof.
case: y => //.
elim => //= ? <-.
by rewrite !natTrecE -[in RHS]addn1 -[in RHS]muln2 mulnDl mul1n muln2 addn2.
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

Lemma bin_of_sub_nat x y : (bin_of_nat x - bin_of_nat y) = bin_of_nat (x - y)%nat.
Proof.
  by rewrite -[y]bin_of_natK -[x]bin_of_natK nat_of_sub_bin !nat_of_binK.
Qed.

Lemma Num_succ i : [Num of i] + 1 = [Num of i.+1].
Proof. by rewrite N.add_1_r succ_nat. Qed.

Lemma pos_Num i : 0 <= [Num of i].
Proof. by case: i. Qed.

Lemma nat_of_pos_pred i : (nat_of_pos i).-1 = nat_of_bin (Pos.pred_N i).
Proof.
  elim: i => // i IH; rewrite /= natTrecE.
  case: i IH => //= p; rewrite /= ?natTrecE // => <-.
  rewrite -!subn1 doubleB subn2 subn1 prednK //.
  have: (nat_of_pos p > 0)%nat.
   elim: p => //= p IH.
   rewrite natTrecE.
   by case: (nat_of_pos p) IH.
  by case: (nat_of_pos p).
Qed.

Lemma pos_of_nat_pred_succ i : Pos.pred_N (pos_of_nat i i) = bin_of_nat i.
Proof.
  apply: (can_inj nat_of_binK).
  rewrite bin_of_natK -nat_of_pos_pred.
  have->: nat_of_pos (pos_of_nat i i) = nat_of_bin (bin_of_nat i.+1) by [].
  by rewrite bin_of_natK.
Qed.

Lemma nth_word_of_N x d (i : 'I_w) :
  nth d (word_of_N x) i =
  if N.testbit x [Num of (val i)]
  then 1%R : 'F_2 else 0%R.
Proof.
case: x; first by rewrite word_of_N0.
rewrite /word_of_N => p.
rewrite -tnth_nth (tnth_nth 0%R).
have->: tval (Tuple (size_word_of_N_iter p)) = word_of_N_iter w p by [].
elim: w i p => [[][]//|] w' IH i p.
case: p => [p|p|].
+ case: i => [][]//= i; rewrite ltnS => i0.
  by move: (IH (Ordinal i0) p) ->; rewrite pos_of_nat_pred_succ.
+ case: i => [][]//= i; rewrite ltnS => i0.
  by move: (IH (Ordinal i0) p) ->; rewrite pos_of_nat_pred_succ.
+ case: i => [][]//= i _.
  case iw': (i < w')%nat.
   by rewrite nth_map // size_iota.
  by rewrite nth_default // size_map size_iota leqNgt iw'.
Qed.

Hint Resolve pos_Num : core.

Lemma N_of_wordK : cancel N_of_word word_of_N.
Proof.
  move=> x; apply/eq_from_tnth => j.
  rewrite (tnth_nth 0%R) nth_word_of_N /N_of_word.
  set T := (fun x0 y : N => 2 * y + x0).
  case: x j => x xH [] i iH.
  rewrite (tnth_nth 0%R) /= => {xH iH}.
  elim: x i => [?|x0 x IH i].
   by rewrite nth_default.
  case: i => [|i].
   case: x0 => [][|[]]//= i.
    rewrite /T /= N.add_0_r N.testbit_even_0.
    by apply/val_inj.
   rewrite /T /= N.testbit_odd_0.
   by apply/val_inj.
  rewrite succ_nat /= N.testbit_succ_r_div2.
  have->: (N.div2 (T (if x0 == 1%R then 1 else 0)
                  (foldr T 0 [seq (if x1 == 1%R then 1 else 0) | x1 <- x])))
        = (foldr T 0 [seq (if x1 == 1%R then 1 else 0) | x1 <- x]).
   rewrite /T.
   case: (x0 == 1%R).
    by rewrite -N.succ_double_spec N.div2_succ_double.
   by rewrite N.add_0_r -N.double_spec N.div2_double.
  rewrite IH //.
  by elim: i.
Qed.

Lemma N_of_word_last v : N.testbit (N_of_word v) [Num of w] = false.
Proof.
  case: v => v i; rewrite /N_of_word; set T := [Num of w].
  have-> /=: T = [Num of (size v)] by rewrite (eqP i).
  have: (size v > 0)%nat by rewrite (eqP i).
  elim: v {i T} => // ? l IHl _.
  case l0: (size l).
   rewrite /= l0.
   move/size0nil:l0 => -> /=.
   by case: ifP.
  rewrite succ_nat /=.
  case: ifP.
   rewrite N.testbit_odd_succ ?IHl -/size ?l0 //.
  by rewrite N.add_0_r N.testbit_even_succ ?IHl -/size ?l0 //.
Qed.

Definition N_of_vector (x : 'rV['F_2]_w) := N_of_word (mktuple (x ord0)).
Definition vector_of_N n := (\row_i (tnth (word_of_N n) i))%R.

Lemma N_of_vectorK : cancel N_of_vector vector_of_N.
Proof.
  move=> x.
  rewrite /N_of_vector /vector_of_N N_of_wordK.
  apply/rowP => i.
  by rewrite mxE tnth_mktuple.
Qed.

Fixpoint rep T (n : nat) (v : T) :=
  match n with
  | n'.+1 =>
    v :: rep n' v
  | 0%nat => [::]
  end.

Lemma nth_rep T (v d: T) (n i : nat) : (i < n)%nat ->  nth d (rep n v) i = v.
Proof. by elim: n i => // n IH []. Qed.

Lemma size_rep T (v: T) n : size (rep n v) = n.
Proof. by elim: n => //= + ->. Qed.

Lemma size_rep_cat T (v v': T) r :
  (r <= w)%nat -> size (rep r v ++ rep (w - r) v') == w.
Proof. move=> *; by rewrite size_cat !size_rep addnC subnK. Qed.

Definition make_upper_mask r (rw : (r <= w)%nat) :=
  Tuple (@size_rep_cat _ (0%R: 'F_2) (1%R: 'F_2) r rw).

Definition make_lower_mask r (rw : (r <= w)%nat) :=
  Tuple (@size_rep_cat _ (1%R: 'F_2) (0%R: 'F_2) r rw).

Local Lemma lem (n : nat) :
  foldr (fun x y => 2*y + x)%N 0
  [seq (if x == (1 : 'F_2)%R then 1 else 0) | x <- [seq 0%R | _ <- iota 0 n]] = 0.
Proof.
  elim: n => // n IH.
  by rewrite -[n.+1]addn1 iota_add !map_cat foldr_cat /= IH.
Qed.

Lemma N_of_word_zero : N_of_word zero = 0.
Proof. by rewrite /N_of_word /zero /= lem. Qed.

Lemma posxO p : N.pos (xO p) = 2 * N.pos p.
Proof. by elim: p. Qed.

Lemma posxI p : N.pos (xI p) = 2 * N.pos p + 1.
Proof. by elim: p. Qed.

Lemma word_of_NK (x : N) :
(x <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))))%nat ->
N_of_word (word_of_N x) = x.
Proof.
  case: x => [|p] /=.
   by rewrite N_of_word_zero.
  rewrite /N_of_word /=.
  elim: w w0 p => // w' IH _ []//= => [| | *]; last by rewrite lem N.add_0_l.
  + move=> p H.
    rewrite !natTrecE nat_of_add_bin addn1 ltnS in H.
    case w'0: (0 < w')%nat.
     rewrite IH // -leq_double.
     apply/(leq_trans H).
     case: (foldr _ _ _) => // ?.
     by rewrite posxO /= natTrecE.
    case: w' w'0 H {IH} => //= _ H.
    suff: false by [].
    rewrite leqNgt in H.
    move/negPf: H <-.
    elim: p => // p H.
    apply/(leq_trans H).
    by rewrite /= natTrecE -!addnn leq_addr.
  + move=> p H.
    rewrite !natTrecE nat_of_add_bin addn1 in H.
    case w'0: (0 < w')%nat.
     rewrite IH //.
     move: (leq_div2r 2 H).
     rewrite -muln2 mulnK // => H'.
     apply/(leq_trans H').
     rewrite -addn1 divnD //.
     set R := foldr _ _ _.
     set Q := match R with
              | _ => _
              end %% 2.
     have->: Q = 0.
      subst Q R.
      case: w' w'0 {IH H H'} => // w' _.
      rewrite /= N.add_1_r.
      case: (match foldr _ _ _ with | 0 => 0 | N.pos q => _ end) => //= ?.
      by rewrite natTrecE -muln2 modnMl.
     rewrite modn_small // add0n ltnn [1 %/ 2]divn_small // !addn0.
     case: R {Q} => //= *.
     by rewrite natTrecE -muln2 mulnK.
    case: w' w'0 H {IH} => //= _ H.
    suff: false by [].
    rewrite leqNgt in H.
    move/negPf: H <-.
    elim: p => // p H.
    apply/(leq_trans H).
    by rewrite /= natTrecE -!addnn leq_addr.
Qed.

Lemma bound_N_of_word x :
(N_of_word x <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))))%nat.
Proof.
  rewrite /N_of_word.
  elim: w x.
   by case=> []//[]//.
  move=> w' IH x.
  case: x => [][]// ? l i; move: (i) => i'.
  rewrite eqSS in i.
  apply/leq_trans.
   apply: (_ : _ <= (2 * foldr (fun x0 y : N => 2 * y + x0) 0 [seq (if x == 1%R then 1 else 0) | x <- l] + 1)%N)%nat.
    rewrite /=; case: ifP => // ?.
    rewrite N.add_0_r N.add_1_r -bin_succ.
    by apply/ltnW.
  rewrite !N.add_1_r -!bin_succ nat_of_mul_bin.
  set T := foldr _ _ _.
  set T' := foldr _ _ _.
  have->: T' = 2 * foldr (fun x0 y : N => (2 * y + x0)%N) 0%N [seq (if x == 1%R then 1 else 0) | x <- rep w' (1 : 'F_2)%R] + 1
   by [].
  rewrite N.add_1_r -bin_succ ltnS nat_of_mul_bin.
  apply/leq_mul => //.
  by apply(IH (Tuple i)).
Qed.

Definition lxor' (x y : w.-tuple 'F_2) :=
  map (fun '(x, y) => x + y)%R (zip x y).

Lemma lxor_prf x y : size (lxor' x y) == w.
Proof.
  case: x y => x X [] y /= Y.
  by rewrite size_map size_zip /= (eqP X) (eqP Y) minnn.
Qed.

Definition lxor (x y : w.-tuple 'F_2) :=
  Tuple (lxor_prf x y).

Lemma neq1 y :
  (y == 1%R :> 'F_2) = false -> y = 0%R.
Proof.
  case: y => [][|[]//] y ?.
  by apply/val_inj.
Qed.

Lemma lxorE x y :
N.lxor (N_of_word x) (N_of_word y) = N_of_word (lxor x y).
Proof.
  case: x y => x X [] y Y.
  rewrite /N_of_word /lxor /= /lxor' /=.
  elim: w w0 x y X Y => // w' IH _ []// x0 x []// y0 y.
  rewrite !eqSS.
  case w'0: (w' > 0)%nat; last first.
   rewrite lt0n in w'0.
   move/negP/negP/eqP: w'0 ->.
   case: x y => []//[]// _ _.
   rewrite /=.
   case: ifP => [/eqP H1|]; case: ifP => [/eqP H2|].
   + by rewrite /= H1 H2 /=.
   + rewrite H1 /=.
     by case: y0 => [][]//[]//=.
   + rewrite /= H2.
     by case: x0 => [][]//[]//=.
   + case: x0 => [][|[]//]//.
     by case: y0 => [][|[]//]//.
 move=> H1 H2.
 rewrite /= -(IH w'0 _ _ H1 H2).
 case: ifP => X; case: ifP => Y.
 + do! case: (foldr _ _ _) => //=.
   - by rewrite (eqP X) (eqP Y).
   - move=> p.
     by rewrite (eqP X) (eqP Y).
   - move=> p.
     by rewrite (eqP X) (eqP Y).
   - move=> p p0.
     by rewrite (eqP X) (eqP Y) /= N.add_0_r.
 + do! case: (foldr _ _ _) => //=.
   - by rewrite (eqP X) (neq1 Y).
   - move=> p.
     by rewrite (eqP X) (neq1 Y).
   - move=> p.
     by rewrite (eqP X) (neq1 Y).
   - move=> p p0.
     rewrite (eqP X) (neq1 Y) /= N.add_1_r.
     by case: (Pos.lxor p0 p).
 + do! case: (foldr _ _ _) => //=.
   - by rewrite (neq1 X) (eqP Y).
   - move=> p.
     by rewrite (neq1 X) (eqP Y).
   - move=> p.
     by rewrite (neq1 X) (eqP Y).
   - move=> p p0.
     rewrite (neq1 X) (eqP Y) /= N.add_1_r.
     by case: (Pos.lxor p0 p).
 + do! case: (foldr _ _ _) => //=.
   - by rewrite (neq1 X) (neq1 Y).
   - move=> p.
     by rewrite (neq1 X) (neq1 Y).
   - move=> p.
     by rewrite (neq1 X) (neq1 Y).
   - move=> p p0.
     rewrite (neq1 X) (neq1 Y) /=.
     by case: (Pos.lxor p0 p).
Qed.

Lemma bound_lxor (x y : N) :
(x <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))))%nat ->
(y <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))))%nat ->
(N.lxor x y <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))))%nat.
Proof.
  move=> H1 H2.
  rewrite -[x]word_of_NK // -[y]word_of_NK //.
  by rewrite lxorE bound_N_of_word.
Qed.

Lemma bound_land (x y : N) :
(x <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))))%nat ->
(N.land x y <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))))%nat.
Proof.
  move=> H; apply/leq_trans/H.
  case: x {H} => // x.
  elim: x y => [x IH []// y|x IH []// y|y].
  + case: y => //[y|y].
    - move: (IH (Npos y)) => /=.
      case: (Pos.land x y) => // p.
      rewrite /= !natTrecE ltnS -!muln2 => H.
      by apply/leq_mul.
    - move: (IH (Npos y)) => /=.
      case: (Pos.land x y) => // p.
      rewrite /= !natTrecE -!muln2 => H.
      by apply/leqW/leq_mul.
  + case: y => //[y|y].
    - move: (IH (Npos y)) => /=.
      case: (Pos.land x y) => // p.
      rewrite /= !natTrecE -!muln2 => H.
      by apply/leq_mul.
    - move: (IH (Npos y)) => /=.
      case: (Pos.land x y) => // p.
      rewrite /= !natTrecE -!muln2 => H.
      by apply/leq_mul.
  + by case: y => []//[].
Qed.

Definition lor' (x y : w.-tuple 'F_2) :=
  map (fun '(x, y) => if (x == 1) || (y == 1) then 1 : 'F_2 else 0)%R (zip x y).

Lemma lor_prf x y : size (lor' x y) == w.
Proof.
  case: x y => x X [] y /= Y.
  by rewrite size_map size_zip /= (eqP X) (eqP Y) minnn.
Qed.

Definition lor (x y : w.-tuple 'F_2) :=
  Tuple (lor_prf x y).

Lemma lorE x y :
N.lor (N_of_word x) (N_of_word y) = N_of_word (lor x y).
Proof.
  case: x y => x X [] y Y.
  rewrite /N_of_word /lor /= /lor' /=.
  elim: w w0 x y X Y => // w' IH _ []// x0 x []// y0 y.
  rewrite !eqSS.
  case w'0: (w' > 0)%nat; last first.
   rewrite lt0n in w'0.
   move/negP/negP/eqP: w'0 ->.
   case: x y => []//[]// _ _.
   rewrite /=.
   by case: ifP => [/eqP H1|]; case: ifP => [/eqP H2|].
 move=> H1 H2.
 rewrite /= -(IH w'0 _ _ H1 H2).
 case: ifP => X; case: ifP => Y.
 + do! case: (foldr _ _ _) => //=.
 + do! case: (foldr _ _ _) => //=.
 + do! case: (foldr _ _ _) => //=.
 + do! case: (foldr _ _ _) => //=.
Qed.

Lemma bound_lor (x y : N) :
(x <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))))%nat ->
(y <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))))%nat ->
(N.lor x y <= N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))))%nat.
Proof.
  move=> H1 H2.
  rewrite -[x]word_of_NK // -[y]word_of_NK //.
  by rewrite lorE bound_N_of_word.
Qed.
End nat_word.
