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
End nat_word.