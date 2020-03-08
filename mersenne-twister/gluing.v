From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require Import mt cycle BinNat BinPos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope N_scope.

Definition w := 32.
Definition r := 31.
Definition n := 624.
Definition m := 397.

(*
Inductive random_state_aux (y : random_state) :=
| Prf : (index y < len)%nat && (size (state_vector y) == len)
        -> random_state_aux y.
*)

Definition N_of_word (t : w.-tuple 'F_2) :=
  foldr (fun x y => 2*y + x) 0
        (map_tuple (fun x => if (x == 1 :> 'F_2)%R then 1%N else 0) t).

Definition word_of_N (n' : N) :=
  tcast (card_ord _)
        (map_tuple (fun i => if N.testbit n' [Num of (val i)]
                          then 1%R : 'F_2 else 0%R) (enum_tuple 'I_w)).

Lemma nth_word_of_N x d (i : 'I_w) :
  nth d (word_of_N x) i =
  if N.testbit x [Num of (val i)]
  then 1%R : 'F_2 else 0%R.
Proof.
by rewrite /word_of_N /= -tnth_nth tcastE tnth_map nth_enum_ord /=.
Qed.

Lemma nth_word_of_N_xor x y d (i : 'I_w) :
nth d (word_of_N (N.lxor x y)) i = (nth d (word_of_N x) i + nth d (word_of_N y) i)%R.
Proof.
  rewrite ?nth_word_of_N N.lxor_spec.
  (repeat case: ifP => //) => *.
   by rewrite GRing.addrr_char2.
  by rewrite GRing.addr0.
Qed.

Local Notation ai := (@array_incomplete w n m r erefl erefl).
Local Notation ia := (@incomplete_array w n m r erefl erefl).

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

Lemma N_of_wordK : cancel N_of_word word_of_N.
Proof.
  move=> x.
  rewrite /word_of_N /N_of_word.
  apply/eq_from_tnth => j.
  set T := (fun x0 y : N => 2 * y + x0).
  rewrite tcastE tnth_map (tnth_nth 0%R) /=
          ?size_enum_ord // nth_enum_ord ?rev_ord_proof //.
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

Definition state_of_array (y : 'rV['F_2]_(n * w - r)) :=
  {| index:=0;
     state_vector:=rev (map N_of_word
      (mktuple (fun j => mktuple (fun x => ai y j x))));|}.

Definition array_of_state (y : random_state) :=
  ia (\matrix_(i, j) nth 0%R (nth (word_of_N 0)
      [seq word_of_N i | i <- rev (rot (index y) (state_vector y))] i) j).

Lemma state_of_arrayK : cancel state_of_array array_of_state.
Proof.
  move=> x.
  rewrite /array_of_state /state_of_array rot0.
  set T := (\matrix_(_, _) _)%R.
  have->: T = (ai x)%R.
   apply/matrixP => i j.
   subst T.
   rewrite !mxE !revK (nth_map 0) /=; last by rewrite 2!size_map size_enum_ord.
   rewrite (nth_map (word_of_N 0)) /=; last by rewrite size_tuple card_ord.
   by rewrite N_of_wordK ?nth_mktuple ?(castmxE, mxE).
  by rewrite array_incompleteK.
Qed.

Lemma pm : prime (2 ^ (n * w - r) - 1).
Admitted.

Definition computeB :=
  array_of_state \o snd \o next_random_state \o state_of_array.

Lemma a32 : size ([:: 1; 0; 0; 1; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 1; 0; 1;
                  1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 1]: seq 'F_2)%R == w.
Proof. by []. Qed.

Local Notation B := (@B w n m r (Tuple a32) erefl erefl erefl erefl).

Lemma size_next_random_state v :
size (state_vector (next_random_state (state_of_array v)).2) = n.
Proof.
by rewrite /next_random_state size_set_nth size_tuple.
Qed.

Lemma index_next_random_state v :
index (next_random_state (state_of_array v)).2 = 1.
Proof. by []. Qed.

(*
from:
https://stackoverflow.com/questions/60581632/how-do-i-describe-a-multiplication-of-vectorized-matrices
*)
Lemma nth_enum_prod p q (a : 'I_q) : val a = seq.index (@ord0 p, a) (enum predT).
Proof.
have /(_ _ 'I_q) pair_snd_inj: injective [eta pair ord0] by move => n T i j [].
have Hfst : (ord0, a) \in [seq (ord0, x2) | x2 <- enum 'I_q].
  by move=> n; rewrite mem_map /= ?mem_enum.
rewrite enumT !unlock /= /prod_enum enum_ordS /= index_cat {}Hfst.
by rewrite index_map /= ?index_enum_ord.
Qed.

Lemma nth_next_random_state v i :
  nth 0 (state_vector (next_random_state (state_of_array v)).2) i.+1%N
= nth 0 (state_vector (state_of_array v)) i.+1.
Proof. by rewrite nth_set_nth. Qed.

Lemma computeBE (v : 'rV_(n * w - r)) : computeB v = (v *m B)%R.
Proof.
  rewrite /computeB.
  apply/rowP => i.
  rewrite !mxE ?castmxE ?mxE (nth_map 0); last
   by rewrite size_rev size_rot size_next_random_state.
  rewrite nth_word_of_N /cycle.B.
  apply/etrans; last first.
   apply/eq_bigr => j _.
   by rewrite castmxE /=.
  set I := (cast_ord _ i).
  set I' := (cast_ord _ (pull_ord _ _ i)).
  rewrite index_next_random_state nth_rev
          ?size_rot ?size_next_random_state ?nth_drop //
          nth_cat size_drop.
  have II: nat_of_ord I = nat_of_ord I' by [].
  apply/etrans; last first.
   apply/eq_bigr => j _.
   by rewrite block_mxEh mxE.
  case: (splitP I) => [a Ia|a].
   have H: (enum_val I') = (ord0, a).
    apply/enum_rank_inj.
    rewrite enum_valK /enum_rank /enum_rank_in /insubd /odflt /oapp /insub.
    destruct idP; last first.
     apply/val_inj.
     move/negP: n0 => /=.
     by rewrite cardT index_mem mem_enum.
    apply/ord_inj.
    by rewrite -II Ia /= (nth_enum_prod n.-1 a).
   have->: (enum_val I').1 = ord0 by rewrite H.
   have->: (enum_val I').2 = a by rewrite H.
   rewrite size_next_random_state ltnn subnn nth_take //.
  rewrite nth_set_nth !N.lxor_spec !N.shiftr_spec ?N.lor_spec ?N.land_spec.
  rewrite !add0n !nth0 !N.add_1_r.
