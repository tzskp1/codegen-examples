From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require Import mt cycle BinNat BinPos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Local Open Scope N_scope.

Definition w := 32.
Definition r := mt.r.
Definition n := mt.len.
Definition m := mt.m.

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

Hint Resolve pos_Num : core.

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

Definition N_of_vector (x : 'rV['F_2]_w) := N_of_word (mktuple (x ord0)).
Definition vector_of_N n := (\row_i (tnth (word_of_N n) i))%R.

Lemma N_of_vectorK : cancel N_of_vector vector_of_N.
Proof.
  move=> x.
  rewrite /N_of_vector /vector_of_N N_of_wordK.
  apply/rowP => i.
  by rewrite mxE tnth_mktuple.
Qed.

Local Notation ai := (@array_incomplete w n (n - m) r erefl erefl erefl erefl erefl).
Local Notation ia := (@incomplete_array w n (n - m) r erefl erefl erefl erefl).

Definition array_of_state (y : random_state) :=
  ia (\matrix_(i, j) nth 0%R (nth (word_of_N 0)
      [seq (@rev_tuple _ _ \o word_of_N) i | i <- rev (rot (index y) (state_vector y))] i) j)%R.

Definition state_of_array (y : 'rV['F_2]_(n * w - r)) :=
  {| index:=0;
     state_vector:=rev (map (N_of_word \o (@rev_tuple _ _))
      (mktuple (fun j => mktuple (fun x => ai y j x))));|}.

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
   by rewrite N_of_wordK ?revK ?nth_mktuple ?(castmxE, mxE).
  by rewrite array_incompleteK.
Qed.

Lemma pm : prime (2 ^ (n * w - r) - 1).
Admitted.

Lemma a32 : size ([:: 1; 0; 0; 1; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 1; 0; 1;
                  1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 1]: seq 'F_2)%R == w.
Proof. by []. Qed.

Local Notation B := (@B w n (n - m) r (Tuple a32) erefl erefl erefl erefl).

(* Local Definition cB := *)
(*   Eval hnf in @computeB w n m r (Tuple a32) erefl erefl erefl erefl. *)
(* Compute (initialize_random_state 338). *)
(* Compute state_of_array (array_of_state (initialize_random_state 338)). *)
(* Print cB. *)

(* Definition T x := Eval compute in (0 : 'rV['F_2]_x)%R. *)
(* Check computeB. *)
(* Eval unfold T in T 2. *)
(* Print T. *)
(*      = (let 'tt := const_mx_key in fun x : Type => id) *)
(*          (('I_1 -> 'I_2 -> 'I_2) -> 'rV_2) *)
(*          (fun x : 'I_1 -> 'I_2 -> 'I_2 => *)
(*           Matrix *)
(*             [ffun x0 => x (let (H, _) := x0 in H) (let (_, H) := x0 in H)]) *)
(*          (fun=> (fun=> Ordinal (ltn0Sn 1))) *)
(*      : 'rV_2 *)

(*      = (let 'tt := const_mx_key in fun x : Type => id) *)
(*          (('I_1 -> 'I_3 -> 'I_2) -> 'rV_3) *)
(*          (fun x : 'I_1 -> 'I_3 -> 'I_2 => *)
(*           Matrix *)
(*             [ffun x0 => x (let (H, _) := x0 in H) (let (_, H) := x0 in H)]) *)
(*          (fun=> (fun=> Ordinal (ltn0Sn 1))) *)
(*      : 'rV_3 *)


Definition computeB :=
  array_of_state \o snd \o next_random_state \o state_of_array.

Lemma size_next_random_state v :
size (state_vector (next_random_state (state_of_array v)).2) = n.
Proof.
by rewrite /next_random_state size_set_nth size_tuple.
Qed.

Lemma index_next_random_state v :
index (next_random_state (state_of_array v)).2 = 1.
Proof. by []. Qed.

Lemma nth_next_random_state v i :
  nth 0 (state_vector (next_random_state (state_of_array v)).2) i.+1%N
= nth 0 (state_vector (state_of_array v)) i.+1.
Proof. by rewrite nth_set_nth. Qed.

Lemma nth_state_vector v (i : 'I_n) :
  nth 0 (state_vector (state_of_array v)) i =
  N_of_word (rev_tuple (mktuple (ai v (rev_ord i)))).
Proof.
rewrite nth_rev; last by rewrite 2!size_map size_enum_ord.
rewrite (nth_map (word_of_N 0)) size_map size_tuple ; last by rewrite rev_ord_proof.
rewrite (nth_map ord0) ?size_tuple ?rev_ord_proof //.
congr N_of_word.
apply/eq_from_tnth => j.
rewrite !(tnth_nth ord0) !nth_rev ?size_tuple //
        !(nth_map ord0) ?size_tuple ?rev_ord_proof
        ?(esym (enumT _), size_enum_ord, rev_ord_proof) //.
by congr (ai _ _); apply/ord_inj; rewrite /= nth_enum_ord ?rev_ord_proof.
Qed.

Lemma testbit_N_of_word v a :
  N.testbit (N_of_word v) [Num of val a] = (tnth v a == 1%R).
Proof.
rewrite (tnth_nth 0%R) -[in RHS](N_of_wordK v) nth_word_of_N.
by case: ifP.
Qed.

Local Lemma tns v b a (Ha : (a < w)%nat) (Hb : (b < n)%nat) :
  N.testbit (nth 0 (state_vector (state_of_array v)) b) [Num of a]
= (ai v (rev_ord (Ordinal Hb)) (rev_ord (Ordinal Ha)) == 1%R).
Proof.
  have H: b = val (Ordinal Hb) by [].
  rewrite [in LHS]H nth_state_vector.
  have {H} H : a = val (Ordinal Ha) by [].
  rewrite [in LHS]H testbit_N_of_word (tnth_nth ord0) nth_rev ?size_tuple //
          (nth_map ord0) ?size_tuple ?rev_ord_proof //.
  congr (_ == _); congr (ai _ _); apply/ord_inj.
  by rewrite nth_enum_ord ?rev_ord_proof.
Qed.

Lemma testbit_N_of_word_w v :
  N.testbit (N_of_word v) w = false.
Proof.
  Admitted.

Lemma computeBE v : computeB v = (v *m B)%R.
Proof.
  rewrite /computeB mulBE /cycle.computeB.
  apply/rowP => i.
  rewrite !mxE ?castmxE ?mxE (nth_map 0); last
   by rewrite size_rev size_rot size_next_random_state.
  rewrite ?nth_rev /comp ?size_tuple ?size_rot ?size_next_random_state ?ltn_pmod //.
  set R := row_ind _ _ _.
  have<-: (rev_ord R = w - R.+1 :> nat)%nat by [].
  rewrite nth_word_of_N /cycle.B; subst R.
  set I := (cast_ord _ i).
  rewrite index_next_random_state
          ?size_rot ?size_next_random_state ?nth_drop //
          nth_cat size_drop ?size_next_random_state.
  set I' := col_ind _ _ _ _ _.
  case: (splitP I) => j Ij; last first.
   have I'0: (I' > 0)%nat.
    rewrite /= in Ij.
    by rewrite /= Ij divnDl.
   have->: (n - I'.+1 < n - 1%N)%nat.
   rewrite /leq subn1 subnS.
   case H: (n - I' > 0)%nat.
    by rewrite prednK // subnAC -subn1 subnBA.
   rewrite lt0n in H.
   by move/negP/negP/eqP: H => ->.
  rewrite nth_drop add1n nth_next_random_state tns => *.
  + rewrite /leq -!subSn //;last by apply/leqW.
    by rewrite subnAC subSn //.
  + by rewrite (rev_ord_proof (Ordinal (@ltn_pmod i w erefl))).
  rewrite break_if !mxE !castmxE.
  congr (v _ _); apply/ord_inj => //.
  rewrite /arr_ind /=.
  set T := cast_ord _ _.
  case: (splitP T) => k /=.
   rewrite /= in Ij.
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
   rewrite /= in Ij.
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

   rewrite /= in Ij.
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

    rewrite /=.
    rewrite !Num_succ !tns; try by rewrite /= Ij Rr.
    rewrite /= Ij Rr mod0n subn1. (rev_ord_proof (Ordinal (@ltn_pmod i w erefl))).
    rewrite /=.
    move=> ? ?.
    set U := N.testbit upper_mask _.
    have->: U = false by rewrite /U /= Ij Rr.
    set L := N.testbit lower_mask _.
    have->: L = true by rewrite /L /= Ij Rr.
    rewrite andbF orFb andbT break_if.
    rewrite !mxE.
    rewrite /arr_ind.

    rewrite /=.
     rewrite /= in Rr.

    rewrite /= Ij Rr.
    move=> ? ->.
   rewrite /= in Rr.
   rewrite castmxE.
   congr (_ + _)%R.

    done.
    apply/leq_trans.
    rewrite -addnC.
    rewrite ltnS#h ltnW //.
    done.
    have: (j < w)%nat by [].
    rewrite je => /ltnW /(leq_trans _) => jle.
    rewrite -/(addn _ _) in jle.

   rewrite /= modn_small in Pl.
    Search (_ == _ +_)%nat.
   rewrite /=.
          rewrite /=

    Print mt.m.
   done.
   done.
   rewrite /=.
   Check nth_state_vector.
   rewrite -!N.shiftr_spec //.
    !addn1 !Num_succ.
   rewrite ?tns.
   rewrite /=.

   set T' := cast_ord _ _.
   set T'' := cast_ord _ _.
   set T := cast_ord _ _.
   rewrite /=.


   (* TODO *)
