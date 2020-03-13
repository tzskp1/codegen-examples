From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require Import mt cycle BinNat BinPos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Compute word_of_N a.
Lemma a32 : size ([:: 1; 0; 0; 1; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 1; 0; 1;
                  1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 1]: seq 'F_2)%R == w.
Proof. by []. Qed.
(* 10011001000010001011000011011111 *)

Local Notation B := (@B w n (n - m) r (Tuple a32) erefl erefl erefl erefl).

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

Local Lemma tnsw v b (Hb : (b < n)%nat) :
  N.testbit (nth 0 (state_vector (state_of_array v)) b) [Num of w] = false.
Proof.
  by rewrite /state_of_array /= nth_rev ?(size_enum_ord, size_map) //
          (nth_map (word_of_N 0%N)) ?(size_enum_ord, size_map)
          ?(rev_ord_proof (Ordinal Hb)) // N_of_word_last.
Qed.

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
    rewrite modn_small //.

    Print len.
    rewrite
    native_compute.
    done.
    ring.
    done.
    rewrite subnS.
    rewrite subnS.
    rewrite -subSn ?ltn_mod //.
    rewrite -subSn ?ltn_mod //.
    rewrite -subSn ?ltn_mod //.
    rewrite !subSS.
    done.
    rewrite -subSn.
    rewrite -subSn.
    rewrite subSS.
    rewrite -subSn.
    rewrite subnBA.
    q30.

   congr (_ + _)%R.
   rewrite q30.
   set TT := val (rev_ord _).
   have: TT = 1.
   rewrite /TT /=.
   Check (val (rev_ord (row_ind (erefl _) (erefl (gluing.r < w)%N) i))).+1.
   rewrite /=.



      rewrite TT30 //=.
      rewrite /=.
      rewrite modn_small //.
      rewrite modn_small //.

      rewrite modn_small //.
      rewrite eqE /=.
     by rewrite /= Rr in Rr'.
    by rewrite mxE.

    rewrite mxE.
     rewrite /=.
     done.
     rewrite /= in Tmpt.
    rewrite
     Compute N.testbit upper_mask [Num of 31].
    rewrite /=.
    rewrite /TT.
    rewrite /=.

    rewrite Ij.
    rewrite /= in Rr.
    rewrite /TT.
    rewrite /=.
