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

Local Notation ai := (@array_incomplete w n m r erefl erefl erefl erefl erefl).
Local Notation ia := (@incomplete_array w n m r erefl erefl erefl erefl).

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

Lemma lxorE x y :
  vector_of_N (N.lxor x y) = (vector_of_N x + vector_of_N y)%R.
Proof.
  apply/rowP => i.
  rewrite !mxE !tcastE !tnth_map N.lxor_spec.
  set A := N.testbit _ _; set B := N.testbit _ _.
  case: A B => [][]//=.
   rewrite GRing.addrr_char2 //.
  by rewrite GRing.addr0.
Qed.

Definition z (rand : random_state) :=
  let state_vec := state_vector rand in
  let ind := index rand in
  let current := nth 0 state_vec ind in
  let next_ind := Nat.modulo (ind + 1%nat) len in
  let next := nth 0 state_vec next_ind in
  N.lor (N.land current upper_mask)
        (N.land next lower_mask).

Notation cz := (@cycle.z' w n m r erefl erefl erefl).

Definition array_of_state (y : random_state) :=
  ia (\matrix_(i, j) nth 0%R (nth (word_of_N 0)
      [seq word_of_N i | i <- rev (rot (index y) (state_vector y))] i) j)%R.

Definition state_of_array (y : 'rV['F_2]_(n * w - r)) :=
  {| index:=0;
     state_vector:=rev (map N_of_word
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
   by rewrite N_of_wordK ?nth_mktuple ?(castmxE, mxE).
  by rewrite array_incompleteK.
Qed.

Lemma pm : prime (2 ^ (n * w - r) - 1).
Admitted.

Lemma a32 : size ([:: 1; 0; 0; 1; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 1; 0; 1;
                  1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 1]: seq 'F_2)%R == w.
Proof. by []. Qed.

Local Notation B := (@B w n m r (Tuple a32) erefl erefl erefl erefl).

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
  N_of_word (mktuple (ai v (rev_ord i))).
Proof.
rewrite nth_rev; last by rewrite 2!size_map size_enum_ord.
rewrite (nth_map (word_of_N 0)) size_map size_tuple ; last by rewrite rev_ord_proof.
rewrite (nth_map ord0) ?size_tuple ?rev_ord_proof //.
congr N_of_word.
apply/eq_from_tnth => j.
rewrite !tnth_mktuple /=.
set T := nth _ _ _.
have-> //: T = rev_ord i.
apply/ord_inj.
by rewrite nth_enum_ord // ?rev_ord_proof.
Qed.

Lemma testbit_N_of_word v a :
  N.testbit (N_of_word v) [Num of val a] = (tnth v a == 1%R).
Proof.
rewrite (tnth_nth 0%R) -[in RHS](N_of_wordK v) nth_word_of_N.
by case: ifP.
Qed.

Local Lemma tns v b a (Ha : (a < w)%nat) (Hb : (b < n)%nat) :
  N.testbit (nth 0 (state_vector (state_of_array v)) b) [Num of a]
= (ai v (rev_ord (Ordinal Hb)) (Ordinal Ha) == 1%R).
Proof.
  have H: b = val (Ordinal Hb) by [].
  rewrite [in LHS]H nth_state_vector.
  have {H} H : a = val (Ordinal Ha) by [].
  by rewrite [in LHS]H testbit_N_of_word tnth_mktuple.
Qed.

Lemma computeBE v : computeB v = (v *m B)%R.
Proof.
  rewrite /computeB mulBE /cycle.computeB.
  apply/rowP => i.
  rewrite !mxE ?castmxE ?mxE (nth_map 0); last
   by rewrite size_rev size_rot size_next_random_state.
  rewrite nth_word_of_N /cycle.B.
  set I := (cast_ord _ i).
  rewrite index_next_random_state nth_rev
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
  + by rewrite /= ltn_mod.
  rewrite break_if !mxE !castmxE.
  congr (v _ _); apply/ord_inj => //.
  rewrite /arr_ind /=.
  set T := cast_ord _ _.
  case: (splitP T) => k /=.
   rewrite /= in Ij.
   rewrite Ij 3!subnS -!subn1 -!subnDA !addn1 subnDA subKn.
    by rewrite subn2 /= !divnDl // divnn add1n modnDl -divn_eq => ->.
   rewrite divnDl // add1n /leq !subSS subn_eq0.
   case: j {Ij} => j H.
   apply/leq_trans.
    apply leq_div2r.
    by apply H.
   by [].
   rewrite /= in Ij.
   rewrite Ij 3!subnS -!subn1 -!subnDA !addn1 subnDA subKn.
    rewrite subn2 /= !divnDl // divnn add1n modnDl -divn_eq => jnwr.
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
   rewrite !N.lxor_spec tns ?ltn_pmod // => *.
   rewrite N.shiftr_spec //.
   rewrite N.lor_spec !N.land_spec !addn1.
   rewrite !Num_succ.

   (* TODO *)
   rewrite tns.
   rewrite /=.

   rewrite N.add_1_r -succ_nat.

   rewrite addn1.
   rewrite tns.
   rewrite /index .
   rewrite tns.
   rewrite /=.
   rewrite /=.#ht
   rewrite


     done.
      H.
   rewrite divnDl // add1n /leq !subSS subn_eq0.
  rewrite

   move: Tk.
   rewrite /=.
   rewrite /=.
     rewrite /=.
     done.
     apply: (_ : _ < n.-1 * w)%nat.


    Search ((_ + _)%% _)%nat.
    rewrite

   rewrite -subnBA.
   rewrite -addnBA.
   rewrite
   Search (_ - (_ - _))%nat.
   rewrite subnAC.
   rewrite subnAC.
   rewrite subnAC.
   rewrite subnAC.
   rewrite subnBA.
   rewrite
   rewrite subnS.
   rewrite subnS.
   rewrite /= in Tk.

  rew


  rewrite /=.
  rewrite -subSn // subSS /leq.
  rewrite -subSn //=.
  subnAC.
  case: I' I'0 => [][]//= I' I'H _.
  rewrite subnS prednK //.
  apply rev_ord_proof.
  apply rev_ord
  rewrite /=.
  elim: I' I'0 => //.
  rewrite
  rewrite /leq.
  rewrite subnS.
  case: I' I'0 => // *.
  rewrite /= subnS prednK //.
  rewrite /=.
  rewrite
   Search ((_ + _) %/ _)%nat.
   rewrite /=.
    rewrite /=.

     Search
     rewrite -subnDA.
      subnS.
     case:
     Search (_ - _.-1)%nat.
    suff?: (n - I' > 0)%nat.

     subSn.
    case: I'
   rewrite subnS.
  rewrite /= in Ij.
  have: val I' = 0%nat.
  rewrite /=.
  have: val (col_ind (erefl _) (erefl _) (erefl _) (erefl _) i).+1 = 0%nat.
  rewrite
   case H: (n - (enum_val I').1.+1 < n - 1%N)%nat.
    rewrite nth_drop add1n nth_next_random_state -subSn // subSS tns //=.
     rewrite /leq -subSn; last by apply ltnW.
     rewrite subnAC subSn // subnn subn_eq0.
     by case: (enum_val I').1 H => [][]//.

  set I' := (cast_ord _ (pull_ord _ _ i)).
  have II: nat_of_ord I = nat_of_ord I' by [].
    move=> H1 H2.
    set S := rev_ord _.
    have: S = (enum_val I').1.
     apply/ord_inj.
     rewrite /=.
   rewrite /=.
    rewrite break_if.
    hh?(mxE, castmxE).
    rewrite break_if ?(mxE, castmxE).
    set T := cast_ord _ _.
    case: (splitP T) => k Tk.
     congr (v _ _); apply/val_inj => //.
     rewrite /=.
     rewrite /= in Tk.
    rewrite /= in Ij.
    rewrite /= in Tk.

    rewrite
   rewrite /y.
   have: val T = (enum_val I').1.-1.
   rewrite /T.
   apply/val_inj.
   rewrite /=.
   rewrite //=.
   rewrite testbit_N_of_word.
   rewrite subSS subnAC subnn .

   case H: (val (enum_val I').1 == 0)%nat; last first.
   move: H.
   rewrite /enum_val enumT /=.
   rewrite nth_map.
   rewrite /prod_enum.
   rewrite /= unlock.
   rewrite /=.
    have H'': (enum_val I') = (ord0, j).
     apply/enum_rank_inj.
     rewrite enum_valK /enum_rank /enum_rank_in /insubd /odflt /oapp /insub.
     destruct idP; last first.
      apply/val_inj.
      move/negP: n0 => /=.
      by rewrite cardT index_mem mem_enum.
     apply/ord_inj.
     by rewrite -II Ij /= (nth_enum_prod n.-1).
    have H''1: (enum_val I').1 = ord0 by rewrite H''.
    by rewrite H''1 in H.
  rewrite break_if.

   have H': (n - (enum_val I').1.+1 < n - 1%N)%nat.
    case: ((enum_val I').1) H => []/=[]// n0.
    rewrite ltnS subSS subn1 => nn.
    by move: (rev_ord_proof (Ordinal nn)).
    rewrite /=.
    rewrite H' nth_drop add1n nth_next_random_state tns //.
    by case: (enum_val I') => + [].
   move=> H'''.
   case: (splitP I) => j Ij.
    have H'': (enum_val I') = (ord0, j).
     apply/enum_rank_inj.
     rewrite enum_valK /enum_rank /enum_rank_in /insubd /odflt /oapp /insub.
     destruct idP; last first.
      apply/val_inj.
      move/negP: n0 => /=.
      by rewrite cardT index_mem mem_enum.
     apply/ord_inj.
     by rewrite -II Ij /= (nth_enum_prod n.-1).
    have H''1: (enum_val I').1 = ord0 by rewrite H''.
    by rewrite H''1 in H.
   rewrite break_if.
   have j' : (j < n * w - r)%nat.
    case: j {Ij} => j Hj.
    by apply: (leq_trans Hj).
   rewrite ?(mxE, castmxE) cast_ord_id.
   (* apply/etrans; last first. *)
   (*  apply: (_ : v ord0 (Ordinal j') = _). *)
   (*  rewrite [in LHS](row_sum_delta v) summxE. *)
   (*  rewrite /lsubmx. *)
   (*  apply eq_bigr => k _. *)
   (*  rewrite !mxE eqxx /=. *)
   (*  congr (_ * _)%R. *)
   (*  set S := cast_ord _ _. *)
   (*  case: (splitP S) => /= l lS. *)
   (*   by rewrite mxE eqE /= lS eq_sym. *)
   (*  rewrite eqE mxE /=. *)
   (*  case jk: (val j == nat_of_ord k) => //. *)
   (*  move/eqP: jk => jk. *)
   (*  case: j jk {Ij j'} => j /= + jk. *)
   (*  by rewrite jk lS ltnNge leq_addr. *)
   (* rewrite ?(mxE, castmxE) cast_ord_id. *)
   set T := cast_ord _ _.
   case: v => c g.
   case: (splitP T) => k /= Tk; last first.
    move: Tk; set S := rev_ord _.
    have I'p: ((enum_val I').1.-1 < n)%nat.
     case: (enum_val I').1 H {H' T S} => [][]//= ? Hc _.
     by apply: (leq_trans _ Hc).
    have->: S = Ordinal I'p.
     apply/val_inj.
     by rewrite /= 2!subnS subnBA.
    rewrite enum_rank_prodE /= => Hc.
    have: (n * w - r + k < n * w - r + k)%nat.
    rewrite -[X in (X < _)%nat]Hc.
    case: (enum_val I').2 => b Hb.
    apply: leq_trans.
     apply: (_ : (_ < (enum_val I').1.-1 * w + w)%nat); by rewrite ltn_add2l.
    rewrite addnC -mulSn.
    apply: leq_trans; last first.
     apply: (_ : n.-1 * w <= _)%nat.
     apply: leq_trans.
     apply: (_ : _ <= n * w - r)%nat.
      have Hn: n = n.-1.+1 by [].
      by rewrite [X in (_ <= X *_ - _)%nat]Hn mulSn addnC -addnBA //.
     by rewrite leq_addr.
    rewrite leq_mul2r /=.
    by case: (enum_val I').1 H => /=[][].
    by rewrite ltnn.
   congr (c _ _); apply/ord_inj => //.
   rewrite -Tk enum_rank_prodE /= 2!subnS subnBA // [X in (X - n)%nat]addnC addnK.
   Focus 2.
   move/eqP: H => H.
   rewrite H ltnn subnn nth_take //.
