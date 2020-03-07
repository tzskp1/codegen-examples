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
     state_vector:=map N_of_word
      (mktuple (fun j => mktuple (fun x => ai y j x)));|}.

Definition array_of_state (y : random_state) :=
  ia (\matrix_(i, j) nth 0%R (nth (word_of_N 0)
      [seq word_of_N i | i <- rot (index y) (state_vector y)] i) j).

Lemma state_of_arrayK : cancel state_of_array array_of_state.
Proof.
  move=> x.
  rewrite /array_of_state /state_of_array rot0 -map_comp.
  set T := (\matrix_(_, _) _)%R.
  have->: T = (ai x)%R.
   apply/matrixP => i j.
   subst T.
   rewrite !mxE (nth_map (word_of_N 0)) /=.
    by rewrite N_of_wordK ?nth_mktuple ?(castmxE, mxE).
   by rewrite size_tuple card_ord.
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
  by rewrite /next_random_state size_set_nth size_map size_tuple.
Qed.

Lemma index_next_random_state v :
index (next_random_state (state_of_array v)).2 = 1.
Proof. by []. Qed.

(* Lemma nth_enum_prod i0 m : *)
(* (m < w)%nat -> *)
(* (nth i0 (enum (prod_finType (ordinal_finType n) (ordinal_finType w))) m).1 *)
(* = 0 :> nat. *)
(* Proof. *)
(*   case: m. *)
(*   rewrite /=. *)
(*   ; last first. *)
(*   rewrite /=. *)
(*   rewrite /=. *)
(*   native_compute. *)

Lemma nth_enum_prod p q (a : 'I_q) :
  val a = seq.index (ord0, a) (Finite.enum (prod_finType (ordinal_finType p.+1) (ordinal_finType q))).
Proof.
  elim: p q a => //.
   elim => [[]//| q IHq a].
   case: q IHq a => //.
    move=> ? a.

(* Compute (enum_rank (ord0, ord0) : ordinal_subType #| {:'I_1 * 'I_11}|)%nat. *)

(* Check (0 : 'rV['F_2]_w)%R. *)
(* Check coord_basis _. *)
(* Check coord . *)
(* Definition e := vbasis (fullv : { vspace 'rV['F_2]_w }). *)
(* Compute shiftr w. *)
(* Check e. *)
(* Compute (nth _ e 3 *m shiftr w)%R. *)

Lemma computeBE (v : 'rV_(n * w - r)) : computeB v = (v *m B)%R.
Proof.
  rewrite /computeB.
  apply/rowP => i.
  rewrite !mxE ?castmxE ?mxE (nth_map 0); last
   by rewrite size_rot size_next_random_state.
  rewrite nth_word_of_N /cycle.B.
  apply/etrans; last first.
   apply/eq_bigr => j _.
   by rewrite castmxE /=.
  set I := (cast_ord _ i).
  set I' := (cast_ord _ (pull_ord _ _ i)).
  rewrite index_next_random_state nth_cat size_drop
          size_next_random_state nth_drop.
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
    rewrite -II Ia /= index_map //.

    rewrite /enum_val.
    rewrite (nth_map (ord0, a)).
    rewrite /Finite.enum.
    Set Printing All.
    rewrite /prod.
    rewrite /enum_mem.
    rewrite
    rewrite
    rewrite /seq.index.
    Check prod_enumP _.
    rewrite /find.
    done.

    apply: (can_inj nat_of_ord).





     rewrite /=.
     done.
     done.
     move=> H.
     Check H.
     rewrite memE.
     rewrite inE.
     apply/
     Set Printing All.
     done.
     rewrite card_prod.
     rewrite !card_ord.
    rewrite /=.
    rewrite /=.
    rewrite /enum_mem.
    rewrite /Finite.EnumDef.enum.
    Set Printing All.
    rewrite /prod_enum.
   have->: (enum_val I').1 = ord0 by rewrite H.
   have->: (enum_val I').2 = a by rewrite H.

   move/(f_equal val).
   rewrite ?mxE.
   case: (splitP T).
   case.
   Check unsplit.
   Print T.

  rewrite big_ord_recl.
  set T := (cast_ord _ _).
  case: (splitP T) => [k Tk|k /esym/eqP]; last by rewrite addn_eq0.
  rewrite ?mxE.
  subst I I'.
  case: i II => i Hi.
  case: i Hi => [|i] Hi.
   rewrite /=.
   rewrite nth_enum_ord.
   rewrite /enum_val subn1.

  done.

  have->: val k = T.
  move=> <-.
  rewrite big_ord_recl.
  set T := (cast_ord _ _).
  case: (splitP T) => [|k /esym/eqP]; last by rewrite addn_eq0.


   move/eqP.
   rewrite /=.
   Search (_ + _ = 0).
   rewrite subnK.

   apply/etrans; last first.
    apply/eq_bigr => j _.
    rewrite mxE.
    done.
   rewrite addn0 (_ : (ord0 < n - 1%N)%nat) //.
   rewrite big_ord_recl.
   rewrite /=.
   Check (split (cast_ord (esym (etrans (addnC (623 * 32 - 31)%N 32%N) (tecnw (erefl (397 < 624)%N) (erefl (0 < 397)%N) (erefl (31 < 32)%N)))) ord0)).
    by rewrite block_mxEh mxE.
   rewrite /=.
   rewrite N.add_0_r.
   rewrite /=.
   case.
    apply/enum_rank_inj.
    rewrite enum_valK.
    (* set T := enum_rank  _. *)
    rewrite /= in Ia.
    apply/val_inj.
    rewrite /=.
    rewrite Ia.
    rewrite /enum_rank.
    rewrite /enum_rank_in.
    rewrite /=.
    rewrite /insubd.
    rewrite /odflt.
    rewrite /oapp.
    rewrite /insub.
    destruct idP.
    rewrite /=.
    rewrite /=.
    rewrite /seq.index.
    native_compute.
    apply
    rewrite /=.
    apply/val_inj.
    rewrite
    set T := idP.
    case HT: T => E.
    rewrtie
    rewrite /=.
    rewrite enum_rank_ord.
    rewrite -II.
    apply/enum_val_inj.
    rewrite /= Ia.
    rewrite /enum_rank.
    done.
    rewrite -II Ia.
    rewrite
    rewrite /=.
    rewrite -Ia.
    done.
    rewrite /=.
    rewrite enum_rankK.
   have->: (enum_val I').1 = 0 :> nat.
   Check (ord0, a).
   Check enum_val_ord I'.
   rewrite enum_rankK.
   Check mxvec_index.

   case In: ((enum_val I').1 < n - 1%N)%nat.
   apply/etrans; last first.
    apply/eq_bigr => j _.
    by rewrite ?mxE.

    have: (enum_val I').1 = 0 :> nat.
    rewrite -II.
    done.
    done.
    by rewrite block_mxEh mxE.

   rewrite /N.testbit.
   rewrite /Pos.testbit.
   set J := (cast_ord _ j).
   Check (cast_ord (esym (etrans (addnC (623 * 32 - 31)%N 32%N) (tecnw (erefl (397 < 624)%N) (erefl (0 < 397)%N) (erefl (31 < 32)%N)))) j).
   Check
  rewrite nth_drop /S.
  set T := if _ then _ else _.
  rewrite /=.

  rewrite /enum_val -II Ia nth_enum_prod //.
  rewrite nth_drop.
  rewrite nth_take //.

   rewrite /enum_val -II Ia.
   by rewrite nth_enum_prod .
   case: a Ia => /= a Ha  _.
   case: a Ha => [*|].
   rewrite /=.
   set T := enum _.
   have: T != [::].
    apply/negP => /eqP /(f_equal size).
    subst T.
    rewrite -cardE /= => /card0_eq H.
    move: (H ((ord0, ord0) : 'I_n * 'I_w)).
    by rewrite inE.
   subst T.
   rewrite /T.
    Check prod_enumP _.
   case: T => //.
    rewrite predX_prod_enum.
    rewrite /enum.
     rewrite s
    rewrite size_enum_ord.
    apply/size0nil.
    native_compute.
    rewrite /
    rewrite /T.
    apply/val_inj.
    done.

   case:enum
   Set Printing All.
   native_compute.
   rewrite (enum_val_nth (enum_default I')).
  rewrite nth_enum_ord.
   (* Check ord0 ord0. *)

   rewrite /=.
   Set Printing All.
   case: a Ha => //.
   set T := nth _ _ _.
   rewrite nth_enum_ord .
  rewrite
   rewrite nth_enum.
  case sI: (split I) => [a|a].
   case: (splitP I).
    move=> ?.
   rewrite /=.

   have: val I = a.

  move/splitP : (split I).
   rewrite

  case sI : (val I < w)%nat.
    rewrite
   case
    move: In.
    have: val I = a.
     case: I sI {II} => ??.
     rewrite /split.
     case: ifP => //.
     hhkk wb
     rewrite /=.
     move/(f_equal val).

     rewrite /=.
     rewrite /=.
     done.
    rewrite /=.
    rewrite /= in In.

   case: ifP.

   rewrite nth_drop.
    done.

   Print n.
    rewrite /= in sI
   case:

    rewrite /=.
    rewrite -cast_ord_comp.
    by rewrite castmxE /=.

  case: ifP => H.

   done.
  case i0: (val i == 0)%nat.
   have->: i = ord0.
    apply/val_inj.
    by rewrite (eqP i0).
    done.
   rewrite /=.

  rewrite
   case: i i0 => i /=.
  set J := (cast_ord _ j).
  case jn: (j <= n.-1)%nat.

  case sJ: (split J).
   rewrite mxE sJ mxE.
   case sI: (split I).
    rewrite mxE.
    done.

    sJ.
   rewrite mxE.

   case: ifP
  Check split.
  have->: J = j :> nat.
   subst T.
   case: j => j jH.
   native_compute.
   done.
   case: j jH => //.
   rewrite /T.
   rewrite /=.
   apply/val_inj.

  done.
  rewrite -cast_ordKV.
  rewrite -summxE.
  rewrite /pull_ord.
  rewrite nth_cat.
  rewrite size_drop.
  rewrite nth_drop.
  rewrite nth_take.
  rewrite /=.
  set T := [Num of _].
  rewrite /= in T.
  case: ifP => H.
  Check [Num of val (enum_val (cast_ord (esym (erefl 1%N, mxvec_cast n w).2) (pull_ord (erefl (m < n)%N) (erefl (r < w)%N) i))).2].
  rewrite
rewrite /=.
  rewrite /=.

  rewrite /array_of_state.
  rewrite /=.
  rewrite /computeB /=.
  rewrite mxE.
  rewrite /=.
  case: ifP => H.

  Check can_inj.


Lemma computeB_seq (x : 'M['F_2]_(n, w)%R) (i : 'I_n) :
(ai \o computeB \o ia) x i =1 x (Ordinal (@ltn_pmod i.+1 n erefl)).
Proof.
  move=> j.
  rewrite /computeB.
Check pcan_inj.
  rewrite /=.
  rewrite /= array_incompleteK.
  rewrite
  rewrite

Check Ordinal (@ltn_pmod i.+1 n erefl).

Lemma computeB_linear : linear computeB.
Proof.
  move=> ? x y.
  rewrite /computeB /=.
  apply/rowP => i.
  rewrite ?(castmxE, mxE).
  rewrite (nth_map 0).
  rewrite nth_cat.
  rewrite size_drop.

  rewrite (nth_map 0).
  rewrite nth_cat.
  rewrite size_drop.

  rewrite (nth_map 0).
  rewrite nth_cat.
  rewrite size_drop.
  case: ifP => //.
  move=> H.
rewrite /=.
  rewrite nth_drop.
  rewrite mxE.
  apply (can_inj state_of_arrayK).

  rewrite
  elim: m => // m IHm a x y.
    by rewrite !iterSr !GRing.linearP IHm.
Qed.
  Canonical iter_linearType m := Linear (iter_linear m).
*)

Lemma commutativity :
  computeB =1 (fun (b : 'rV_(n * w - r)) =>
     b *m (@B w n m r (Tuple a32) pm erefl erefl erefl erefl erefl))%R.
Proof.
  move=> x.
  apply/rowP => i.
  rewrite /=.
  rewrite /computeB /=.
  rewrite /array_of_state.
  rewrite !mxE ?castmxE.
  rewrite mxE.
  rewrite ?mxE.
  rewrite /=.
  rewrite (nth_map 0).
  rewrite nth_cat.
  rewrite size_drop.
  case: ifP => H.
  rewrite nth_drop.
  rewrite /=.
  rewrite rot1.

  apply (can_inj state_of_arrayK).
  rewrite /=.
  rewrite state_of_arrayK.
  rewrite /=.
