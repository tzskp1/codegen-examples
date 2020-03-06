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

Definition N_of_word (t : w.-tuple 'F_2) :=
  foldr (fun x y => 2*y + x) 0
        (map_tuple (fun x => if (x == 1 :> 'F_2)%R then 1%N else 0) t).

Definition word_of_N (n' : N) :=
  tcast (card_ord _)
        (map_tuple (fun i => if N.testbit n' [Num of (val i)]
                          then 1%R : 'F_2 else 0%R) (enum_tuple 'I_w)).

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
  have->: bin_of_nat i.+1 = N.succ (bin_of_nat i).
   apply: (can_inj nat_of_binK).
   rewrite bin_of_natK.

   elim: i => // i IHi.
   rewrite -IHi.
    natTrecE .
   apply: (can_inj bin_of_natK).
   rewrite nat_of_binK.
   rewrite /= nat_of_succ_pos IHi {IHi}.

   apply: (can_inj nat_of_binK).
   rewrite bin_of_natK.

   rewrite /=.
   donee
   rewrite IHi.
   rewrite /=.
   rewrite /=.
   done.
   rewrite /=.

   elim: i => //= i IHi.
   elim: i => //= i IHi.
   congr (_.+1).
   elim: i {IHi} => // i.

   case: i => //.
   rewrite /=.
   compute.
   done.
   rewrite /nat_of_pos /pos_of_nat.

    IHi.
   elim: i {IHi} => // i IHi.
   rewrite /=  nat_of_succ_pos -IHi /=.

  rewrite bin_of_natK.
  rewrite /=.
   rewrite -addn1 nat_of_add_bin.
   move: (bin_of_natK i) => <-.
   rewrite /=.
   rewrite
   move: (nat_of_binK i).
   rewrite /=.
   rewrite nat_of_posK.
   rewrite IHi.
   Set Printing All.
   bin_of_natK
   case: i {IHi} => // i.
   rewrite /N.succ.
   rewrite -nat_of_succ_pos.
   rewrite t
   rewrite /N.succ.
   done.
   rewrite /=.
   rewrite IHi /=.
   apply: (can_inj nat_of_binK).
   done.
   apply
   rewrite /=.

   elim: i => //= i IHi.
    rewrite /=.
   rewrite /=.
   rewrite /pos_of_nat.
   rewrite /=.
   done.
   apply/val_inj.

   rewrite
  rewrite /= N.testbit_succ_r_div2.
  rewrite nat_of_succ_pos.
  move=> i.
  rewrite /=.
  rewrite -cat1s map_cat foldr_cat.

  rewrite /=.

  rewrite -cat1s map_cat foldl_cat.
   case: (lem1 [seq (if x1 == 1%R then 1 else 0) | x1 <- x] (T 0 (if x0 == 1%R then 1 else 0))) => y ye.
   rewrite /= ye {ye}.
   rewrite /T /=.
   rewrite
   rewrite /=.
    rewrite /=.
    N.add_0_r N.testbit_even_0.
   rewrite /=.

  rewrite -cat1s map_cat foldl_cat.
   rewrite /=.
   case: x0.
   rewrite /=.
   rewrite /= yz.

   rewrite /=.

   have: exists y, exists z, (foldl T 0 [seq (if x1 == 1%R then 1 else 0) | x1 <- x0 :: x])
        = 2 * y + z.
    elim: x {IH} => [|? x IH].
     exists (if x0 == 1%R then 1 else 0); exists 0.
     rewrite /= /T; by case: ifP.
    case: IH => y [] z IH.
    exists (2 * y + z).
    rewrite
    rewrite /=.
    move=> ? x.
    rewrite

    den
    rewrite /=.
    rewrite /=.
   rewrite -cat1s map_cat foldl_cat.
   rewrite /=.
   subst T.

  rewrite /=.

  rewrite -cat1s

  (if N.testbit (foldl T (T 0 (if x0 == 1%R then 1 else 0)) [seq (if x1 == 1%R then 1 else 0) | x1 <- x]) (bin_of_nat i) then 1%R else 0%R) = ((x0 :: x)`_i)%R
  rewrite /=.
  rewrite /map_tuple.
  have->: val (Tuple xH) = x.
  rewrite
   rewrite /=.
  rewrite -cat1s foldr_cat /=.
   rewrite /=.
    apply/val_inj => /=.
    case: ifP => //.
    rewrite /= N.add_0_r.
    case: x IH => //.
    move=> ?? IH.
    rewrite -cat1s foldr_cat /=.
    rewrite /=.
    rewrite
    case: ifP => //.
    rewrite
    rewrite

   rewrite /=.
  rewrite
  rewrite /= ltnS leq_eqVlt => /orP[/eqP ->|].
  rewrite /testbit /=


Print N.testbit.
Compute N.testbit 5 2.
Print Pos.testbit.

Check (iota 0 32).
Compute word_of_N 1.
Compute N_of_word .
  case: i.
   case: x0 => []//[|[]//].
   case.
   []//.
    rewrite /=.
   rewrite /=.
  rewrite /=.

   rewrite /=.
  ? x IH i.
  move/eqP: xH iH => <-.
  rewrite nth_last
   rewrite
  move=> x.
  rewrite /=.
  case: x j.
  elim => // ? x IH j.
  rewrite -foldr_map.
  case: ifP.

  rewrite
  rewrite /=.
  rewrite /=.
  case: ifP.
  rewrite /=.
  rewrite tnth_enum_tuple.

Lemma word_of_NK : cancel word_of_N N_of_word.
Proof.
  move=> x.


(* Check testbit. *)
Variable n' : N.
(* Check sumbool. *)

                    (enum 'I_w))).

Check @array_incomplete w n m r erefl erefl.

Check [Num of _].
Definition word_of_N (n : N) :=
           (t : w.-tuple 'F_2) :=
  foldr (fun x y => 2 * y + x) 0
        (map_tuple (fun x => if (x == 1 :> 'F_2)%R then 1%N else 0) t).

Definition state_of_array (y : 'rV['F_2]_(n * w - r)) :=
  {| index:=0;
     state_vector:=map N_of_word
      (mktuple (fun j => mktuple (@array_incomplete w n m r erefl erefl y j)));|}.

Check (state_of_array _).


(* Compute rot 2 (iota 0 4). *)



(* Definition array_incomplete (y : 'rV['F_2]_p) *)
(* Compute rot 2 (iota 0 4). *)
