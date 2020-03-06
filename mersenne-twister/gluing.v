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

Lemma succ_nat i : bin_of_nat i.+1 = N.succ (bin_of_nat i).
Proof.
  apply: (can_inj nat_of_binK).
  rewrite bin_of_natK.
  elim: i => // i IHi.
  rewrite /= nat_of_succ_pos IHi {IHi}.
  Admitted.


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
  have->: (N.div2 (T (if x0 == 1%R then 1 else 0) (foldr T 0 [seq (if x1 == 1%R then 1 else 0) | x1 <- x])))
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
      (mktuple (fun j => mktuple (@array_incomplete w n m r erefl erefl y j)));|}.

Definition array_of_state (y : random_state) :=
  map word_of_N (rot (index y) (state_vector y)).
Check @incomplete_array w n m r erefl erefl.
Check array_of_state.
   'rV['F_2]_(n * w - r).
  {| index:=0;
     state_vector:=map N_of_word
      (mktuple (fun j => mktuple (@array_incomplete w n m r erefl erefl y j)));|}.

(* Compute rot 2 (iota 0 4). *)



(* Definition array_incomplete (y : 'rV['F_2]_p) *)
(* Compute rot 2 (iota 0 4). *)
