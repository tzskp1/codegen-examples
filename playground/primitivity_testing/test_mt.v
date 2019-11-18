From mathcomp Require Import all_ssreflect.

Require Import BinNat.

Require Import codegen.codegen.

Open Scope N_scope.

Definition w : nat := 32.
Definition n : nat := 624.
Definition m : nat := 397.
Definition r : nat := 31.

Definition p : nat := w * n - r.

Definition upper_mask := 2147483648.
Definition lower_mask := upper_mask - 1.

Definition bottom_zero_mask := 429496726.
Definition bottom_one_mask := 1.

Definition word_seq := seq N.

Record random_state := {index : nat; state : word_seq}.

Fixpoint range (i : nat) : seq N :=
  match i with
  | 0%nat => [::]
  | S i' => (N_of_nat (minus n i)) :: (range i')
  end.

Definition initial_state : word_seq := range n.

Definition make_mtRand state := {| index := 0; state := state; |}.

Definition next a rand :=
  let i := (index rand) in
  let i1 := Nat.modulo (i + 1%nat) n in
  let s := (state rand) in
  let z := N.lor (N.land (nth 0 s i) upper_mask)
                 (N.land (nth 0 s i1) lower_mask) in
  let im := Nat.modulo (i + m) n in
  let xi := N.lxor (N.lxor (nth 0 s im)
                           (N.shiftr z 1))
                   (if N.eqb (N.land z 1) 0 then 0 else a) in
  let next_rand := {|
        index := i1;
        state := set_nth 0 s i xi;
      |} in
  (xi, next_rand).

Fixpoint generate a words rand times :=
  match times with
  | 0%nat => words
  | S m =>
    let (nextValue, nextRand) := next a rand in
    generate a (words ++ [:: nextValue]) nextRand m
  end.

Fixpoint decimate_aux words acc times :=
  match times with
  | 0%nat => acc
  | S times' =>
    let j := plus (minus p times) 1%nat in
    let k := minus (2%nat * j) 1%nat in
    decimate_aux words (acc ++ [:: nth 0 words k]) times'
  end.

Definition decimate words :=
  decimate_aux words [:: nth 0 words 0] p.

Fixpoint process_aux a words times :=
  match times with
  | 0%nat => words
  | S times' =>
    let k := plus times n in
    let xk := nth 0 words k in
    let kn := minus k n in
    let xkn := nth 0 words kn in
    let knm := plus kn m in
    let xknm := nth 0 words knm in
    let kn1 := plus kn 1%nat in
    let xkn1 := nth 0 words kn1 in
    let y := N.lxor xk
                    (N.lxor xknm
                            (if N.eqb (N.land xkn1 1) 0 then 0 else a)) in
    let y1 := N.shiftl y 1 in
    let y2 := if N.eqb (N.land xkn1 1) 0
              then N.land y1 bottom_zero_mask
              else N.lor y1 bottom_one_mask in
    let newxkn1 := N.lor (N.land upper_mask xkn1)
                         (N.land lower_mask y2) in
    let newxkn := N.lor (N.land upper_mask y2)
                         (N.land lower_mask xkn) in
    let words1 := set_nth 0 words kn1 newxkn1 in
    let words2 := set_nth 0 words1 kn newxkn in
    let state := take n words2 in
    process_aux a state times'
  end.

Definition process a state : seq N :=
  let rand := make_mtRand state in
  let p2n := minus (2%nat * p) n in
  let expandedWords := generate a state rand p2n in
  let decimatedWords := decimate expandedWords in
  let pn := minus p n in
  process_aux a decimatedWords pn.

Fixpoint recursive_process a state times :=
  match times with
  | 0%nat => state
  | S times' => process a (recursive_process a state times')
  end.

Definition a := 2567483615.

Fixpoint check_aux initial_state last_state index :=
  match index with
  | 0%nat => true
  | S index' => ((nth 0 initial_state index) == (nth 0 last_state index)) && check_aux initial_state last_state index'
  end.

Definition check initial_state last_state :=
  ((N.land upper_mask (nth 0 initial_state 0)) == (N.land upper_mask (nth 0 last_state 0))) && check_aux initial_state last_state (minus n 1%nat).

Definition test a := check initial_state (recursive_process a initial_state p).
