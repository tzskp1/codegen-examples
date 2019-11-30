From mathcomp Require Import all_ssreflect.

Require Import BinNat.

Require Import codegen.codegen.

Open Scope N_scope.

Definition w : nat := 32.
Definition n : nat := 624.
Definition m : nat := 397.
Definition r : nat := 31.

Definition p : nat := w * n - r.

Definition len : nat := 2*p.

Definition upper_mask := 2147483648.
Definition lower_mask := upper_mask - 1.

Definition bottom_zero_mask := 2 * upper_mask - 2.

Definition bottom_one_mask := 1.

Definition word_seq := seq N. (* len.-tuple N にするべきか *)

Definition state_vector := seq N. (* n.-tuple N にしたい*)

Definition state_vector_of_word_seq (words : word_seq) : state_vector :=
  take n words.

Definition word_seq_of_state_vector (state : state_vector) : word_seq := state.

Record random_state := {index : nat; state : state_vector}.

Fixpoint range_aux (i : nat) : seq N :=
  match i with
  | 0%nat => [::]
  | S i' => (N_of_nat i') :: (range_aux i')
  end.

Definition range i := rev (range_aux i). 

Definition initial_state : state_vector  := range n. (* in_tuple (range n) にしたい *)

Definition start_state := initial_state.

Definition make_mtRand state := {| index := 0; state := state; |}.

Definition set_nth_state_vector (s : state_vector) i x : state_vector :=
  set_nth 0 s i x.

Definition nth_state_vector (s : state_vector) i : N := nth 0 s i.

Definition set_nth_word_seq (s : word_seq) i x : word_seq :=
  set_nth 0 s i x.

Definition nth_word_seq (s : word_seq) i : N := nth 0 s i.

Definition next a rand :=
  let i := (index rand) in
  let i1 := Nat.modulo (plus i 1%nat) n in
  let s := (state rand) in
  let z := N.lor (N.land (nth_state_vector s i) upper_mask)
                 (N.land (nth_state_vector s i1) lower_mask) in
  let im := Nat.modulo (plus i m) n in
  let xi := N.lxor (N.lxor (nth_state_vector s im)
                           (N.shiftr z 1))
                   (if N.eqb (N.land z 1) 0 then 0 else a) in
  let next_rand := {|
        index := i1;
        state := set_nth_state_vector s i xi;
      |} in
  (xi, next_rand).

Definition p2n := minus len n.

Fixpoint generate_aux a (words : word_seq) rand times : word_seq :=
  match times with
  | 0%nat => words
  | S m =>
    let (nextValue, nextRand) := next a rand in
    generate_aux a (set_nth_word_seq words (plus n (p2n - times)) nextValue) nextRand m
  end.

Definition generate a (state : state_vector) : word_seq :=
  let rand := make_mtRand state in
  let start_word_seq := word_seq_of_state_vector state in
  generate_aux a start_word_seq rand p2n.

Fixpoint decimate_aux (words : word_seq) (acc : word_seq) times : word_seq :=
  match times with
  | 0%nat => acc
  | S times' =>
    let j := plus (minus p times) 1%nat in
    let k := minus (2%nat * j) 1%nat in
    decimate_aux words (set_nth_word_seq acc j (nth_word_seq words k)) times'
  end.

Definition decimate words :=
  decimate_aux words words p.

Fixpoint process_aux a (words : word_seq) times : word_seq :=
  match times with
  | 0%nat => words
  | S times' =>
    let k := plus times (minus n 1%nat) in
    let xk := nth_word_seq words k in
    let kn := minus k n in
    let xkn := nth_word_seq words kn in
    let knm := plus kn m in
    let xknm := nth_word_seq words knm in
    let kn1 := plus kn 1%nat in
    let xkn1 := nth_word_seq words kn1 in
    let y := N.lxor (N.lxor xk xknm)
                    (if N.eqb (N.land xkn1 1) 0 then 0 else a) in
    let y1 := N.shiftl y 1 in
    let y2 := if N.eqb (N.land xkn1 1) 0
              then N.land y1 bottom_zero_mask
              else N.lor y1 bottom_one_mask in
    let newxkn1 := N.lor (N.land upper_mask xkn1)
                         (N.land lower_mask y2) in
    let newxkn := N.lor (N.land upper_mask y2)
                        (N.land lower_mask xkn) in
    let words1 := set_nth_word_seq words kn1 newxkn1 in
    let words2 := set_nth_word_seq words1 kn newxkn in
    process_aux a words2 times'
  end.

Definition a := 2567483615.

Definition process a (state : state_vector) : state_vector :=
  let expandedWords := generate a state in
  let decimatedWords := decimate expandedWords in
  let pn1 := minus p (minus n 1%nat) in
  state_vector_of_word_seq (process_aux a decimatedWords pn1).

Fixpoint recursive_process a state times {struct times} :=
  match times with
  | 0%nat => state
  | S times' => recursive_process a (process a state) times'
  end.

Fixpoint check_aux initial_state last_state index :=
  match index with
  | 0%nat => true
  | S index' => (N.eqb (nth_state_vector initial_state index)
                       (nth_state_vector last_state index))
                &&
                check_aux initial_state last_state index'
  end.

Definition check initial_state last_state :=
  (N.eqb (N.land upper_mask (nth_state_vector initial_state 0))
         (N.land upper_mask (nth_state_vector last_state 0)))
  &&
  check_aux initial_state last_state (minus n 1%nat).

Definition test a := check initial_state (recursive_process a start_state p).

CodeGen Terminate Monomorphization start_state.
CodeGen Terminate Monomorphization initial_state.
CodeGen Terminate Monomorphization set_nth_state_vector.
CodeGen Terminate Monomorphization nth_state_vector.
CodeGen Terminate Monomorphization set_nth_word_seq.
CodeGen Terminate Monomorphization nth_word_seq.
CodeGen Monomorphization next.
CodeGen Monomorphization generate_aux.
CodeGen Monomorphization generate.
CodeGen Monomorphization decimate_aux.
CodeGen Monomorphization decimate.
CodeGen Monomorphization process_aux.
CodeGen Monomorphization process.
CodeGen Monomorphization recursive_process.
CodeGen Monomorphization check_aux.
CodeGen Monomorphization check.
CodeGen Monomorphization test.
Print _next.
Print _generate_aux.
Print _generate.
Print _decimate_aux.
Print _decimate.
Print _process_aux.
Print _process.
Print _recursive_process.
Print _check_aux.
Print _check.
Print _test.

CodeGen GenCFile "inversive_decimation_generated.c"
        _next
        _generate_aux
        _generate
        _decimate_aux
        _decimate
        _process_aux
        _process
        _recursive_process
        _check_aux
        _check
        _test.
