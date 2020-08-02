From mathcomp Require Import all_ssreflect all_algebra.
Require Import codegen.codegen primitivity nat_word BinNat.
Require mt cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section gluing.
Local Open Scope N_scope.

Notation len := 624. (* 'n' in tgfsr3.pdf, p.4 is 623*)
Notation m := 397. (* 'm' in  tgfsr3.pdf, p.4 *)
Notation w := 32.
Notation r := 31.
Notation u := 11.
Notation s := 7.
Notation t := 15.
Notation l := 18.
Notation a := 2567483615.
Notation b := 2636928640.
Notation c := 4022730752.

Definition upper_mask := Eval compute in @mt.upper_mask r w erefl.
Definition lower_mask := Eval compute in @mt.lower_mask r w erefl.
Definition whole_mask :=
Eval compute in N_of_word (Tuple (@introTF _ _ true eqP (size_rep (1%R: 'F_2) w))).
Definition set_nth d xs n := Eval compute in @set_nth N d xs n.
Definition nth d xs n := Eval compute in @nth N d xs n.
Definition next_random_state (rand : mt.random_state) :=
let state_vec := mt.state_vector rand in
let ind := mt.index rand in
let current := nth 0 state_vec ind in
let next_ind := N.succ ind mod len in
let next := nth 0 state_vec next_ind in
let far_ind := (ind + m) mod len in
let far := nth 0 state_vec far_ind in
let z := N.lor (N.land current upper_mask) (N.land next lower_mask) in
let xi := N.lxor (N.lxor far (N.shiftr z 1)) (if N.testbit z 0 then a else 0) in
let next_rand :=
  {| mt.index := next_ind; mt.state_vector := set_nth 0 state_vec ind xi |} in
(xi, next_rand).

Lemma next_random_stateE2 :
  next_random_state =1 @mt.next_random_state len m r a w erefl.
Proof. by []. Qed.

Definition tempering xi :=
  let y1 := N.lxor xi (N.shiftr xi u) in
  let y2 := N.lxor y1 (N.land (N.shiftl y1 s) b) in
  let y3 := N.lxor y2 (N.land (N.shiftl y2 t) c) in
  let y4 := N.lxor y3 (N.shiftr y3 l) in
  y4.
Lemma temperingE : tempering =1 mt.tempering u s t l b c.
Proof. by []. Qed.

Definition cycleB_dvdP :=
  @cycle.cycleB_dvdP w len (len - m) r (word_of_N w a) pm
                     erefl erefl erefl erefl erefl.

Definition next_random_stateE1 :=
  @cycle.next_random_stateE w len (len - m) r (word_of_N w a)
                            erefl erefl erefl erefl erefl.
End gluing.

CodeGen Snippet "#include <stdbool.h> /* for bool, true and false */".

CodeGen Inductive Type bool => "bool".
CodeGen Inductive Match bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

CodeGen Snippet "#include <stdint.h>".
CodeGen Snippet "#include <stdio.h>".
CodeGen Snippet "typedef uint64_t nat;".
CodeGen Snippet "typedef uint32_t positive;".
CodeGen Snippet "typedef uint32_t N;".
CodeGen Snippet "#define succ(n) ((n)+1)".
CodeGen Snippet "#define succn(n) ((n)+1)".
CodeGen Snippet "#define predn(n) ((n)-1)".
CodeGen Snippet "#define xH() (1)".
CodeGen Snippet "#define xO(n) (2*(n))".
CodeGen Snippet "#define xI(n) (2*(n)+1)".
CodeGen Snippet "#define add(n, m) ((n) + (m))".
CodeGen Snippet "#define subn(n, m) ((n) - (m))".
CodeGen Snippet "#define modulo(n, m) ((n) % (m))".
CodeGen Snippet "#define lxor(n, m) ((n) ^ (m))".
CodeGen Snippet "#define lor(n, m) ((n) | (m))".
CodeGen Snippet "#define land(n, m) ((n) & (m))".
CodeGen Snippet "#define testbit(n1,n2) ((n1)&(1<<(n2)))".
CodeGen Snippet "#define nat_of_bin(n) ((nat)(n))".
CodeGen Snippet "#define N0() (0)".
CodeGen Snippet "#define Npos(n) ((nat)(n))".
CodeGen Snippet "#define shiftl(n1,n2) ((n1)<<(n2))".
CodeGen Snippet "#define shiftr(n1,n2) ((n1)>>(n2))".

CodeGen Inductive Type nat => "nat".
CodeGen Inductive Match nat => ""
| O => "case 0"
| S => "default" "predn".
CodeGen Primitive S => "succn".

CodeGen Snippet "#define LARGE_NUM 1000".
CodeGen Snippet "
typedef struct {
  N list[LARGE_NUM];
  int index;
} list_N;
".

CodeGen Snippet "
typedef struct {
  N index;
  list_N state_vector;
} rand_state;
".

CodeGen Snippet "
rand_state Build_random_state(N index, list_N list) {
  rand_state r = {index,list};
  return r;
}
".

CodeGen Snippet "#define INDEX(x)        ((x).index)".
CodeGen Snippet "#define STATE_VECTOR(x) ((x).state_vector)".

CodeGen Inductive Type mt.random_state => "rand_state".
CodeGen Primitive mt.index => "INDEX".
CodeGen Primitive mt.state_vector => "STATE_VECTOR".

CodeGen Snippet "
typedef struct {
  nat fst;
  rand_state snd;
} prodNrnd;
".
CodeGen Snippet "#define make_prodNrnd(x, y) ((prodNrnd){ (x), (y) })".

CodeGen Inductive Type N * mt.random_state => "prodNrnd".
CodeGen Primitive pair N mt.random_state => "make_prodNrnd".

CodeGen Snippet "
N nth(N default_value, list_N l, N index) {
  return l.list[index];
}
".

CodeGen Snippet "
list_N set_nth(N default_value, list_N l, N index, N value) {
  l.list[index] = value;
  return l;
}
".

CodeGen Function lower_mask.
CodeGen Function upper_mask.
CodeGen Function next_random_state.
CodeGen Function tempering.

CodeGen Snippet "
rand_state initialize_random_state(int s)
{
    static list_N mt;
    int mti;
    mt.list[0]= s & 0xffffffffUL;
    for (mti=1; mti<LARGE_NUM; mti++) {
        mt.list[mti] =
	    (1812433253UL * (mt.list[mti-1] ^ (mt.list[mti-1] >> 30)) + mti);
        mt.list[mti] &= 0xffffffffUL;
    }
    return Build_random_state(0, mt);
}
".

CodeGen Snippet "
int main(void) {
  int seed = 20190820;
  rand_state r = initialize_random_state(seed);
  int i;
  for (i = 0; i < 2048; ++i) {
    prodNrnd p = next_random_state(r);
    printf(""%d:%u\n"", i, tempering(p.fst));
    r = p.snd;
  }
  return 0;
}
".

CodeGen GenerateFile "./mt19937_generated.c".
