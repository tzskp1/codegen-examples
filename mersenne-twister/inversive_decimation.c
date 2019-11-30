#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include <stdbool.h>
#define n0_true() true
#define n0_false() false
#define sw_bool(b) (b)
#define case_true_bool default
#define case_false_bool case false
#define n2_andb(a,b) ((a)&&(b))
#define n2_orb(a,b) ((a)||(b))

#define nat uint64_t
#define n0_O() ((nat)0)
#define n1_S(n) ((n)+1)
#define sw_nat(n) (n)
#define case_O_nat case 0
#define case_S_nat default
#define field0_S_nat(n) ((n)-1)

#define N uint32_t
#define n0_N0() 0
#define n2_land_0(n1,n2) ((n1)&(n2))
#define n2_lor_0(n1,n2) ((n1)|(n2))
#define n2_lxor_0(n1,n2) ((n1)^(n2))
#define n2_shiftl_0(n1,n2) ((n1)<<(n2))
#define n2_shiftr(n1,n2) ((n1)>>(n2))
#define n2_eqb_0(n1,n2) ((n1)==(n2))
#define n1_of_nat(n) ((uint32_t)n)

#define positive uint32_t
#define n0_xH() 1
#define n1_xO(n) (2*(n))
#define n1_xI(n) (2*(n)+1)
#define n1_Npos(n) n

#define n2_add(a,b) ((a)+(b))
#define n2_sub(a,b) ((a)-(b))
#define n2_mul(a,b) ((a)*(b))
#define n2_div(a,b) ((a)/(b))

#define n2_addn(a,b) ((a)+(b))
#define n2_subn(a,b) ((a)-(b))
#define n2_muln(a,b) ((a)*(b))
#define n2_divn(a,b) ((a)/(b))
#define n2_modulo(a,b) ((a)%(b))

#define n2_add_0(a,b) ((a)+(b))
#define n2_sub_0(a,b) ((a)-(b))
#define n2_mul_0(a,b) ((a)*(b))
#define n2_div_0(a,b) ((a)/(b))

#define n0_w() 32
#define n0_n() 624
#define n0_m() 397
#define n0_r() 31

#define n0_p() (n0_w() * n0_n() - n0_r())

#define n0_upper_mask() 2147483648
#define n0_lower_mask() (n0_upper_mask() - 1)

#define n0_bottom_zero_mask() (2 * n0_upper_mask() - 2)
#define n0_bottom_one_mask() 1

#define n0_len() (n0_p() * 2)

#define n0_p2n() (2 * n0_p() - n0_n())

typedef N* list_N;

N n2_nth_word_seq(list_N l, nat index) {
  return l[index];
}

list_N n3_set_nth_word_seq(list_N l, nat index, N value) {
  l[index] = value;
  return l;
}

N n2_nth_state_vector(list_N l, nat index) {
  return l[index];
}

list_N n3_set_nth_state_vector(list_N l, nat index, N value) {
  l[index] = value;
  return l;
}

void init(list_N l) {
  for (int i = 0; i < n0_n(); ++i) {
    l[i] = i;
  }
}

N g_state[n0_len()];

list_N n0_start_state() {
  init(g_state);
  return g_state;
}

N g_initial_state[n0_n()];

list_N n0_initial_state() {
  init(g_initial_state);
  return g_initial_state;
}

struct rand_state {
  nat index;
  list_N state;
};

#define random_state struct rand_state

N g_state_vector[n0_n()];

random_state g_rand = {0,g_state_vector};

list_N n1_state_vector_of_word_seq(list_N word_seq) {
  return word_seq;
}

list_N n1_word_seq_of_state_vector(list_N state_vector) {
  return state_vector;
}

random_state n2_Build_random_state(nat index, list_N state) {
  g_rand.index = index;
  return g_rand;
}

nat n1_index(random_state rand) {
  return rand.index;
}

list_N n1_state(random_state rand) {
  return rand.state;
}

random_state n1_make_mtRand(list_N state) {
  g_rand.index = 0;
  for (int i = 0; i < n0_n(); ++i) {
    g_rand.state[i] = state[i];
  }
  return g_rand;
}

struct prod_n_random_state {
  N n;
  random_state r;
};

#define prod_N_random_state struct prod_n_random_state

prod_N_random_state n2_pair_N_random_state(N n, random_state r) {
  prod_N_random_state x = {n,r};
  return x;
}

#define field0_pair_prod_N_random_state(p) (p).n
#define field1_pair_prod_N_random_state(p) (p).r

#include "inversive_decimation_generated.c"

int main(void) {
  N a = 2567483615;
  if (n1_test(a)) {
    puts("ok");
  } else {
    puts("ng");
  }
  return 0;
}


