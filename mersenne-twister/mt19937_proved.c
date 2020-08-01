#include <stdbool.h> /* for bool, true and false */

#include <stdint.h>

#include <stdio.h>

typedef uint64_t nat;

typedef uint32_t positive;

typedef uint32_t N;

#define succ(n) ((n)+1)

#define succn(n) ((n)+1)

#define predn(n) ((n)-1)

#define xH() (1)

#define xO(n) (2*(n))

#define xI(n) (2*(n)+1)

#define add(n, m) ((n) + (m))

#define subn(n, m) ((n) - (m))

#define modulo(n, m) ((n) % (m))

#define lxor(n, m) ((n) ^ (m))

#define lor(n, m) ((n) | (m))

#define land(n, m) ((n) & (m))

#define testbit(n1,n2) ((n1)&(1<<(n2)))

#define nat_of_bin(n) ((nat)(n))

#define N0() (0)

#define Npos(n) ((nat)(n))

#define shiftl(n1,n2) ((n1)<<(n2))

#define shiftr(n1,n2) ((n1)>>(n2))

#define LARGE_NUM 1000

 typedef struct {   N list[LARGE_NUM];   int index; } list_N; 

 typedef struct {   N index;   list_N state_vector; } rand_state; 

 rand_state Build_random_state(N index, list_N list) {   rand_state r = {index,list};   return r; } 

#define INDEX(x)        ((x).index)

#define STATE_VECTOR(x) ((x).state_vector)

 typedef struct {   nat fst;   rand_state snd; } prodNrnd; 

#define make_prodNrnd(x, y) ((prodNrnd){ (x), (y) })

 N nth(N default_value, list_N l, N index) {   return l.list[index]; } 

 list_N set_nth(N default_value, list_N l, N index, N value) {   l.list[index] = value;   return l; } 

static N
lower_mask(void)
{
  positive v1_p;
  positive v2_p;
  positive v3_p;
  positive v4_p;
  positive v5_p;
  positive v6_p;
  positive v7_p;
  positive v8_p;
  positive v9_p;
  positive v10_p;
  positive v11_p;
  positive v12_p;
  positive v13_p;
  positive v14_p;
  positive v15_p;
  positive v16_p;
  positive v17_p;
  positive v18_p;
  positive v19_p;
  positive v20_p;
  positive v21_p;
  positive v22_p;
  positive v23_p;
  positive v24_p;
  positive v25_p;
  positive v26_p;
  positive v27_p;
  positive v28_p;
  positive v29_p;
  positive v30_p;
  positive v31_p;
  v1_p = xH();
  v2_p = xI(v1_p);
  v3_p = xI(v2_p);
  v4_p = xI(v3_p);
  v5_p = xI(v4_p);
  v6_p = xI(v5_p);
  v7_p = xI(v6_p);
  v8_p = xI(v7_p);
  v9_p = xI(v8_p);
  v10_p = xI(v9_p);
  v11_p = xI(v10_p);
  v12_p = xI(v11_p);
  v13_p = xI(v12_p);
  v14_p = xI(v13_p);
  v15_p = xI(v14_p);
  v16_p = xI(v15_p);
  v17_p = xI(v16_p);
  v18_p = xI(v17_p);
  v19_p = xI(v18_p);
  v20_p = xI(v19_p);
  v21_p = xI(v20_p);
  v22_p = xI(v21_p);
  v23_p = xI(v22_p);
  v24_p = xI(v23_p);
  v25_p = xI(v24_p);
  v26_p = xI(v25_p);
  v27_p = xI(v26_p);
  v28_p = xI(v27_p);
  v29_p = xI(v28_p);
  v30_p = xI(v29_p);
  v31_p = xI(v30_p);
  return Npos(v31_p);
}

static N
upper_mask(void)
{
  positive v1_p;
  positive v2_p;
  positive v3_p;
  positive v4_p;
  positive v5_p;
  positive v6_p;
  positive v7_p;
  positive v8_p;
  positive v9_p;
  positive v10_p;
  positive v11_p;
  positive v12_p;
  positive v13_p;
  positive v14_p;
  positive v15_p;
  positive v16_p;
  positive v17_p;
  positive v18_p;
  positive v19_p;
  positive v20_p;
  positive v21_p;
  positive v22_p;
  positive v23_p;
  positive v24_p;
  positive v25_p;
  positive v26_p;
  positive v27_p;
  positive v28_p;
  positive v29_p;
  positive v30_p;
  positive v31_p;
  positive v32_p;
  v1_p = xH();
  v2_p = xO(v1_p);
  v3_p = xO(v2_p);
  v4_p = xO(v3_p);
  v5_p = xO(v4_p);
  v6_p = xO(v5_p);
  v7_p = xO(v6_p);
  v8_p = xO(v7_p);
  v9_p = xO(v8_p);
  v10_p = xO(v9_p);
  v11_p = xO(v10_p);
  v12_p = xO(v11_p);
  v13_p = xO(v12_p);
  v14_p = xO(v13_p);
  v15_p = xO(v14_p);
  v16_p = xO(v15_p);
  v17_p = xO(v16_p);
  v18_p = xO(v17_p);
  v19_p = xO(v18_p);
  v20_p = xO(v19_p);
  v21_p = xO(v20_p);
  v22_p = xO(v21_p);
  v23_p = xO(v22_p);
  v24_p = xO(v23_p);
  v25_p = xO(v24_p);
  v26_p = xO(v25_p);
  v27_p = xO(v26_p);
  v28_p = xO(v27_p);
  v29_p = xO(v28_p);
  v30_p = xO(v29_p);
  v31_p = xO(v30_p);
  v32_p = xO(v31_p);
  return Npos(v32_p);
}

static prodNrnd
next_random_state(rand_state v1_rand)
{
  list_N v2_state_vec;
  N v3_ind;
  N v4_n;
  nat v5_n;
  N v6_current;
  N v7_n;
  N v8_n;
  N v9_next_ind;
  N v10_n;
  nat v11_n;
  N v12_next;
  N v13_n;
  N v14_n;
  N v15_n;
  N v16_far_ind;
  N v17_n;
  nat v18_n;
  N v19_far;
  N v20_n;
  N v21_n;
  N v22_n;
  N v23_n;
  N v24_z;
  positive v25_p;
  N v26_n;
  N v27_n;
  N v28_n;
  N v29_n;
  bool v30_b;
  N v31_n;
  N v32_xi;
  N v33_n;
  nat v34_n;
  list_N v35_l;
  rand_state v36_next_rand;
  v2_state_vec = STATE_VECTOR(v1_rand);
  v3_ind = INDEX(v1_rand);
  v4_n = N0();
  v5_n = nat_of_bin(v3_ind);
  v6_current = nth(v4_n, v2_state_vec, v5_n);
  v7_n = succ(v3_ind);
  v8_n = len();
  v9_next_ind = modulo(v7_n, v8_n);
  v10_n = N0();
  v11_n = nat_of_bin(v9_next_ind);
  v12_next = nth(v10_n, v2_state_vec, v11_n);
  v13_n = m();
  v14_n = add(v3_ind, v13_n);
  v15_n = len();
  v16_far_ind = modulo(v14_n, v15_n);
  v17_n = N0();
  v18_n = nat_of_bin(v16_far_ind);
  v19_far = nth(v17_n, v2_state_vec, v18_n);
  v20_n = upper_mask();
  v21_n = land(v6_current, v20_n);
  v22_n = lower_mask();
  v23_n = land(v12_next, v22_n);
  v24_z = lor(v21_n, v23_n);
  v25_p = xH();
  v26_n = Npos(v25_p);
  v27_n = shiftr(v24_z, v26_n);
  v28_n = lxor(v19_far, v27_n);
  v29_n = N0();
  v30_b = testbit(v24_z, v29_n);
  switch (v30_b)
  {
    default:
      v31_n = a();
      break;
    case 0:
      v31_n = N0();
      break;
  }
  v32_xi = lxor(v28_n, v31_n);
  v33_n = N0();
  v34_n = nat_of_bin(v3_ind);
  v35_l = set_nth(v33_n, v2_state_vec, v34_n, v32_xi);
  v36_next_rand = Build_random_state(v9_next_ind, v35_l);
  return make_prodNrnd(v32_xi, v36_next_rand);
}

static N
tempering(N v1_xi)
{
  N v2_n;
  N v3_n;
  N v4_y1;
  N v5_n;
  N v6_n;
  N v7_n;
  N v8_n;
  N v9_y2;
  N v10_n;
  N v11_n;
  N v12_n;
  N v13_n;
  N v14_y3;
  N v15_n;
  N v16_n;
  v2_n = u();
  v3_n = shiftr(v1_xi, v2_n);
  v4_y1 = lxor(v1_xi, v3_n);
  v5_n = s();
  v6_n = shiftl(v4_y1, v5_n);
  v7_n = b();
  v8_n = land(v6_n, v7_n);
  v9_y2 = lxor(v4_y1, v8_n);
  v10_n = t();
  v11_n = shiftl(v9_y2, v10_n);
  v12_n = c();
  v13_n = land(v11_n, v12_n);
  v14_y3 = lxor(v9_y2, v13_n);
  v15_n = l();
  v16_n = shiftr(v14_y3, v15_n);
  return lxor(v14_y3, v16_n);
}

 rand_state initialize_random_state(int s) {     static list_N mt;     int mti;     mt.list[0]= s & 0xffffffffUL;     for (mti=1; mti<LARGE_NUM; mti++) {         mt.list[mti] = 	    (1812433253UL * (mt.list[mti-1] ^ (mt.list[mti-1] >> 30)) + mti);         mt.list[mti] &= 0xffffffffUL;     }     return Build_random_state(0, mt); } 

 int main(void) {   int seed = 20190820;   rand_state r = initialize_random_state(seed);   int i;   for (i = 0; i < 2048; ++i) {     prodNrnd p = next_random_state(r);     printf("%d:%u\n", i, tempering(p.fst));     r = p.snd;   }   return 0; } 

