static
prod_N_random_state
n2_next(N v0_a, random_state v1_rand)
{
  nat v2_i = n1_index(v1_rand);
  nat v3_n = n0_O();
  nat v4_n = n1_S(v3_n);
  nat v5_n = n2_add(v2_i, v4_n);
  nat v6_n = n0_n();
  nat v7_i1 = n2_modulo(v5_n, v6_n);
  list_N v8_s = n1_state(v1_rand);
  N v9_n = n2_nth_state_vector(v8_s, v2_i);
  N v10_n = n0_upper_mask();
  N v11_n = n2_land_0(v9_n, v10_n);
  N v12_n = n2_nth_state_vector(v8_s, v7_i1);
  N v13_n = n0_lower_mask();
  N v14_n = n2_land_0(v12_n, v13_n);
  N v15_z = n2_lor_0(v11_n, v14_n);
  nat v16_n = n0_m();
  nat v17_n = n2_add(v2_i, v16_n);
  nat v18_n = n0_n();
  nat v19_im = n2_modulo(v17_n, v18_n);
  N v20_n = n2_nth_state_vector(v8_s, v19_im);
  positive v21_p = n0_xH();
  N v22_n = n1_Npos(v21_p);
  N v23_n = n2_shiftr(v15_z, v22_n);
  N v24_n = n2_lxor_0(v20_n, v23_n);
  positive v25_p = n0_xH();
  N v26_n = n1_Npos(v25_p);
  N v27_n = n2_land_0(v15_z, v26_n);
  N v28_n = n0_N0();
  bool v29_b = n2_eqb_0(v27_n, v28_n);
  N v30_n;
  switch (sw_bool(v29_b))
  {
    case_true_bool: { v30_n = n0_N0(); break; }
    case_false_bool: { v30_n = v0_a; break; }
  }
  N v31_xi = n2_lxor_0(v24_n, v30_n);
  list_N v32_l = n3_set_nth_state_vector(v8_s, v2_i, v31_xi);
  random_state v33_next_rand = n2_Build_random_state(v7_i1, v32_l);
  return n2_pair_N_random_state(v31_xi, v33_next_rand);
}
static
list_N
n4_generate_aux(N v0_a, list_N v1_words, random_state v2_rand, nat v3_times)
{
  n4_generate_aux:;
  switch (sw_nat(v3_times))
  {
    case_O_nat: { return v1_words; }
    case_S_nat: {
      nat v4_m = field0_S_nat(v3_times);
      prod_N_random_state v5_p = n2_next(v0_a, v2_rand);
      N v6_nextValue = field0_pair_prod_N_random_state(v5_p);
      random_state v7_nextRand = field1_pair_prod_N_random_state(v5_p);
      nat v8_n = n0_n();
      nat v9_n = n0_p2n();
      nat v10_n = n2_subn(v9_n, v3_times);
      nat v11_n = n2_add(v8_n, v10_n);
      list_N v12_l = n3_set_nth_word_seq(v1_words, v11_n, v6_nextValue);
      v1_words = v12_l;
      v2_rand = v7_nextRand;
      v3_times = v4_m;
      goto n4_generate_aux;
    }
  }
}
static
list_N
n2_generate(N v0_a, list_N v1_state)
{
  random_state v2_rand = n1_make_mtRand(v1_state);
  list_N v3_start_word_seq = n1_word_seq_of_state_vector(v1_state);
  nat v4_n = n0_p2n();
  return n4_generate_aux(v0_a, v3_start_word_seq, v2_rand, v4_n);
}
static
list_N
n3_decimate_aux(list_N v0_words, list_N v1_acc, nat v2_times)
{
  n3_decimate_aux:;
  switch (sw_nat(v2_times))
  {
    case_O_nat: { return v1_acc; }
    case_S_nat: {
      nat v3_times_ = field0_S_nat(v2_times);
      nat v4_n = n0_p();
      nat v5_n = n2_sub(v4_n, v2_times);
      nat v6_n = n0_O();
      nat v7_n = n1_S(v6_n);
      nat v8_j = n2_add(v5_n, v7_n);
      nat v9_n = n0_O();
      nat v10_n = n1_S(v9_n);
      nat v11_n = n1_S(v10_n);
      nat v12_n = n2_muln(v11_n, v8_j);
      nat v13_n = n0_O();
      nat v14_n = n1_S(v13_n);
      nat v15_k = n2_sub(v12_n, v14_n);
      N v16_n = n2_nth_word_seq(v0_words, v15_k);
      list_N v17_l = n3_set_nth_word_seq(v1_acc, v8_j, v16_n);
      v1_acc = v17_l;
      v2_times = v3_times_;
      goto n3_decimate_aux;
    }
  }
}
static
list_N
n1_decimate(list_N v0_words)
{
  nat v1_n = n0_p(); return n3_decimate_aux(v0_words, v0_words, v1_n);
}
static
list_N
n3_process_aux(N v0_a, list_N v1_words, nat v2_times)
{
  n3_process_aux:;
  switch (sw_nat(v2_times))
  {
    case_O_nat: { return v1_words; }
    case_S_nat: {
      nat v3_times_ = field0_S_nat(v2_times);
      nat v4_n = n0_n();
      nat v5_n = n0_O();
      nat v6_n = n1_S(v5_n);
      nat v7_n = n2_sub(v4_n, v6_n);
      nat v8_k = n2_add(v2_times, v7_n);
      N v9_xk = n2_nth_word_seq(v1_words, v8_k);
      nat v10_n = n0_n();
      nat v11_kn = n2_sub(v8_k, v10_n);
      N v12_xkn = n2_nth_word_seq(v1_words, v11_kn);
      nat v13_n = n0_m();
      nat v14_knm = n2_add(v11_kn, v13_n);
      N v15_xknm = n2_nth_word_seq(v1_words, v14_knm);
      nat v16_n = n0_O();
      nat v17_n = n1_S(v16_n);
      nat v18_kn1 = n2_add(v11_kn, v17_n);
      N v19_xkn1 = n2_nth_word_seq(v1_words, v18_kn1);
      N v20_n = n2_lxor_0(v9_xk, v15_xknm);
      positive v21_p = n0_xH();
      N v22_n = n1_Npos(v21_p);
      N v23_n = n2_land_0(v19_xkn1, v22_n);
      N v24_n = n0_N0();
      bool v25_b = n2_eqb_0(v23_n, v24_n);
      N v26_n;
      switch (sw_bool(v25_b))
      {
        case_true_bool: { v26_n = n0_N0(); break; }
        case_false_bool: { v26_n = v0_a; break; }
      }
      N v27_y = n2_lxor_0(v20_n, v26_n);
      positive v28_p = n0_xH();
      N v29_n = n1_Npos(v28_p);
      N v30_y1 = n2_shiftl_0(v27_y, v29_n);
      positive v31_p = n0_xH();
      N v32_n = n1_Npos(v31_p);
      N v33_n = n2_land_0(v19_xkn1, v32_n);
      N v34_n = n0_N0();
      bool v35_b = n2_eqb_0(v33_n, v34_n);
      N v36_y2;
      switch (sw_bool(v35_b))
      {
        case_true_bool: {
          N v37_n = n0_bottom_zero_mask();
          v36_y2 = n2_land_0(v30_y1, v37_n);
          break;
        }
        case_false_bool: {
          N v38_n = n0_bottom_one_mask();
          v36_y2 = n2_lor_0(v30_y1, v38_n);
          break;
        }
      }
      N v39_n = n0_upper_mask();
      N v40_n = n2_land_0(v39_n, v19_xkn1);
      N v41_n = n0_lower_mask();
      N v42_n = n2_land_0(v41_n, v36_y2);
      N v43_newxkn1 = n2_lor_0(v40_n, v42_n);
      N v44_n = n0_upper_mask();
      N v45_n = n2_land_0(v44_n, v36_y2);
      N v46_n = n0_lower_mask();
      N v47_n = n2_land_0(v46_n, v12_xkn);
      N v48_newxkn = n2_lor_0(v45_n, v47_n);
      list_N
      v49_words1
      =
      n3_set_nth_word_seq(v1_words,
      v18_kn1,
      v43_newxkn1);
      list_N
      v50_words2
      =
      n3_set_nth_word_seq(v49_words1,
      v11_kn,
      v48_newxkn);
      v1_words = v50_words2;
      v2_times = v3_times_;
      goto n3_process_aux;
    }
  }
}
static
list_N
n2_process(N v0_a, list_N v1_state)
{
  list_N v2_expandedWords = n2_generate(v0_a, v1_state);
  list_N v3_decimatedWords = n1_decimate(v2_expandedWords);
  nat v4_n = n0_p();
  nat v5_n = n0_n();
  nat v6_n = n0_O();
  nat v7_n = n1_S(v6_n);
  nat v8_n = n2_sub(v5_n, v7_n);
  nat v9_pn1 = n2_sub(v4_n, v8_n);
  list_N v10_l = n3_process_aux(v0_a, v3_decimatedWords, v9_pn1);
  return n1_state_vector_of_word_seq(v10_l);
}
static
list_N
n3_recursive_process(N v0_a, list_N v1_state, nat v2_times)
{
  n3_recursive_process:;
  switch (sw_nat(v2_times))
  {
    case_O_nat: { return v1_state; }
    case_S_nat: {
      nat v3_times_ = field0_S_nat(v2_times);
      list_N v4_l = n2_process(v0_a, v1_state);
      v1_state = v4_l;
      v2_times = v3_times_;
      goto n3_recursive_process;
    }
  }
}
static
bool
n3_check_aux(list_N v0_initial_state, list_N v1_last_state, nat v2_index)
{
  switch (sw_nat(v2_index))
  {
    case_O_nat: { return n0_true(); }
    case_S_nat: {
      nat v3_index_ = field0_S_nat(v2_index);
      N v4_n = n2_nth_state_vector(v0_initial_state, v2_index);
      N v5_n = n2_nth_state_vector(v1_last_state, v2_index);
      bool v6_b = n2_eqb_0(v4_n, v5_n);
      bool v7_b = n3_check_aux(v0_initial_state, v1_last_state, v3_index_);
      return n2_andb(v6_b, v7_b);
    }
  }
}
static
bool
n2_check(list_N v0_initial_state, list_N v1_last_state)
{
  N v2_n = n0_upper_mask();
  nat v3_n = n0_O();
  N v4_n = n2_nth_state_vector(v0_initial_state, v3_n);
  N v5_n = n2_land_0(v2_n, v4_n);
  N v6_n = n0_upper_mask();
  nat v7_n = n0_O();
  N v8_n = n2_nth_state_vector(v1_last_state, v7_n);
  N v9_n = n2_land_0(v6_n, v8_n);
  bool v10_b = n2_eqb_0(v5_n, v9_n);
  nat v11_n = n0_n();
  nat v12_n = n0_O();
  nat v13_n = n1_S(v12_n);
  nat v14_n = n2_sub(v11_n, v13_n);
  bool v15_b = n3_check_aux(v0_initial_state, v1_last_state, v14_n);
  return n2_andb(v10_b, v15_b);
}
static
bool
n1_test(N v0_a)
{
  list_N v1_l = n0_initial_state();
  list_N v2_l = n0_start_state();
  nat v3_n = n0_p();
  list_N v4_l = n3_recursive_process(v0_a, v2_l, v3_n);
  return n2_check(v1_l, v4_l);
}
