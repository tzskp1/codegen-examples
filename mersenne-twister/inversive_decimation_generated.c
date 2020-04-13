prod_N_random_state
n2_next(N v1_a, random_state v0_rand)
{
  nat v2_i = n1_index(v0_rand);
  nat v3_n = n0_O();
  nat v4_n = n1_S(v3_n);
  nat v5_n = n2_add(v2_i, v4_n);
  nat v6_n = n0_n();
  nat v7_i1 = n2_modulo(v5_n, v6_n);
  list_N v8_s = n1_state(v0_rand);
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
    case_false_bool: { v30_n = v1_a; break; }
  }
  N v31_xi = n2_lxor_0(v24_n, v30_n);
  list_N v32_l = n3_set_nth_state_vector(v8_s, v2_i, v31_xi);
  random_state v33_next_rand = n2_Build_random_state(v7_i1, v32_l);
  return n2_pair_N_random_state(v31_xi, v33_next_rand);
}
list_N
n4_generate_aux(N v37_a,
                list_N v36_words,
                random_state v35_rand,
                nat v34_times)
{
  n4_generate_aux:;
  switch (sw_nat(v34_times))
  {
    case_O_nat: { return v36_words; }
    case_S_nat: {
      nat v39_m = field0_S_nat(v34_times);
      prod_N_random_state v40_p = n2_next(v37_a, v35_rand);
      N v41_nextValue = field0_pair_prod_N_random_state(v40_p);
      random_state v42_nextRand = field1_pair_prod_N_random_state(v40_p);
      nat v43_n = n0_n();
      nat v44_n = n0_p2n();
      nat v45_n = n2_subn(v44_n, v34_times);
      nat v46_n = n2_add(v43_n, v45_n);
      list_N v47_l = n3_set_nth_word_seq(v36_words, v46_n, v41_nextValue);
      v36_words = v47_l;
      v35_rand = v42_nextRand;
      v34_times = v39_m;
      goto n4_generate_aux;
    }
  }
}
list_N
n2_generate(N v49_a, list_N v48_state)
{
  random_state v50_rand = n1_make_mtRand(v48_state);
  list_N v51_start_word_seq = n1_word_seq_of_state_vector(v48_state);
  nat v52_n = n0_p2n();
  return n4_generate_aux(v49_a, v51_start_word_seq, v50_rand, v52_n);
}
list_N
n3_decimate_aux(list_N v55_words, list_N v54_acc, nat v53_times)
{
  n3_decimate_aux:;
  switch (sw_nat(v53_times))
  {
    case_O_nat: { return v54_acc; }
    case_S_nat: {
      nat v57_times_ = field0_S_nat(v53_times);
      nat v58_n = n0_p();
      nat v59_n = n2_sub(v58_n, v53_times);
      nat v60_n = n0_O();
      nat v61_n = n1_S(v60_n);
      nat v62_j = n2_add(v59_n, v61_n);
      nat v63_n = n0_O();
      nat v64_n = n1_S(v63_n);
      nat v65_n = n1_S(v64_n);
      nat v66_n = n2_muln(v65_n, v62_j);
      nat v67_n = n0_O();
      nat v68_n = n1_S(v67_n);
      nat v69_k = n2_sub(v66_n, v68_n);
      N v70_n = n2_nth_word_seq(v55_words, v69_k);
      list_N v71_l = n3_set_nth_word_seq(v54_acc, v62_j, v70_n);
      v54_acc = v71_l;
      v53_times = v57_times_;
      goto n3_decimate_aux;
    }
  }
}
list_N
n1_decimate(list_N v72_words)
{
  nat v73_n = n0_p(); return n3_decimate_aux(v72_words, v72_words, v73_n);
}
list_N
n3_process_aux(N v76_a, list_N v75_words, nat v74_times)
{
  n3_process_aux:;
  switch (sw_nat(v74_times))
  {
    case_O_nat: { return v75_words; }
    case_S_nat: {
      nat v78_times_ = field0_S_nat(v74_times);
      nat v79_n = n0_n();
      nat v80_n = n0_O();
      nat v81_n = n1_S(v80_n);
      nat v82_n = n2_sub(v79_n, v81_n);
      nat v83_k = n2_add(v74_times, v82_n);
      N v84_xk = n2_nth_word_seq(v75_words, v83_k);
      nat v85_n = n0_n();
      nat v86_kn = n2_sub(v83_k, v85_n);
      N v87_xkn = n2_nth_word_seq(v75_words, v86_kn);
      nat v88_n = n0_m();
      nat v89_knm = n2_add(v86_kn, v88_n);
      N v90_xknm = n2_nth_word_seq(v75_words, v89_knm);
      nat v91_n = n0_O();
      nat v92_n = n1_S(v91_n);
      nat v93_kn1 = n2_add(v86_kn, v92_n);
      N v94_xkn1 = n2_nth_word_seq(v75_words, v93_kn1);
      N v95_n = n2_lxor_0(v84_xk, v90_xknm);
      positive v96_p = n0_xH();
      N v97_n = n1_Npos(v96_p);
      N v98_n = n2_land_0(v94_xkn1, v97_n);
      N v99_n = n0_N0();
      bool v100_b = n2_eqb_0(v98_n, v99_n);
      N v101_n;
      switch (sw_bool(v100_b))
      {
        case_true_bool: { v101_n = n0_N0(); break; }
        case_false_bool: { v101_n = v76_a; break; }
      }
      N v102_y = n2_lxor_0(v95_n, v101_n);
      positive v103_p = n0_xH();
      N v104_n = n1_Npos(v103_p);
      N v105_y1 = n2_shiftl_0(v102_y, v104_n);
      positive v106_p = n0_xH();
      N v107_n = n1_Npos(v106_p);
      N v108_n = n2_land_0(v94_xkn1, v107_n);
      N v109_n = n0_N0();
      bool v110_b = n2_eqb_0(v108_n, v109_n);
      N v111_y2;
      switch (sw_bool(v110_b))
      {
        case_true_bool: {
          N v112_n = n0_bottom_zero_mask();
          v111_y2 = n2_land_0(v105_y1, v112_n);
          break;
        }
        case_false_bool: {
          N v113_n = n0_bottom_one_mask();
          v111_y2 = n2_lor_0(v105_y1, v113_n);
          break;
        }
      }
      N v114_n = n0_upper_mask();
      N v115_n = n2_land_0(v114_n, v94_xkn1);
      N v116_n = n0_lower_mask();
      N v117_n = n2_land_0(v116_n, v111_y2);
      N v118_newxkn1 = n2_lor_0(v115_n, v117_n);
      N v119_n = n0_upper_mask();
      N v120_n = n2_land_0(v119_n, v111_y2);
      N v121_n = n0_lower_mask();
      N v122_n = n2_land_0(v121_n, v87_xkn);
      N v123_newxkn = n2_lor_0(v120_n, v122_n);
      list_N
      v124_words1
      =
      n3_set_nth_word_seq(v75_words,
      v93_kn1,
      v118_newxkn1);
      list_N
      v125_words2
      =
      n3_set_nth_word_seq(v124_words1,
      v86_kn,
      v123_newxkn);
      v75_words = v125_words2;
      v74_times = v78_times_;
      goto n3_process_aux;
    }
  }
}
list_N
n2_process(N v127_a, list_N v126_state)
{
  list_N v128_expandedWords = n2_generate(v127_a, v126_state);
  list_N v129_decimatedWords = n1_decimate(v128_expandedWords);
  nat v130_n = n0_p();
  nat v131_n = n0_n();
  nat v132_n = n0_O();
  nat v133_n = n1_S(v132_n);
  nat v134_n = n2_sub(v131_n, v133_n);
  nat v135_pn1 = n2_sub(v130_n, v134_n);
  list_N v136_l = n3_process_aux(v127_a, v129_decimatedWords, v135_pn1);
  return n1_state_vector_of_word_seq(v136_l);
}
list_N
n3_recursive_process(N v139_a, list_N v138_state, nat v137_times)
{
  n3_recursive_process:;
  switch (sw_nat(v137_times))
  {
    case_O_nat: { return v138_state; }
    case_S_nat: {
      nat v141_times_ = field0_S_nat(v137_times);
      list_N v142_l = n2_process(v139_a, v138_state);
      v138_state = v142_l;
      v137_times = v141_times_;
      goto n3_recursive_process;
    }
  }
}
bool
n3_check_aux(list_N v145_initial_state,
             list_N v144_last_state,
             nat v143_index)
{
  switch (sw_nat(v143_index))
  {
    case_O_nat: { return n0_true(); }
    case_S_nat: {
      nat v147_index_ = field0_S_nat(v143_index);
      N v148_n = n2_nth_state_vector(v145_initial_state, v143_index);
      N v149_n = n2_nth_state_vector(v144_last_state, v143_index);
      bool v150_b = n2_eqb_0(v148_n, v149_n);
      bool
      v151_b
      =
      n3_check_aux(v145_initial_state,
      v144_last_state,
      v147_index_);
      return n2_andb(v150_b, v151_b);
    }
  }
}
bool
n2_check(list_N v153_initial_state, list_N v152_last_state)
{
  N v154_n = n0_upper_mask();
  nat v155_n = n0_O();
  N v156_n = n2_nth_state_vector(v153_initial_state, v155_n);
  N v157_n = n2_land_0(v154_n, v156_n);
  N v158_n = n0_upper_mask();
  nat v159_n = n0_O();
  N v160_n = n2_nth_state_vector(v152_last_state, v159_n);
  N v161_n = n2_land_0(v158_n, v160_n);
  bool v162_b = n2_eqb_0(v157_n, v161_n);
  nat v163_n = n0_n();
  nat v164_n = n0_O();
  nat v165_n = n1_S(v164_n);
  nat v166_n = n2_sub(v163_n, v165_n);
  bool v167_b = n3_check_aux(v153_initial_state, v152_last_state, v166_n);
  return n2_andb(v162_b, v167_b);
}
bool
n1_test(N v168_a)
{
  list_N v169_l = n0_initial_state();
  list_N v170_l = n0_start_state();
  nat v171_n = n0_p();
  list_N v172_l = n3_recursive_process(v168_a, v170_l, v171_n);
  return n2_check(v169_l, v172_l);
}
