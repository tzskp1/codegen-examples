list_N
n2_generate_state_vector(nat v1_rest, list_N v0_acc)
{
  n2_generate_state_vector:;
  switch (sw_nat(v1_rest))
  {
    case_O_nat: { return v0_acc; }
    case_S_nat: {
      nat v3_m = field0_S_nat(v1_rest);
      switch (sw_nat(v3_m))
      {
        case_O_nat: { return v0_acc; }
        case_S_nat: {
          nat v4_n = field0_S_nat(v3_m);
          positive v5_p = n0_xH();
          positive v6_p = n1_xI(v5_p);
          positive v7_p = n1_xO(v6_p);
          positive v8_p = n1_xI(v7_p);
          positive v9_p = n1_xI(v8_p);
          positive v10_p = n1_xO(v9_p);
          positive v11_p = n1_xO(v10_p);
          positive v12_p = n1_xO(v11_p);
          positive v13_p = n1_xO(v12_p);
          positive v14_p = n1_xO(v13_p);
          positive v15_p = n1_xO(v14_p);
          positive v16_p = n1_xO(v15_p);
          positive v17_p = n1_xI(v16_p);
          positive v18_p = n1_xI(v17_p);
          positive v19_p = n1_xI(v18_p);
          positive v20_p = n1_xI(v19_p);
          positive v21_p = n1_xO(v20_p);
          positive v22_p = n1_xO(v21_p);
          positive v23_p = n1_xO(v22_p);
          positive v24_p = n1_xI(v23_p);
          positive v25_p = n1_xO(v24_p);
          positive v26_p = n1_xO(v25_p);
          positive v27_p = n1_xI(v26_p);
          positive v28_p = n1_xO(v27_p);
          positive v29_p = n1_xI(v28_p);
          positive v30_p = n1_xI(v29_p);
          positive v31_p = n1_xO(v30_p);
          positive v32_p = n1_xO(v31_p);
          positive v33_p = n1_xI(v32_p);
          positive v34_p = n1_xO(v33_p);
          positive v35_p = n1_xI(v34_p);
          N v36_n = n1_Npos(v35_p);
          N v37_n = n0_N0();
          N v38_n = n2_head_N(v37_n, v0_acc);
          N v39_n = n0_N0();
          N v40_n = n2_head_N(v39_n, v0_acc);
          positive v41_p = n0_xH();
          positive v42_p = n1_xI(v41_p);
          positive v43_p = n1_xI(v42_p);
          positive v44_p = n1_xI(v43_p);
          positive v45_p = n1_xO(v44_p);
          N v46_n = n1_Npos(v45_p);
          N v47_n = n2_shiftr(v40_n, v46_n);
          N v48_n = n2_lxor(v38_n, v47_n);
          N v49_n = n2_mul_0(v36_n, v48_n);
          nat v50_n = n0_len();
          nat v51_n = n2_subn(v50_n, v1_rest);
          N v52_n = n1_of_nat(v51_n);
          N v53_n = n2_add_0(v49_n, v52_n);
          positive v54_p = n0_xH();
          N v55_n = n1_Npos(v54_p);
          N v56_n = n2_add_0(v53_n, v55_n);
          N v57_n = n0_whole_mask();
          N v58_n = n2_land(v56_n, v57_n);
          list_N v59_l = n2_cons_N(v58_n, v0_acc);
          v1_rest = v3_m;
          v0_acc = v59_l;
          goto n2_generate_state_vector;
        }
      }
    }
  }
}
random_state
n1_initialize_random_state(N v60_seed)
{
  nat v61_n = n0_O();
  nat v62_n = n0_len();
  N v63_n = n0_whole_mask();
  N v64_n = n2_land(v60_seed, v63_n);
  list_N v65_l = n0_nil_N();
  list_N v66_l = n2_cons_N(v64_n, v65_l);
  list_N v67_l = n2_generate_state_vector(v62_n, v66_l);
  list_N v68_l = n1_rev_N(v67_l);
  return n2_Build_random_state(v61_n, v68_l);
}
prod_N_random_state
n1_next_random_state(random_state v69_rand)
{
  list_N v70_state_vec = n1_state_vector(v69_rand);
  nat v71_ind = n1_index(v69_rand);
  N v72_n = n0_N0();
  N v73_current = n3_nth_N(v72_n, v70_state_vec, v71_ind);
  nat v74_n = n0_O();
  nat v75_n = n1_S(v74_n);
  nat v76_n = n2_addn(v71_ind, v75_n);
  nat v77_n = n0_len();
  nat v78_next_ind = n2_modulo(v76_n, v77_n);
  N v79_n = n0_N0();
  N v80_next = n3_nth_N(v79_n, v70_state_vec, v78_next_ind);
  nat v81_n = n0_m();
  nat v82_n = n2_addn(v71_ind, v81_n);
  nat v83_n = n0_len();
  nat v84_far_ind = n2_modulo(v82_n, v83_n);
  N v85_n = n0_N0();
  N v86_far = n3_nth_N(v85_n, v70_state_vec, v84_far_ind);
  N v87_n = n0_upper_mask();
  N v88_n = n2_land(v73_current, v87_n);
  N v89_n = n0_lower_mask();
  N v90_n = n2_land(v80_next, v89_n);
  N v91_z = n2_lor(v88_n, v90_n);
  positive v92_p = n0_xH();
  N v93_n = n1_Npos(v92_p);
  N v94_n = n2_shiftr(v91_z, v93_n);
  N v95_n = n2_lxor(v86_far, v94_n);
  positive v96_p = n0_xH();
  N v97_n = n1_Npos(v96_p);
  N v98_n = n2_land(v91_z, v97_n);
  N v99_n = n0_N0();
  bool v100_b = n2_eqb_0(v98_n, v99_n);
  N v101_n;
  switch (sw_bool(v100_b))
  {
    case_true_bool: { v101_n = n0_N0(); break; }
    case_false_bool: { v101_n = n0_a(); break; }
  }
  N v102_xi = n2_lxor(v95_n, v101_n);
  N v103_n = n0_u();
  N v104_n = n2_shiftr(v102_xi, v103_n);
  N v105_y1 = n2_lxor(v102_xi, v104_n);
  N v106_n = n0_s();
  N v107_n = n2_shiftl(v105_y1, v106_n);
  N v108_n = n0_b();
  N v109_n = n2_land(v107_n, v108_n);
  N v110_y2 = n2_lxor(v105_y1, v109_n);
  N v111_n = n0_t();
  N v112_n = n2_shiftl(v110_y2, v111_n);
  N v113_n = n0_c();
  N v114_n = n2_land(v112_n, v113_n);
  N v115_y3 = n2_lxor(v110_y2, v114_n);
  N v116_n = n0_l();
  N v117_n = n2_shiftr(v115_y3, v116_n);
  N v118_y4 = n2_lxor(v115_y3, v117_n);
  N v119_n = n0_N0();
  list_N v120_l = n4_set_nth_N(v119_n, v70_state_vec, v71_ind, v102_xi);
  random_state v121_next_rand = n2_Build_random_state(v78_next_ind, v120_l);
  return n2_pair_N_random_state(v118_y4, v121_next_rand);
}
N
n2_nth_rand(nat v123_n, random_state v122_rand)
{
  n2_nth_rand:;
  prod_N_random_state v125_p = n1_next_random_state(v122_rand);
  N v126_r = field0_pair_prod_N_random_state(v125_p);
  random_state v127_next_state = field1_pair_prod_N_random_state(v125_p);
  switch (sw_nat(v123_n))
  {
    case_O_nat: { return v126_r; }
    case_S_nat: {
      nat v128_m = field0_S_nat(v123_n);
      v123_n = v128_m;
      v122_rand = v127_next_state;
      goto n2_nth_rand;
    }
  }
}
N
n2_nth_rand_with_seed(nat v130_n, N v129_seed)
{
  random_state v131_rand = n1_initialize_random_state(v129_seed);
  return n2_nth_rand(v130_n, v131_rand);
}
