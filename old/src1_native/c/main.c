#include "runtime.h"

tll_ptr andb_i1(tll_ptr b1_v17911, tll_ptr b2_v17912);
tll_ptr orb_i2(tll_ptr b1_v17916, tll_ptr b2_v17917);
tll_ptr notb_i3(tll_ptr b_v17921);
tll_ptr compareb_i4(tll_ptr b1_v17923, tll_ptr b2_v17924);
tll_ptr lten_i5(tll_ptr x_v17928, tll_ptr y_v17929);
tll_ptr ltn_i6(tll_ptr x_v17933, tll_ptr y_v17934);
tll_ptr gten_i7(tll_ptr x_v17938, tll_ptr y_v17939);
tll_ptr gtn_i8(tll_ptr x_v17943, tll_ptr y_v17944);
tll_ptr eqn_i9(tll_ptr x_v17948, tll_ptr y_v17949);
tll_ptr comparen_i10(tll_ptr n1_v17953, tll_ptr n2_v17954);
tll_ptr pred_i11(tll_ptr x_v17958);
tll_ptr addn_i12(tll_ptr x_v17960, tll_ptr y_v17961);
tll_ptr subn_i13(tll_ptr x_v17965, tll_ptr y_v17966);
tll_ptr muln_i14(tll_ptr x_v17970, tll_ptr y_v17971);
tll_ptr divn_i15(tll_ptr x_v17975, tll_ptr y_v17976);
tll_ptr modn_i16(tll_ptr x_v17980, tll_ptr y_v17981);
tll_ptr eqc_i17(tll_ptr c1_v17985, tll_ptr c2_v17986);
tll_ptr comparec_i18(tll_ptr c1_v17992, tll_ptr c2_v17993);
tll_ptr cats_i19(tll_ptr s1_v17999, tll_ptr s2_v18000);
tll_ptr strlen_i20(tll_ptr s_v18006);
tll_ptr eqs_i21(tll_ptr s1_v18010, tll_ptr s2_v18011);
tll_ptr compares_i22(tll_ptr s1_v18021, tll_ptr s2_v18022);
tll_ptr and_thenUUU_i58(tll_ptr A_v18032, tll_ptr B_v18033, tll_ptr opt_v18034, tll_ptr f_v18035);
tll_ptr and_thenUUL_i57(tll_ptr A_v18047, tll_ptr B_v18048, tll_ptr opt_v18049, tll_ptr f_v18050);
tll_ptr and_thenULU_i56(tll_ptr A_v18062, tll_ptr B_v18063, tll_ptr opt_v18064, tll_ptr f_v18065);
tll_ptr and_thenULL_i55(tll_ptr A_v18077, tll_ptr B_v18078, tll_ptr opt_v18079, tll_ptr f_v18080);
tll_ptr and_thenLUL_i53(tll_ptr A_v18092, tll_ptr B_v18093, tll_ptr opt_v18094, tll_ptr f_v18095);
tll_ptr and_thenLLL_i51(tll_ptr A_v18107, tll_ptr B_v18108, tll_ptr opt_v18109, tll_ptr f_v18110);
tll_ptr lenUU_i66(tll_ptr A_v18122, tll_ptr xs_v18123);
tll_ptr lenUL_i65(tll_ptr A_v18131, tll_ptr xs_v18132);
tll_ptr lenLL_i63(tll_ptr A_v18140, tll_ptr xs_v18141);
tll_ptr appendUU_i70(tll_ptr A_v18149, tll_ptr xs_v18150, tll_ptr ys_v18151);
tll_ptr appendUL_i69(tll_ptr A_v18160, tll_ptr xs_v18161, tll_ptr ys_v18162);
tll_ptr appendLL_i67(tll_ptr A_v18171, tll_ptr xs_v18172, tll_ptr ys_v18173);
tll_ptr readline_i33(tll_ptr __v18182);
tll_ptr print_i34(tll_ptr s_v18197);
tll_ptr prerr_i35(tll_ptr s_v18208);
tll_ptr get_at_i37(tll_ptr A_v18219, tll_ptr n_v18220, tll_ptr xs_v18221, tll_ptr a_v18222);
tll_ptr string_of_digit_i38(tll_ptr n_v18237);
tll_ptr string_of_nat_i39(tll_ptr n_v18239);
tll_ptr digit_of_char_i40(tll_ptr c_v18243);
tll_ptr nat_of_string_loop_i41(tll_ptr s_v18245, tll_ptr acc_v18246);
tll_ptr nat_of_string_i42(tll_ptr s_v18253);
tll_ptr pow_i43(tll_ptr n_v18255, tll_ptr m_v18256);
tll_ptr alice_i47(tll_ptr a_v18260, tll_ptr p_v18261, tll_ptr g_v18262, tll_ptr ch_v18263);
tll_ptr bob_i48(tll_ptr b_v18295, tll_ptr p_v18296, tll_ptr g_v18297, tll_ptr ch_v18298);
tll_ptr key_exchange_i49(tll_ptr __v18332);

tll_ptr addnclo_i82;
tll_ptr aliceclo_i115;
tll_ptr and_thenLLLclo_i98;
tll_ptr and_thenLULclo_i97;
tll_ptr and_thenULLclo_i96;
tll_ptr and_thenULUclo_i95;
tll_ptr and_thenUULclo_i94;
tll_ptr and_thenUUUclo_i93;
tll_ptr andbclo_i71;
tll_ptr appendLLclo_i104;
tll_ptr appendULclo_i103;
tll_ptr appendUUclo_i102;
tll_ptr bobclo_i116;
tll_ptr catsclo_i89;
tll_ptr comparebclo_i74;
tll_ptr comparecclo_i88;
tll_ptr comparenclo_i80;
tll_ptr comparesclo_i92;
tll_ptr digit_of_charclo_i111;
tll_ptr digits_i36;
tll_ptr divnclo_i85;
tll_ptr eqcclo_i87;
tll_ptr eqnclo_i79;
tll_ptr eqsclo_i91;
tll_ptr get_atclo_i108;
tll_ptr gtenclo_i77;
tll_ptr gtnclo_i78;
tll_ptr key_exchangeclo_i117;
tll_ptr lenLLclo_i101;
tll_ptr lenULclo_i100;
tll_ptr lenUUclo_i99;
tll_ptr ltenclo_i75;
tll_ptr ltnclo_i76;
tll_ptr modnclo_i86;
tll_ptr mulnclo_i84;
tll_ptr nat_of_string_loopclo_i112;
tll_ptr nat_of_stringclo_i113;
tll_ptr notbclo_i73;
tll_ptr orbclo_i72;
tll_ptr powclo_i114;
tll_ptr predclo_i81;
tll_ptr prerrclo_i107;
tll_ptr printclo_i106;
tll_ptr readlineclo_i105;
tll_ptr string_of_digitclo_i109;
tll_ptr string_of_natclo_i110;
tll_ptr strlenclo_i90;
tll_ptr subnclo_i83;

tll_ptr andb_i1(tll_ptr b1_v17911, tll_ptr b2_v17912) {
  tll_ptr ifte_ret_t1;
  if (b1_v17911) {
    ifte_ret_t1 = b2_v17912;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v17915, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v17915);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v17913, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v17913);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v17916, tll_ptr b2_v17917) {
  tll_ptr ifte_ret_t7;
  if (b1_v17916) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v17917;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v17920, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v17920);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v17918, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v17918);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v17921) {
  tll_ptr ifte_ret_t13;
  if (b_v17921) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v17922, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v17922);
  return call_ret_t14;
}

tll_ptr compareb_i4(tll_ptr b1_v17923, tll_ptr b2_v17924) {
  tll_ptr EQ_t17; tll_ptr EQ_t21; tll_ptr GT_t18; tll_ptr LT_t20;
  tll_ptr ifte_ret_t19; tll_ptr ifte_ret_t22; tll_ptr ifte_ret_t23;
  if (b1_v17923) {
    if (b2_v17924) {
      instr_struct(&EQ_t17, 3, 0);
      ifte_ret_t19 = EQ_t17;
    }
    else {
      instr_struct(&GT_t18, 2, 0);
      ifte_ret_t19 = GT_t18;
    }
    ifte_ret_t23 = ifte_ret_t19;
  }
  else {
    if (b2_v17924) {
      instr_struct(&LT_t20, 1, 0);
      ifte_ret_t22 = LT_t20;
    }
    else {
      instr_struct(&EQ_t21, 3, 0);
      ifte_ret_t22 = EQ_t21;
    }
    ifte_ret_t23 = ifte_ret_t22;
  }
  return ifte_ret_t23;
}

tll_ptr lam_fun_t25(tll_ptr b2_v17927, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = compareb_i4(env[0], b2_v17927);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr b1_v17925, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, b1_v17925);
  return lam_clo_t26;
}

tll_ptr lten_i5(tll_ptr x_v17928, tll_ptr y_v17929) {
  tll_ptr lten_ret_t29;
  instr_lten(&lten_ret_t29, x_v17928, y_v17929);
  return lten_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v17932, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = lten_i5(env[0], y_v17932);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v17930, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v17930);
  return lam_clo_t32;
}

tll_ptr ltn_i6(tll_ptr x_v17933, tll_ptr y_v17934) {
  tll_ptr ltn_ret_t35;
  instr_ltn(&ltn_ret_t35, x_v17933, y_v17934);
  return ltn_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v17937, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = ltn_i6(env[0], y_v17937);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v17935, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v17935);
  return lam_clo_t38;
}

tll_ptr gten_i7(tll_ptr x_v17938, tll_ptr y_v17939) {
  tll_ptr gten_ret_t41;
  instr_gten(&gten_ret_t41, x_v17938, y_v17939);
  return gten_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v17942, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = gten_i7(env[0], y_v17942);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v17940, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v17940);
  return lam_clo_t44;
}

tll_ptr gtn_i8(tll_ptr x_v17943, tll_ptr y_v17944) {
  tll_ptr gtn_ret_t47;
  instr_gtn(&gtn_ret_t47, x_v17943, y_v17944);
  return gtn_ret_t47;
}

tll_ptr lam_fun_t49(tll_ptr y_v17947, tll_env env) {
  tll_ptr call_ret_t48;
  call_ret_t48 = gtn_i8(env[0], y_v17947);
  return call_ret_t48;
}

tll_ptr lam_fun_t51(tll_ptr x_v17945, tll_env env) {
  tll_ptr lam_clo_t50;
  instr_clo(&lam_clo_t50, &lam_fun_t49, 1, x_v17945);
  return lam_clo_t50;
}

tll_ptr eqn_i9(tll_ptr x_v17948, tll_ptr y_v17949) {
  tll_ptr eqn_ret_t53;
  instr_eqn(&eqn_ret_t53, x_v17948, y_v17949);
  return eqn_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v17952, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = eqn_i9(env[0], y_v17952);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v17950, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v17950);
  return lam_clo_t56;
}

tll_ptr comparen_i10(tll_ptr n1_v17953, tll_ptr n2_v17954) {
  tll_ptr EQ_t65; tll_ptr GT_t62; tll_ptr LT_t64; tll_ptr add_ret_t60;
  tll_ptr add_ret_t61; tll_ptr call_ret_t59; tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t66; tll_ptr ifte_ret_t67;
  if (n1_v17953) {
    if (n2_v17954) {
      add_ret_t60 = (tll_ptr)((long)n1_v17953 - 1);
      add_ret_t61 = (tll_ptr)((long)n2_v17954 - 1);
      call_ret_t59 = comparen_i10(add_ret_t60, add_ret_t61);
      ifte_ret_t63 = call_ret_t59;
    }
    else {
      instr_struct(&GT_t62, 2, 0);
      ifte_ret_t63 = GT_t62;
    }
    ifte_ret_t67 = ifte_ret_t63;
  }
  else {
    if (n2_v17954) {
      instr_struct(&LT_t64, 1, 0);
      ifte_ret_t66 = LT_t64;
    }
    else {
      instr_struct(&EQ_t65, 3, 0);
      ifte_ret_t66 = EQ_t65;
    }
    ifte_ret_t67 = ifte_ret_t66;
  }
  return ifte_ret_t67;
}

tll_ptr lam_fun_t69(tll_ptr n2_v17957, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = comparen_i10(env[0], n2_v17957);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr n1_v17955, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, n1_v17955);
  return lam_clo_t70;
}

tll_ptr pred_i11(tll_ptr x_v17958) {
  tll_ptr add_ret_t73; tll_ptr ifte_ret_t74;
  if (x_v17958) {
    add_ret_t73 = (tll_ptr)((long)x_v17958 - 1);
    ifte_ret_t74 = add_ret_t73;
  }
  else {
    ifte_ret_t74 = (tll_ptr)0;
  }
  return ifte_ret_t74;
}

tll_ptr lam_fun_t76(tll_ptr x_v17959, tll_env env) {
  tll_ptr call_ret_t75;
  call_ret_t75 = pred_i11(x_v17959);
  return call_ret_t75;
}

tll_ptr addn_i12(tll_ptr x_v17960, tll_ptr y_v17961) {
  tll_ptr addn_ret_t78;
  instr_addn(&addn_ret_t78, x_v17960, y_v17961);
  return addn_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v17964, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i12(env[0], y_v17964);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v17962, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v17962);
  return lam_clo_t81;
}

tll_ptr subn_i13(tll_ptr x_v17965, tll_ptr y_v17966) {
  tll_ptr subn_ret_t84;
  instr_subn(&subn_ret_t84, x_v17965, y_v17966);
  return subn_ret_t84;
}

tll_ptr lam_fun_t86(tll_ptr y_v17969, tll_env env) {
  tll_ptr call_ret_t85;
  call_ret_t85 = subn_i13(env[0], y_v17969);
  return call_ret_t85;
}

tll_ptr lam_fun_t88(tll_ptr x_v17967, tll_env env) {
  tll_ptr lam_clo_t87;
  instr_clo(&lam_clo_t87, &lam_fun_t86, 1, x_v17967);
  return lam_clo_t87;
}

tll_ptr muln_i14(tll_ptr x_v17970, tll_ptr y_v17971) {
  tll_ptr muln_ret_t90;
  instr_muln(&muln_ret_t90, x_v17970, y_v17971);
  return muln_ret_t90;
}

tll_ptr lam_fun_t92(tll_ptr y_v17974, tll_env env) {
  tll_ptr call_ret_t91;
  call_ret_t91 = muln_i14(env[0], y_v17974);
  return call_ret_t91;
}

tll_ptr lam_fun_t94(tll_ptr x_v17972, tll_env env) {
  tll_ptr lam_clo_t93;
  instr_clo(&lam_clo_t93, &lam_fun_t92, 1, x_v17972);
  return lam_clo_t93;
}

tll_ptr divn_i15(tll_ptr x_v17975, tll_ptr y_v17976) {
  tll_ptr divn_ret_t96;
  instr_divn(&divn_ret_t96, x_v17975, y_v17976);
  return divn_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v17979, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = divn_i15(env[0], y_v17979);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v17977, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v17977);
  return lam_clo_t99;
}

tll_ptr modn_i16(tll_ptr x_v17980, tll_ptr y_v17981) {
  tll_ptr modn_ret_t102;
  instr_modn(&modn_ret_t102, x_v17980, y_v17981);
  return modn_ret_t102;
}

tll_ptr lam_fun_t104(tll_ptr y_v17984, tll_env env) {
  tll_ptr call_ret_t103;
  call_ret_t103 = modn_i16(env[0], y_v17984);
  return call_ret_t103;
}

tll_ptr lam_fun_t106(tll_ptr x_v17982, tll_env env) {
  tll_ptr lam_clo_t105;
  instr_clo(&lam_clo_t105, &lam_fun_t104, 1, x_v17982);
  return lam_clo_t105;
}

tll_ptr eqc_i17(tll_ptr c1_v17985, tll_ptr c2_v17986) {
  tll_ptr call_ret_t110; tll_ptr n1_v17987; tll_ptr n2_v17988;
  tll_ptr switch_ret_t108; tll_ptr switch_ret_t109;
  switch(((tll_node)c1_v17985)->tag) {
    case 5:
      n1_v17987 = ((tll_node)c1_v17985)->data[0];
      switch(((tll_node)c2_v17986)->tag) {
        case 5:
          n2_v17988 = ((tll_node)c2_v17986)->data[0];
          call_ret_t110 = eqn_i9(n1_v17987, n2_v17988);
          switch_ret_t109 = call_ret_t110;
          break;
      }
      switch_ret_t108 = switch_ret_t109;
      break;
  }
  return switch_ret_t108;
}

tll_ptr lam_fun_t112(tll_ptr c2_v17991, tll_env env) {
  tll_ptr call_ret_t111;
  call_ret_t111 = eqc_i17(env[0], c2_v17991);
  return call_ret_t111;
}

tll_ptr lam_fun_t114(tll_ptr c1_v17989, tll_env env) {
  tll_ptr lam_clo_t113;
  instr_clo(&lam_clo_t113, &lam_fun_t112, 1, c1_v17989);
  return lam_clo_t113;
}

tll_ptr comparec_i18(tll_ptr c1_v17992, tll_ptr c2_v17993) {
  tll_ptr call_ret_t118; tll_ptr n1_v17994; tll_ptr n2_v17995;
  tll_ptr switch_ret_t116; tll_ptr switch_ret_t117;
  switch(((tll_node)c1_v17992)->tag) {
    case 5:
      n1_v17994 = ((tll_node)c1_v17992)->data[0];
      switch(((tll_node)c2_v17993)->tag) {
        case 5:
          n2_v17995 = ((tll_node)c2_v17993)->data[0];
          call_ret_t118 = comparen_i10(n1_v17994, n2_v17995);
          switch_ret_t117 = call_ret_t118;
          break;
      }
      switch_ret_t116 = switch_ret_t117;
      break;
  }
  return switch_ret_t116;
}

tll_ptr lam_fun_t120(tll_ptr c2_v17998, tll_env env) {
  tll_ptr call_ret_t119;
  call_ret_t119 = comparec_i18(env[0], c2_v17998);
  return call_ret_t119;
}

tll_ptr lam_fun_t122(tll_ptr c1_v17996, tll_env env) {
  tll_ptr lam_clo_t121;
  instr_clo(&lam_clo_t121, &lam_fun_t120, 1, c1_v17996);
  return lam_clo_t121;
}

tll_ptr cats_i19(tll_ptr s1_v17999, tll_ptr s2_v18000) {
  tll_ptr String_t126; tll_ptr c_v18001; tll_ptr call_ret_t125;
  tll_ptr s1_v18002; tll_ptr switch_ret_t124;
  switch(((tll_node)s1_v17999)->tag) {
    case 6:
      switch_ret_t124 = s2_v18000;
      break;
    case 7:
      c_v18001 = ((tll_node)s1_v17999)->data[0];
      s1_v18002 = ((tll_node)s1_v17999)->data[1];
      call_ret_t125 = cats_i19(s1_v18002, s2_v18000);
      instr_struct(&String_t126, 7, 2, c_v18001, call_ret_t125);
      switch_ret_t124 = String_t126;
      break;
  }
  return switch_ret_t124;
}

tll_ptr lam_fun_t128(tll_ptr s2_v18005, tll_env env) {
  tll_ptr call_ret_t127;
  call_ret_t127 = cats_i19(env[0], s2_v18005);
  return call_ret_t127;
}

tll_ptr lam_fun_t130(tll_ptr s1_v18003, tll_env env) {
  tll_ptr lam_clo_t129;
  instr_clo(&lam_clo_t129, &lam_fun_t128, 1, s1_v18003);
  return lam_clo_t129;
}

tll_ptr strlen_i20(tll_ptr s_v18006) {
  tll_ptr __v18007; tll_ptr add_ret_t134; tll_ptr call_ret_t133;
  tll_ptr s_v18008; tll_ptr switch_ret_t132;
  switch(((tll_node)s_v18006)->tag) {
    case 6:
      switch_ret_t132 = (tll_ptr)0;
      break;
    case 7:
      __v18007 = ((tll_node)s_v18006)->data[0];
      s_v18008 = ((tll_node)s_v18006)->data[1];
      call_ret_t133 = strlen_i20(s_v18008);
      add_ret_t134 = (tll_ptr)((long)call_ret_t133 + 1);
      switch_ret_t132 = add_ret_t134;
      break;
  }
  return switch_ret_t132;
}

tll_ptr lam_fun_t136(tll_ptr s_v18009, tll_env env) {
  tll_ptr call_ret_t135;
  call_ret_t135 = strlen_i20(s_v18009);
  return call_ret_t135;
}

tll_ptr eqs_i21(tll_ptr s1_v18010, tll_ptr s2_v18011) {
  tll_ptr __v18012; tll_ptr __v18013; tll_ptr c1_v18014; tll_ptr c2_v18016;
  tll_ptr call_ret_t141; tll_ptr call_ret_t142; tll_ptr call_ret_t143;
  tll_ptr s1_v18015; tll_ptr s2_v18017; tll_ptr switch_ret_t138;
  tll_ptr switch_ret_t139; tll_ptr switch_ret_t140;
  switch(((tll_node)s1_v18010)->tag) {
    case 6:
      switch(((tll_node)s2_v18011)->tag) {
        case 6:
          switch_ret_t139 = (tll_ptr)1;
          break;
        case 7:
          __v18012 = ((tll_node)s2_v18011)->data[0];
          __v18013 = ((tll_node)s2_v18011)->data[1];
          switch_ret_t139 = (tll_ptr)0;
          break;
      }
      switch_ret_t138 = switch_ret_t139;
      break;
    case 7:
      c1_v18014 = ((tll_node)s1_v18010)->data[0];
      s1_v18015 = ((tll_node)s1_v18010)->data[1];
      switch(((tll_node)s2_v18011)->tag) {
        case 6:
          switch_ret_t140 = (tll_ptr)0;
          break;
        case 7:
          c2_v18016 = ((tll_node)s2_v18011)->data[0];
          s2_v18017 = ((tll_node)s2_v18011)->data[1];
          call_ret_t142 = eqc_i17(c1_v18014, c2_v18016);
          call_ret_t143 = eqs_i21(s1_v18015, s2_v18017);
          call_ret_t141 = andb_i1(call_ret_t142, call_ret_t143);
          switch_ret_t140 = call_ret_t141;
          break;
      }
      switch_ret_t138 = switch_ret_t140;
      break;
  }
  return switch_ret_t138;
}

tll_ptr lam_fun_t145(tll_ptr s2_v18020, tll_env env) {
  tll_ptr call_ret_t144;
  call_ret_t144 = eqs_i21(env[0], s2_v18020);
  return call_ret_t144;
}

tll_ptr lam_fun_t147(tll_ptr s1_v18018, tll_env env) {
  tll_ptr lam_clo_t146;
  instr_clo(&lam_clo_t146, &lam_fun_t145, 1, s1_v18018);
  return lam_clo_t146;
}

tll_ptr compares_i22(tll_ptr s1_v18021, tll_ptr s2_v18022) {
  tll_ptr EQ_t151; tll_ptr GT_t154; tll_ptr GT_t159; tll_ptr LT_t152;
  tll_ptr LT_t158; tll_ptr __v18023; tll_ptr __v18024; tll_ptr c1_v18025;
  tll_ptr c2_v18027; tll_ptr call_ret_t155; tll_ptr call_ret_t157;
  tll_ptr s1_v18026; tll_ptr s2_v18028; tll_ptr switch_ret_t149;
  tll_ptr switch_ret_t150; tll_ptr switch_ret_t153; tll_ptr switch_ret_t156;
  switch(((tll_node)s1_v18021)->tag) {
    case 6:
      switch(((tll_node)s2_v18022)->tag) {
        case 6:
          instr_struct(&EQ_t151, 3, 0);
          switch_ret_t150 = EQ_t151;
          break;
        case 7:
          __v18023 = ((tll_node)s2_v18022)->data[0];
          __v18024 = ((tll_node)s2_v18022)->data[1];
          instr_struct(&LT_t152, 1, 0);
          switch_ret_t150 = LT_t152;
          break;
      }
      switch_ret_t149 = switch_ret_t150;
      break;
    case 7:
      c1_v18025 = ((tll_node)s1_v18021)->data[0];
      s1_v18026 = ((tll_node)s1_v18021)->data[1];
      switch(((tll_node)s2_v18022)->tag) {
        case 6:
          instr_struct(&GT_t154, 2, 0);
          switch_ret_t153 = GT_t154;
          break;
        case 7:
          c2_v18027 = ((tll_node)s2_v18022)->data[0];
          s2_v18028 = ((tll_node)s2_v18022)->data[1];
          call_ret_t155 = comparec_i18(c1_v18025, c2_v18027);
          switch(((tll_node)call_ret_t155)->tag) {
            case 3:
              call_ret_t157 = compares_i22(s1_v18026, s2_v18028);
              switch_ret_t156 = call_ret_t157;
              break;
            case 1:
              instr_struct(&LT_t158, 1, 0);
              switch_ret_t156 = LT_t158;
              break;
            case 2:
              instr_struct(&GT_t159, 2, 0);
              switch_ret_t156 = GT_t159;
              break;
          }
          switch_ret_t153 = switch_ret_t156;
          break;
      }
      switch_ret_t149 = switch_ret_t153;
      break;
  }
  return switch_ret_t149;
}

tll_ptr lam_fun_t161(tll_ptr s2_v18031, tll_env env) {
  tll_ptr call_ret_t160;
  call_ret_t160 = compares_i22(env[0], s2_v18031);
  return call_ret_t160;
}

tll_ptr lam_fun_t163(tll_ptr s1_v18029, tll_env env) {
  tll_ptr lam_clo_t162;
  instr_clo(&lam_clo_t162, &lam_fun_t161, 1, s1_v18029);
  return lam_clo_t162;
}

tll_ptr and_thenUUU_i58(tll_ptr A_v18032, tll_ptr B_v18033, tll_ptr opt_v18034, tll_ptr f_v18035) {
  tll_ptr NoneUU_t166; tll_ptr app_ret_t167; tll_ptr switch_ret_t165;
  tll_ptr x_v18036;
  switch(((tll_node)opt_v18034)->tag) {
    case 18:
      instr_struct(&NoneUU_t166, 18, 0);
      switch_ret_t165 = NoneUU_t166;
      break;
    case 19:
      x_v18036 = ((tll_node)opt_v18034)->data[0];
      instr_app(&app_ret_t167, f_v18035, x_v18036);
      switch_ret_t165 = app_ret_t167;
      break;
  }
  return switch_ret_t165;
}

tll_ptr lam_fun_t169(tll_ptr f_v18046, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = and_thenUUU_i58(env[2], env[1], env[0], f_v18046);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr opt_v18044, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 3, opt_v18044, env[0], env[1]);
  return lam_clo_t170;
}

tll_ptr lam_fun_t173(tll_ptr B_v18041, tll_env env) {
  tll_ptr lam_clo_t172;
  instr_clo(&lam_clo_t172, &lam_fun_t171, 2, B_v18041, env[0]);
  return lam_clo_t172;
}

tll_ptr lam_fun_t175(tll_ptr A_v18037, tll_env env) {
  tll_ptr lam_clo_t174;
  instr_clo(&lam_clo_t174, &lam_fun_t173, 1, A_v18037);
  return lam_clo_t174;
}

tll_ptr and_thenUUL_i57(tll_ptr A_v18047, tll_ptr B_v18048, tll_ptr opt_v18049, tll_ptr f_v18050) {
  tll_ptr NoneUL_t178; tll_ptr app_ret_t179; tll_ptr switch_ret_t177;
  tll_ptr x_v18051;
  switch(((tll_node)opt_v18049)->tag) {
    case 16:
      instr_free_struct(opt_v18049);
      instr_struct(&NoneUL_t178, 16, 0);
      switch_ret_t177 = NoneUL_t178;
      break;
    case 17:
      x_v18051 = ((tll_node)opt_v18049)->data[0];
      instr_free_struct(opt_v18049);
      instr_app(&app_ret_t179, f_v18050, x_v18051);
      switch_ret_t177 = app_ret_t179;
      break;
  }
  return switch_ret_t177;
}

tll_ptr lam_fun_t181(tll_ptr f_v18061, tll_env env) {
  tll_ptr call_ret_t180;
  call_ret_t180 = and_thenUUL_i57(env[2], env[1], env[0], f_v18061);
  return call_ret_t180;
}

tll_ptr lam_fun_t183(tll_ptr opt_v18059, tll_env env) {
  tll_ptr lam_clo_t182;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 3, opt_v18059, env[0], env[1]);
  return lam_clo_t182;
}

tll_ptr lam_fun_t185(tll_ptr B_v18056, tll_env env) {
  tll_ptr lam_clo_t184;
  instr_clo(&lam_clo_t184, &lam_fun_t183, 2, B_v18056, env[0]);
  return lam_clo_t184;
}

tll_ptr lam_fun_t187(tll_ptr A_v18052, tll_env env) {
  tll_ptr lam_clo_t186;
  instr_clo(&lam_clo_t186, &lam_fun_t185, 1, A_v18052);
  return lam_clo_t186;
}

tll_ptr and_thenULU_i56(tll_ptr A_v18062, tll_ptr B_v18063, tll_ptr opt_v18064, tll_ptr f_v18065) {
  tll_ptr NoneLU_t190; tll_ptr app_ret_t191; tll_ptr switch_ret_t189;
  tll_ptr x_v18066;
  switch(((tll_node)opt_v18064)->tag) {
    case 18:
      instr_struct(&NoneLU_t190, 14, 0);
      switch_ret_t189 = NoneLU_t190;
      break;
    case 19:
      x_v18066 = ((tll_node)opt_v18064)->data[0];
      instr_app(&app_ret_t191, f_v18065, x_v18066);
      switch_ret_t189 = app_ret_t191;
      break;
  }
  return switch_ret_t189;
}

tll_ptr lam_fun_t193(tll_ptr f_v18076, tll_env env) {
  tll_ptr call_ret_t192;
  call_ret_t192 = and_thenULU_i56(env[2], env[1], env[0], f_v18076);
  return call_ret_t192;
}

tll_ptr lam_fun_t195(tll_ptr opt_v18074, tll_env env) {
  tll_ptr lam_clo_t194;
  instr_clo(&lam_clo_t194, &lam_fun_t193, 3, opt_v18074, env[0], env[1]);
  return lam_clo_t194;
}

tll_ptr lam_fun_t197(tll_ptr B_v18071, tll_env env) {
  tll_ptr lam_clo_t196;
  instr_clo(&lam_clo_t196, &lam_fun_t195, 2, B_v18071, env[0]);
  return lam_clo_t196;
}

tll_ptr lam_fun_t199(tll_ptr A_v18067, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 1, A_v18067);
  return lam_clo_t198;
}

tll_ptr and_thenULL_i55(tll_ptr A_v18077, tll_ptr B_v18078, tll_ptr opt_v18079, tll_ptr f_v18080) {
  tll_ptr NoneLL_t202; tll_ptr app_ret_t203; tll_ptr switch_ret_t201;
  tll_ptr x_v18081;
  switch(((tll_node)opt_v18079)->tag) {
    case 16:
      instr_free_struct(opt_v18079);
      instr_struct(&NoneLL_t202, 12, 0);
      switch_ret_t201 = NoneLL_t202;
      break;
    case 17:
      x_v18081 = ((tll_node)opt_v18079)->data[0];
      instr_free_struct(opt_v18079);
      instr_app(&app_ret_t203, f_v18080, x_v18081);
      switch_ret_t201 = app_ret_t203;
      break;
  }
  return switch_ret_t201;
}

tll_ptr lam_fun_t205(tll_ptr f_v18091, tll_env env) {
  tll_ptr call_ret_t204;
  call_ret_t204 = and_thenULL_i55(env[2], env[1], env[0], f_v18091);
  return call_ret_t204;
}

tll_ptr lam_fun_t207(tll_ptr opt_v18089, tll_env env) {
  tll_ptr lam_clo_t206;
  instr_clo(&lam_clo_t206, &lam_fun_t205, 3, opt_v18089, env[0], env[1]);
  return lam_clo_t206;
}

tll_ptr lam_fun_t209(tll_ptr B_v18086, tll_env env) {
  tll_ptr lam_clo_t208;
  instr_clo(&lam_clo_t208, &lam_fun_t207, 2, B_v18086, env[0]);
  return lam_clo_t208;
}

tll_ptr lam_fun_t211(tll_ptr A_v18082, tll_env env) {
  tll_ptr lam_clo_t210;
  instr_clo(&lam_clo_t210, &lam_fun_t209, 1, A_v18082);
  return lam_clo_t210;
}

tll_ptr and_thenLUL_i53(tll_ptr A_v18092, tll_ptr B_v18093, tll_ptr opt_v18094, tll_ptr f_v18095) {
  tll_ptr NoneUL_t214; tll_ptr app_ret_t215; tll_ptr switch_ret_t213;
  tll_ptr x_v18096;
  switch(((tll_node)opt_v18094)->tag) {
    case 12:
      instr_free_struct(opt_v18094);
      instr_struct(&NoneUL_t214, 16, 0);
      switch_ret_t213 = NoneUL_t214;
      break;
    case 13:
      x_v18096 = ((tll_node)opt_v18094)->data[0];
      instr_free_struct(opt_v18094);
      instr_app(&app_ret_t215, f_v18095, x_v18096);
      switch_ret_t213 = app_ret_t215;
      break;
  }
  return switch_ret_t213;
}

tll_ptr lam_fun_t217(tll_ptr f_v18106, tll_env env) {
  tll_ptr call_ret_t216;
  call_ret_t216 = and_thenLUL_i53(env[2], env[1], env[0], f_v18106);
  return call_ret_t216;
}

tll_ptr lam_fun_t219(tll_ptr opt_v18104, tll_env env) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 3, opt_v18104, env[0], env[1]);
  return lam_clo_t218;
}

tll_ptr lam_fun_t221(tll_ptr B_v18101, tll_env env) {
  tll_ptr lam_clo_t220;
  instr_clo(&lam_clo_t220, &lam_fun_t219, 2, B_v18101, env[0]);
  return lam_clo_t220;
}

tll_ptr lam_fun_t223(tll_ptr A_v18097, tll_env env) {
  tll_ptr lam_clo_t222;
  instr_clo(&lam_clo_t222, &lam_fun_t221, 1, A_v18097);
  return lam_clo_t222;
}

tll_ptr and_thenLLL_i51(tll_ptr A_v18107, tll_ptr B_v18108, tll_ptr opt_v18109, tll_ptr f_v18110) {
  tll_ptr NoneLL_t226; tll_ptr app_ret_t227; tll_ptr switch_ret_t225;
  tll_ptr x_v18111;
  switch(((tll_node)opt_v18109)->tag) {
    case 12:
      instr_free_struct(opt_v18109);
      instr_struct(&NoneLL_t226, 12, 0);
      switch_ret_t225 = NoneLL_t226;
      break;
    case 13:
      x_v18111 = ((tll_node)opt_v18109)->data[0];
      instr_free_struct(opt_v18109);
      instr_app(&app_ret_t227, f_v18110, x_v18111);
      switch_ret_t225 = app_ret_t227;
      break;
  }
  return switch_ret_t225;
}

tll_ptr lam_fun_t229(tll_ptr f_v18121, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = and_thenLLL_i51(env[2], env[1], env[0], f_v18121);
  return call_ret_t228;
}

tll_ptr lam_fun_t231(tll_ptr opt_v18119, tll_env env) {
  tll_ptr lam_clo_t230;
  instr_clo(&lam_clo_t230, &lam_fun_t229, 3, opt_v18119, env[0], env[1]);
  return lam_clo_t230;
}

tll_ptr lam_fun_t233(tll_ptr B_v18116, tll_env env) {
  tll_ptr lam_clo_t232;
  instr_clo(&lam_clo_t232, &lam_fun_t231, 2, B_v18116, env[0]);
  return lam_clo_t232;
}

tll_ptr lam_fun_t235(tll_ptr A_v18112, tll_env env) {
  tll_ptr lam_clo_t234;
  instr_clo(&lam_clo_t234, &lam_fun_t233, 1, A_v18112);
  return lam_clo_t234;
}

tll_ptr lenUU_i66(tll_ptr A_v18122, tll_ptr xs_v18123) {
  tll_ptr add_ret_t242; tll_ptr call_ret_t240; tll_ptr consUU_t243;
  tll_ptr n_v18126; tll_ptr nilUU_t238; tll_ptr pair_struct_t239;
  tll_ptr pair_struct_t244; tll_ptr switch_ret_t237; tll_ptr switch_ret_t241;
  tll_ptr x_v18124; tll_ptr xs_v18125; tll_ptr xs_v18127;
  switch(((tll_node)xs_v18123)->tag) {
    case 26:
      instr_struct(&nilUU_t238, 26, 0);
      instr_struct(&pair_struct_t239, 0, 2, (tll_ptr)0, nilUU_t238);
      switch_ret_t237 = pair_struct_t239;
      break;
    case 27:
      x_v18124 = ((tll_node)xs_v18123)->data[0];
      xs_v18125 = ((tll_node)xs_v18123)->data[1];
      call_ret_t240 = lenUU_i66(0, xs_v18125);
      switch(((tll_node)call_ret_t240)->tag) {
        case 0:
          n_v18126 = ((tll_node)call_ret_t240)->data[0];
          xs_v18127 = ((tll_node)call_ret_t240)->data[1];
          instr_free_struct(call_ret_t240);
          add_ret_t242 = (tll_ptr)((long)n_v18126 + 1);
          instr_struct(&consUU_t243, 27, 2, x_v18124, xs_v18127);
          instr_struct(&pair_struct_t244, 0, 2, add_ret_t242, consUU_t243);
          switch_ret_t241 = pair_struct_t244;
          break;
      }
      switch_ret_t237 = switch_ret_t241;
      break;
  }
  return switch_ret_t237;
}

tll_ptr lam_fun_t246(tll_ptr xs_v18130, tll_env env) {
  tll_ptr call_ret_t245;
  call_ret_t245 = lenUU_i66(env[0], xs_v18130);
  return call_ret_t245;
}

tll_ptr lam_fun_t248(tll_ptr A_v18128, tll_env env) {
  tll_ptr lam_clo_t247;
  instr_clo(&lam_clo_t247, &lam_fun_t246, 1, A_v18128);
  return lam_clo_t247;
}

tll_ptr lenUL_i65(tll_ptr A_v18131, tll_ptr xs_v18132) {
  tll_ptr add_ret_t255; tll_ptr call_ret_t253; tll_ptr consUL_t256;
  tll_ptr n_v18135; tll_ptr nilUL_t251; tll_ptr pair_struct_t252;
  tll_ptr pair_struct_t257; tll_ptr switch_ret_t250; tll_ptr switch_ret_t254;
  tll_ptr x_v18133; tll_ptr xs_v18134; tll_ptr xs_v18136;
  switch(((tll_node)xs_v18132)->tag) {
    case 24:
      instr_free_struct(xs_v18132);
      instr_struct(&nilUL_t251, 24, 0);
      instr_struct(&pair_struct_t252, 0, 2, (tll_ptr)0, nilUL_t251);
      switch_ret_t250 = pair_struct_t252;
      break;
    case 25:
      x_v18133 = ((tll_node)xs_v18132)->data[0];
      xs_v18134 = ((tll_node)xs_v18132)->data[1];
      instr_free_struct(xs_v18132);
      call_ret_t253 = lenUL_i65(0, xs_v18134);
      switch(((tll_node)call_ret_t253)->tag) {
        case 0:
          n_v18135 = ((tll_node)call_ret_t253)->data[0];
          xs_v18136 = ((tll_node)call_ret_t253)->data[1];
          instr_free_struct(call_ret_t253);
          add_ret_t255 = (tll_ptr)((long)n_v18135 + 1);
          instr_struct(&consUL_t256, 25, 2, x_v18133, xs_v18136);
          instr_struct(&pair_struct_t257, 0, 2, add_ret_t255, consUL_t256);
          switch_ret_t254 = pair_struct_t257;
          break;
      }
      switch_ret_t250 = switch_ret_t254;
      break;
  }
  return switch_ret_t250;
}

tll_ptr lam_fun_t259(tll_ptr xs_v18139, tll_env env) {
  tll_ptr call_ret_t258;
  call_ret_t258 = lenUL_i65(env[0], xs_v18139);
  return call_ret_t258;
}

tll_ptr lam_fun_t261(tll_ptr A_v18137, tll_env env) {
  tll_ptr lam_clo_t260;
  instr_clo(&lam_clo_t260, &lam_fun_t259, 1, A_v18137);
  return lam_clo_t260;
}

tll_ptr lenLL_i63(tll_ptr A_v18140, tll_ptr xs_v18141) {
  tll_ptr add_ret_t268; tll_ptr call_ret_t266; tll_ptr consLL_t269;
  tll_ptr n_v18144; tll_ptr nilLL_t264; tll_ptr pair_struct_t265;
  tll_ptr pair_struct_t270; tll_ptr switch_ret_t263; tll_ptr switch_ret_t267;
  tll_ptr x_v18142; tll_ptr xs_v18143; tll_ptr xs_v18145;
  switch(((tll_node)xs_v18141)->tag) {
    case 20:
      instr_free_struct(xs_v18141);
      instr_struct(&nilLL_t264, 20, 0);
      instr_struct(&pair_struct_t265, 0, 2, (tll_ptr)0, nilLL_t264);
      switch_ret_t263 = pair_struct_t265;
      break;
    case 21:
      x_v18142 = ((tll_node)xs_v18141)->data[0];
      xs_v18143 = ((tll_node)xs_v18141)->data[1];
      instr_free_struct(xs_v18141);
      call_ret_t266 = lenLL_i63(0, xs_v18143);
      switch(((tll_node)call_ret_t266)->tag) {
        case 0:
          n_v18144 = ((tll_node)call_ret_t266)->data[0];
          xs_v18145 = ((tll_node)call_ret_t266)->data[1];
          instr_free_struct(call_ret_t266);
          add_ret_t268 = (tll_ptr)((long)n_v18144 + 1);
          instr_struct(&consLL_t269, 21, 2, x_v18142, xs_v18145);
          instr_struct(&pair_struct_t270, 0, 2, add_ret_t268, consLL_t269);
          switch_ret_t267 = pair_struct_t270;
          break;
      }
      switch_ret_t263 = switch_ret_t267;
      break;
  }
  return switch_ret_t263;
}

tll_ptr lam_fun_t272(tll_ptr xs_v18148, tll_env env) {
  tll_ptr call_ret_t271;
  call_ret_t271 = lenLL_i63(env[0], xs_v18148);
  return call_ret_t271;
}

tll_ptr lam_fun_t274(tll_ptr A_v18146, tll_env env) {
  tll_ptr lam_clo_t273;
  instr_clo(&lam_clo_t273, &lam_fun_t272, 1, A_v18146);
  return lam_clo_t273;
}

tll_ptr appendUU_i70(tll_ptr A_v18149, tll_ptr xs_v18150, tll_ptr ys_v18151) {
  tll_ptr call_ret_t277; tll_ptr consUU_t278; tll_ptr switch_ret_t276;
  tll_ptr x_v18152; tll_ptr xs_v18153;
  switch(((tll_node)xs_v18150)->tag) {
    case 26:
      switch_ret_t276 = ys_v18151;
      break;
    case 27:
      x_v18152 = ((tll_node)xs_v18150)->data[0];
      xs_v18153 = ((tll_node)xs_v18150)->data[1];
      call_ret_t277 = appendUU_i70(0, xs_v18153, ys_v18151);
      instr_struct(&consUU_t278, 27, 2, x_v18152, call_ret_t277);
      switch_ret_t276 = consUU_t278;
      break;
  }
  return switch_ret_t276;
}

tll_ptr lam_fun_t280(tll_ptr ys_v18159, tll_env env) {
  tll_ptr call_ret_t279;
  call_ret_t279 = appendUU_i70(env[1], env[0], ys_v18159);
  return call_ret_t279;
}

tll_ptr lam_fun_t282(tll_ptr xs_v18157, tll_env env) {
  tll_ptr lam_clo_t281;
  instr_clo(&lam_clo_t281, &lam_fun_t280, 2, xs_v18157, env[0]);
  return lam_clo_t281;
}

tll_ptr lam_fun_t284(tll_ptr A_v18154, tll_env env) {
  tll_ptr lam_clo_t283;
  instr_clo(&lam_clo_t283, &lam_fun_t282, 1, A_v18154);
  return lam_clo_t283;
}

tll_ptr appendUL_i69(tll_ptr A_v18160, tll_ptr xs_v18161, tll_ptr ys_v18162) {
  tll_ptr call_ret_t287; tll_ptr consUL_t288; tll_ptr switch_ret_t286;
  tll_ptr x_v18163; tll_ptr xs_v18164;
  switch(((tll_node)xs_v18161)->tag) {
    case 24:
      instr_free_struct(xs_v18161);
      switch_ret_t286 = ys_v18162;
      break;
    case 25:
      x_v18163 = ((tll_node)xs_v18161)->data[0];
      xs_v18164 = ((tll_node)xs_v18161)->data[1];
      instr_free_struct(xs_v18161);
      call_ret_t287 = appendUL_i69(0, xs_v18164, ys_v18162);
      instr_struct(&consUL_t288, 25, 2, x_v18163, call_ret_t287);
      switch_ret_t286 = consUL_t288;
      break;
  }
  return switch_ret_t286;
}

tll_ptr lam_fun_t290(tll_ptr ys_v18170, tll_env env) {
  tll_ptr call_ret_t289;
  call_ret_t289 = appendUL_i69(env[1], env[0], ys_v18170);
  return call_ret_t289;
}

tll_ptr lam_fun_t292(tll_ptr xs_v18168, tll_env env) {
  tll_ptr lam_clo_t291;
  instr_clo(&lam_clo_t291, &lam_fun_t290, 2, xs_v18168, env[0]);
  return lam_clo_t291;
}

tll_ptr lam_fun_t294(tll_ptr A_v18165, tll_env env) {
  tll_ptr lam_clo_t293;
  instr_clo(&lam_clo_t293, &lam_fun_t292, 1, A_v18165);
  return lam_clo_t293;
}

tll_ptr appendLL_i67(tll_ptr A_v18171, tll_ptr xs_v18172, tll_ptr ys_v18173) {
  tll_ptr call_ret_t297; tll_ptr consLL_t298; tll_ptr switch_ret_t296;
  tll_ptr x_v18174; tll_ptr xs_v18175;
  switch(((tll_node)xs_v18172)->tag) {
    case 20:
      instr_free_struct(xs_v18172);
      switch_ret_t296 = ys_v18173;
      break;
    case 21:
      x_v18174 = ((tll_node)xs_v18172)->data[0];
      xs_v18175 = ((tll_node)xs_v18172)->data[1];
      instr_free_struct(xs_v18172);
      call_ret_t297 = appendLL_i67(0, xs_v18175, ys_v18173);
      instr_struct(&consLL_t298, 21, 2, x_v18174, call_ret_t297);
      switch_ret_t296 = consLL_t298;
      break;
  }
  return switch_ret_t296;
}

tll_ptr lam_fun_t300(tll_ptr ys_v18181, tll_env env) {
  tll_ptr call_ret_t299;
  call_ret_t299 = appendLL_i67(env[1], env[0], ys_v18181);
  return call_ret_t299;
}

tll_ptr lam_fun_t302(tll_ptr xs_v18179, tll_env env) {
  tll_ptr lam_clo_t301;
  instr_clo(&lam_clo_t301, &lam_fun_t300, 2, xs_v18179, env[0]);
  return lam_clo_t301;
}

tll_ptr lam_fun_t304(tll_ptr A_v18176, tll_env env) {
  tll_ptr lam_clo_t303;
  instr_clo(&lam_clo_t303, &lam_fun_t302, 1, A_v18176);
  return lam_clo_t303;
}

tll_ptr lam_fun_t311(tll_ptr __v18183, tll_env env) {
  tll_ptr __v18192; tll_ptr ch_v18190; tll_ptr ch_v18191; tll_ptr ch_v18194;
  tll_ptr ch_v18195; tll_ptr prim_ch_t306; tll_ptr recv_msg_t308;
  tll_ptr s_v18193; tll_ptr send_ch_t307; tll_ptr send_ch_t310;
  tll_ptr switch_ret_t309;
  instr_open(&prim_ch_t306, &proc_stdin);
  ch_v18190 = prim_ch_t306;
  instr_send(&send_ch_t307, ch_v18190, (tll_ptr)1);
  ch_v18191 = send_ch_t307;
  instr_recv(&recv_msg_t308, ch_v18191);
  __v18192 = recv_msg_t308;
  switch(((tll_node)__v18192)->tag) {
    case 0:
      s_v18193 = ((tll_node)__v18192)->data[0];
      ch_v18194 = ((tll_node)__v18192)->data[1];
      instr_free_struct(__v18192);
      instr_send(&send_ch_t310, ch_v18194, (tll_ptr)0);
      ch_v18195 = send_ch_t310;
      switch_ret_t309 = s_v18193;
      break;
  }
  return switch_ret_t309;
}

tll_ptr readline_i33(tll_ptr __v18182) {
  tll_ptr lam_clo_t312;
  instr_clo(&lam_clo_t312, &lam_fun_t311, 0);
  return lam_clo_t312;
}

tll_ptr lam_fun_t314(tll_ptr __v18196, tll_env env) {
  tll_ptr call_ret_t313;
  call_ret_t313 = readline_i33(__v18196);
  return call_ret_t313;
}

tll_ptr lam_fun_t320(tll_ptr __v18198, tll_env env) {
  tll_ptr ch_v18203; tll_ptr ch_v18204; tll_ptr ch_v18205; tll_ptr ch_v18206;
  tll_ptr prim_ch_t316; tll_ptr send_ch_t317; tll_ptr send_ch_t318;
  tll_ptr send_ch_t319;
  instr_open(&prim_ch_t316, &proc_stdout);
  ch_v18203 = prim_ch_t316;
  instr_send(&send_ch_t317, ch_v18203, (tll_ptr)1);
  ch_v18204 = send_ch_t317;
  instr_send(&send_ch_t318, ch_v18204, env[0]);
  ch_v18205 = send_ch_t318;
  instr_send(&send_ch_t319, ch_v18205, (tll_ptr)0);
  ch_v18206 = send_ch_t319;
  return 0;
}

tll_ptr print_i34(tll_ptr s_v18197) {
  tll_ptr lam_clo_t321;
  instr_clo(&lam_clo_t321, &lam_fun_t320, 1, s_v18197);
  return lam_clo_t321;
}

tll_ptr lam_fun_t323(tll_ptr s_v18207, tll_env env) {
  tll_ptr call_ret_t322;
  call_ret_t322 = print_i34(s_v18207);
  return call_ret_t322;
}

tll_ptr lam_fun_t329(tll_ptr __v18209, tll_env env) {
  tll_ptr ch_v18214; tll_ptr ch_v18215; tll_ptr ch_v18216; tll_ptr ch_v18217;
  tll_ptr prim_ch_t325; tll_ptr send_ch_t326; tll_ptr send_ch_t327;
  tll_ptr send_ch_t328;
  instr_open(&prim_ch_t325, &proc_stderr);
  ch_v18214 = prim_ch_t325;
  instr_send(&send_ch_t326, ch_v18214, (tll_ptr)1);
  ch_v18215 = send_ch_t326;
  instr_send(&send_ch_t327, ch_v18215, env[0]);
  ch_v18216 = send_ch_t327;
  instr_send(&send_ch_t328, ch_v18216, (tll_ptr)0);
  ch_v18217 = send_ch_t328;
  return 0;
}

tll_ptr prerr_i35(tll_ptr s_v18208) {
  tll_ptr lam_clo_t330;
  instr_clo(&lam_clo_t330, &lam_fun_t329, 1, s_v18208);
  return lam_clo_t330;
}

tll_ptr lam_fun_t332(tll_ptr s_v18218, tll_env env) {
  tll_ptr call_ret_t331;
  call_ret_t331 = prerr_i35(s_v18218);
  return call_ret_t331;
}

tll_ptr get_at_i37(tll_ptr A_v18219, tll_ptr n_v18220, tll_ptr xs_v18221, tll_ptr a_v18222) {
  tll_ptr __v18223; tll_ptr __v18226; tll_ptr add_ret_t377;
  tll_ptr call_ret_t376; tll_ptr ifte_ret_t379; tll_ptr switch_ret_t375;
  tll_ptr switch_ret_t378; tll_ptr x_v18225; tll_ptr xs_v18224;
  if (n_v18220) {
    switch(((tll_node)xs_v18221)->tag) {
      case 26:
        switch_ret_t375 = a_v18222;
        break;
      case 27:
        __v18223 = ((tll_node)xs_v18221)->data[0];
        xs_v18224 = ((tll_node)xs_v18221)->data[1];
        add_ret_t377 = (tll_ptr)((long)n_v18220 - 1);
        call_ret_t376 = get_at_i37(0, add_ret_t377, xs_v18224, a_v18222);
        switch_ret_t375 = call_ret_t376;
        break;
    }
    ifte_ret_t379 = switch_ret_t375;
  }
  else {
    switch(((tll_node)xs_v18221)->tag) {
      case 26:
        switch_ret_t378 = a_v18222;
        break;
      case 27:
        x_v18225 = ((tll_node)xs_v18221)->data[0];
        __v18226 = ((tll_node)xs_v18221)->data[1];
        switch_ret_t378 = x_v18225;
        break;
    }
    ifte_ret_t379 = switch_ret_t378;
  }
  return ifte_ret_t379;
}

tll_ptr lam_fun_t381(tll_ptr a_v18236, tll_env env) {
  tll_ptr call_ret_t380;
  call_ret_t380 = get_at_i37(env[2], env[1], env[0], a_v18236);
  return call_ret_t380;
}

tll_ptr lam_fun_t383(tll_ptr xs_v18234, tll_env env) {
  tll_ptr lam_clo_t382;
  instr_clo(&lam_clo_t382, &lam_fun_t381, 3, xs_v18234, env[0], env[1]);
  return lam_clo_t382;
}

tll_ptr lam_fun_t385(tll_ptr n_v18231, tll_env env) {
  tll_ptr lam_clo_t384;
  instr_clo(&lam_clo_t384, &lam_fun_t383, 2, n_v18231, env[0]);
  return lam_clo_t384;
}

tll_ptr lam_fun_t387(tll_ptr A_v18227, tll_env env) {
  tll_ptr lam_clo_t386;
  instr_clo(&lam_clo_t386, &lam_fun_t385, 1, A_v18227);
  return lam_clo_t386;
}

tll_ptr string_of_digit_i38(tll_ptr n_v18237) {
  tll_ptr EmptyString_t390; tll_ptr call_ret_t389;
  instr_struct(&EmptyString_t390, 6, 0);
  call_ret_t389 = get_at_i37(0, n_v18237, digits_i36, EmptyString_t390);
  return call_ret_t389;
}

tll_ptr lam_fun_t392(tll_ptr n_v18238, tll_env env) {
  tll_ptr call_ret_t391;
  call_ret_t391 = string_of_digit_i38(n_v18238);
  return call_ret_t391;
}

tll_ptr string_of_nat_i39(tll_ptr n_v18239) {
  tll_ptr call_ret_t394; tll_ptr call_ret_t395; tll_ptr call_ret_t396;
  tll_ptr call_ret_t397; tll_ptr call_ret_t398; tll_ptr call_ret_t399;
  tll_ptr ifte_ret_t400; tll_ptr n_v18241; tll_ptr s_v18240;
  call_ret_t395 = modn_i16(n_v18239, (tll_ptr)10);
  call_ret_t394 = string_of_digit_i38(call_ret_t395);
  s_v18240 = call_ret_t394;
  call_ret_t396 = divn_i15(n_v18239, (tll_ptr)10);
  n_v18241 = call_ret_t396;
  call_ret_t397 = ltn_i6((tll_ptr)0, n_v18241);
  if (call_ret_t397) {
    call_ret_t399 = string_of_nat_i39(n_v18241);
    call_ret_t398 = cats_i19(call_ret_t399, s_v18240);
    ifte_ret_t400 = call_ret_t398;
  }
  else {
    ifte_ret_t400 = s_v18240;
  }
  return ifte_ret_t400;
}

tll_ptr lam_fun_t402(tll_ptr n_v18242, tll_env env) {
  tll_ptr call_ret_t401;
  call_ret_t401 = string_of_nat_i39(n_v18242);
  return call_ret_t401;
}

tll_ptr digit_of_char_i40(tll_ptr c_v18243) {
  tll_ptr Char_t405; tll_ptr Char_t408; tll_ptr Char_t411; tll_ptr Char_t414;
  tll_ptr Char_t417; tll_ptr Char_t420; tll_ptr Char_t423; tll_ptr Char_t426;
  tll_ptr Char_t429; tll_ptr Char_t432; tll_ptr NoneUL_t434;
  tll_ptr SomeUL_t406; tll_ptr SomeUL_t409; tll_ptr SomeUL_t412;
  tll_ptr SomeUL_t415; tll_ptr SomeUL_t418; tll_ptr SomeUL_t421;
  tll_ptr SomeUL_t424; tll_ptr SomeUL_t427; tll_ptr SomeUL_t430;
  tll_ptr SomeUL_t433; tll_ptr call_ret_t404; tll_ptr call_ret_t407;
  tll_ptr call_ret_t410; tll_ptr call_ret_t413; tll_ptr call_ret_t416;
  tll_ptr call_ret_t419; tll_ptr call_ret_t422; tll_ptr call_ret_t425;
  tll_ptr call_ret_t428; tll_ptr call_ret_t431; tll_ptr ifte_ret_t435;
  tll_ptr ifte_ret_t436; tll_ptr ifte_ret_t437; tll_ptr ifte_ret_t438;
  tll_ptr ifte_ret_t439; tll_ptr ifte_ret_t440; tll_ptr ifte_ret_t441;
  tll_ptr ifte_ret_t442; tll_ptr ifte_ret_t443; tll_ptr ifte_ret_t444;
  instr_struct(&Char_t405, 5, 1, (tll_ptr)48);
  call_ret_t404 = eqc_i17(c_v18243, Char_t405);
  if (call_ret_t404) {
    instr_struct(&SomeUL_t406, 17, 1, (tll_ptr)0);
    ifte_ret_t444 = SomeUL_t406;
  }
  else {
    instr_struct(&Char_t408, 5, 1, (tll_ptr)49);
    call_ret_t407 = eqc_i17(c_v18243, Char_t408);
    if (call_ret_t407) {
      instr_struct(&SomeUL_t409, 17, 1, (tll_ptr)1);
      ifte_ret_t443 = SomeUL_t409;
    }
    else {
      instr_struct(&Char_t411, 5, 1, (tll_ptr)50);
      call_ret_t410 = eqc_i17(c_v18243, Char_t411);
      if (call_ret_t410) {
        instr_struct(&SomeUL_t412, 17, 1, (tll_ptr)2);
        ifte_ret_t442 = SomeUL_t412;
      }
      else {
        instr_struct(&Char_t414, 5, 1, (tll_ptr)51);
        call_ret_t413 = eqc_i17(c_v18243, Char_t414);
        if (call_ret_t413) {
          instr_struct(&SomeUL_t415, 17, 1, (tll_ptr)3);
          ifte_ret_t441 = SomeUL_t415;
        }
        else {
          instr_struct(&Char_t417, 5, 1, (tll_ptr)52);
          call_ret_t416 = eqc_i17(c_v18243, Char_t417);
          if (call_ret_t416) {
            instr_struct(&SomeUL_t418, 17, 1, (tll_ptr)4);
            ifte_ret_t440 = SomeUL_t418;
          }
          else {
            instr_struct(&Char_t420, 5, 1, (tll_ptr)53);
            call_ret_t419 = eqc_i17(c_v18243, Char_t420);
            if (call_ret_t419) {
              instr_struct(&SomeUL_t421, 17, 1, (tll_ptr)5);
              ifte_ret_t439 = SomeUL_t421;
            }
            else {
              instr_struct(&Char_t423, 5, 1, (tll_ptr)54);
              call_ret_t422 = eqc_i17(c_v18243, Char_t423);
              if (call_ret_t422) {
                instr_struct(&SomeUL_t424, 17, 1, (tll_ptr)6);
                ifte_ret_t438 = SomeUL_t424;
              }
              else {
                instr_struct(&Char_t426, 5, 1, (tll_ptr)55);
                call_ret_t425 = eqc_i17(c_v18243, Char_t426);
                if (call_ret_t425) {
                  instr_struct(&SomeUL_t427, 17, 1, (tll_ptr)7);
                  ifte_ret_t437 = SomeUL_t427;
                }
                else {
                  instr_struct(&Char_t429, 5, 1, (tll_ptr)56);
                  call_ret_t428 = eqc_i17(c_v18243, Char_t429);
                  if (call_ret_t428) {
                    instr_struct(&SomeUL_t430, 17, 1, (tll_ptr)8);
                    ifte_ret_t436 = SomeUL_t430;
                  }
                  else {
                    instr_struct(&Char_t432, 5, 1, (tll_ptr)57);
                    call_ret_t431 = eqc_i17(c_v18243, Char_t432);
                    if (call_ret_t431) {
                      instr_struct(&SomeUL_t433, 17, 1, (tll_ptr)9);
                      ifte_ret_t435 = SomeUL_t433;
                    }
                    else {
                      instr_struct(&NoneUL_t434, 16, 0);
                      ifte_ret_t435 = NoneUL_t434;
                    }
                    ifte_ret_t436 = ifte_ret_t435;
                  }
                  ifte_ret_t437 = ifte_ret_t436;
                }
                ifte_ret_t438 = ifte_ret_t437;
              }
              ifte_ret_t439 = ifte_ret_t438;
            }
            ifte_ret_t440 = ifte_ret_t439;
          }
          ifte_ret_t441 = ifte_ret_t440;
        }
        ifte_ret_t442 = ifte_ret_t441;
      }
      ifte_ret_t443 = ifte_ret_t442;
    }
    ifte_ret_t444 = ifte_ret_t443;
  }
  return ifte_ret_t444;
}

tll_ptr lam_fun_t446(tll_ptr c_v18244, tll_env env) {
  tll_ptr call_ret_t445;
  call_ret_t445 = digit_of_char_i40(c_v18244);
  return call_ret_t445;
}

tll_ptr nat_of_string_loop_i41(tll_ptr s_v18245, tll_ptr acc_v18246) {
  tll_ptr NoneUL_t452; tll_ptr SomeUL_t449; tll_ptr c_v18247;
  tll_ptr call_ret_t450; tll_ptr call_ret_t453; tll_ptr call_ret_t454;
  tll_ptr call_ret_t455; tll_ptr n_v18249; tll_ptr s_v18248;
  tll_ptr switch_ret_t448; tll_ptr switch_ret_t451;
  switch(((tll_node)s_v18245)->tag) {
    case 6:
      instr_struct(&SomeUL_t449, 17, 1, acc_v18246);
      switch_ret_t448 = SomeUL_t449;
      break;
    case 7:
      c_v18247 = ((tll_node)s_v18245)->data[0];
      s_v18248 = ((tll_node)s_v18245)->data[1];
      call_ret_t450 = digit_of_char_i40(c_v18247);
      switch(((tll_node)call_ret_t450)->tag) {
        case 16:
          instr_free_struct(call_ret_t450);
          instr_struct(&NoneUL_t452, 16, 0);
          switch_ret_t451 = NoneUL_t452;
          break;
        case 17:
          n_v18249 = ((tll_node)call_ret_t450)->data[0];
          instr_free_struct(call_ret_t450);
          call_ret_t455 = muln_i14(acc_v18246, (tll_ptr)10);
          call_ret_t454 = addn_i12(call_ret_t455, n_v18249);
          call_ret_t453 = nat_of_string_loop_i41(s_v18248, call_ret_t454);
          switch_ret_t451 = call_ret_t453;
          break;
      }
      switch_ret_t448 = switch_ret_t451;
      break;
  }
  return switch_ret_t448;
}

tll_ptr lam_fun_t457(tll_ptr acc_v18252, tll_env env) {
  tll_ptr call_ret_t456;
  call_ret_t456 = nat_of_string_loop_i41(env[0], acc_v18252);
  return call_ret_t456;
}

tll_ptr lam_fun_t459(tll_ptr s_v18250, tll_env env) {
  tll_ptr lam_clo_t458;
  instr_clo(&lam_clo_t458, &lam_fun_t457, 1, s_v18250);
  return lam_clo_t458;
}

tll_ptr nat_of_string_i42(tll_ptr s_v18253) {
  tll_ptr call_ret_t461;
  call_ret_t461 = nat_of_string_loop_i41(s_v18253, (tll_ptr)0);
  return call_ret_t461;
}

tll_ptr lam_fun_t463(tll_ptr s_v18254, tll_env env) {
  tll_ptr call_ret_t462;
  call_ret_t462 = nat_of_string_i42(s_v18254);
  return call_ret_t462;
}

tll_ptr pow_i43(tll_ptr n_v18255, tll_ptr m_v18256) {
  tll_ptr add_ret_t467; tll_ptr call_ret_t465; tll_ptr call_ret_t466;
  tll_ptr ifte_ret_t468;
  if (m_v18256) {
    add_ret_t467 = (tll_ptr)((long)m_v18256 - 1);
    call_ret_t466 = pow_i43(n_v18255, add_ret_t467);
    call_ret_t465 = muln_i14(n_v18255, call_ret_t466);
    ifte_ret_t468 = call_ret_t465;
  }
  else {
    ifte_ret_t468 = (tll_ptr)1;
  }
  return ifte_ret_t468;
}

tll_ptr lam_fun_t470(tll_ptr m_v18259, tll_env env) {
  tll_ptr call_ret_t469;
  call_ret_t469 = pow_i43(env[0], m_v18259);
  return call_ret_t469;
}

tll_ptr lam_fun_t472(tll_ptr n_v18257, tll_env env) {
  tll_ptr lam_clo_t471;
  instr_clo(&lam_clo_t471, &lam_fun_t470, 1, n_v18257);
  return lam_clo_t471;
}

tll_ptr lam_fun_t492(tll_ptr __v18264, tll_env env) {
  tll_ptr B_v18280; tll_ptr Char_t488; tll_ptr EmptyString_t489;
  tll_ptr String_t490; tll_ptr __v18279; tll_ptr app_ret_t491;
  tll_ptr b_v18277; tll_ptr call_ret_t474; tll_ptr call_ret_t475;
  tll_ptr call_ret_t483; tll_ptr call_ret_t484; tll_ptr call_ret_t485;
  tll_ptr call_ret_t486; tll_ptr call_ret_t487; tll_ptr ch_v18275;
  tll_ptr ch_v18278; tll_ptr ch_v18281; tll_ptr ch_v18283;
  tll_ptr pair_struct_t477; tll_ptr pair_struct_t481; tll_ptr pf_v18282;
  tll_ptr recv_msg_t479; tll_ptr s_v18284; tll_ptr send_ch_t476;
  tll_ptr switch_ret_t478; tll_ptr switch_ret_t480; tll_ptr switch_ret_t482;
  tll_ptr x_v18276;
  call_ret_t475 = pow_i43(env[1], env[3]);
  call_ret_t474 = modn_i16(call_ret_t475, env[2]);
  x_v18276 = call_ret_t474;
  instr_send(&send_ch_t476, env[0], x_v18276);
  ch_v18275 = send_ch_t476;
  instr_struct(&pair_struct_t477, 0, 2, 0, ch_v18275);
  switch(((tll_node)pair_struct_t477)->tag) {
    case 0:
      b_v18277 = ((tll_node)pair_struct_t477)->data[0];
      ch_v18278 = ((tll_node)pair_struct_t477)->data[1];
      instr_free_struct(pair_struct_t477);
      instr_recv(&recv_msg_t479, ch_v18278);
      __v18279 = recv_msg_t479;
      switch(((tll_node)__v18279)->tag) {
        case 0:
          B_v18280 = ((tll_node)__v18279)->data[0];
          ch_v18281 = ((tll_node)__v18279)->data[1];
          instr_free_struct(__v18279);
          instr_struct(&pair_struct_t481, 0, 2, 0, ch_v18281);
          switch(((tll_node)pair_struct_t481)->tag) {
            case 0:
              pf_v18282 = ((tll_node)pair_struct_t481)->data[0];
              ch_v18283 = ((tll_node)pair_struct_t481)->data[1];
              instr_free_struct(pair_struct_t481);
              call_ret_t484 = pow_i43(B_v18280, env[3]);
              call_ret_t483 = modn_i16(call_ret_t484, env[2]);
              s_v18284 = call_ret_t483;
              call_ret_t487 = string_of_nat_i39(s_v18284);
              instr_struct(&Char_t488, 5, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t489, 6, 0);
              instr_struct(&String_t490, 7, 2, Char_t488, EmptyString_t489);
              call_ret_t486 = cats_i19(call_ret_t487, String_t490);
              call_ret_t485 = print_i34(call_ret_t486);
              instr_app(&app_ret_t491, call_ret_t485, 0);
              instr_free_clo(call_ret_t485);
              switch_ret_t482 = app_ret_t491;
              break;
          }
          switch_ret_t480 = switch_ret_t482;
          break;
      }
      switch_ret_t478 = switch_ret_t480;
      break;
  }
  return switch_ret_t478;
}

tll_ptr alice_i47(tll_ptr a_v18260, tll_ptr p_v18261, tll_ptr g_v18262, tll_ptr ch_v18263) {
  tll_ptr lam_clo_t493;
  instr_clo(&lam_clo_t493, &lam_fun_t492, 4,
            ch_v18263, g_v18262, p_v18261, a_v18260);
  return lam_clo_t493;
}

tll_ptr lam_fun_t495(tll_ptr ch_v18294, tll_env env) {
  tll_ptr call_ret_t494;
  call_ret_t494 = alice_i47(env[2], env[1], env[0], ch_v18294);
  return call_ret_t494;
}

tll_ptr lam_fun_t497(tll_ptr g_v18292, tll_env env) {
  tll_ptr lam_clo_t496;
  instr_clo(&lam_clo_t496, &lam_fun_t495, 3, g_v18292, env[0], env[1]);
  return lam_clo_t496;
}

tll_ptr lam_fun_t499(tll_ptr p_v18289, tll_env env) {
  tll_ptr lam_clo_t498;
  instr_clo(&lam_clo_t498, &lam_fun_t497, 2, p_v18289, env[0]);
  return lam_clo_t498;
}

tll_ptr lam_fun_t501(tll_ptr a_v18285, tll_env env) {
  tll_ptr lam_clo_t500;
  instr_clo(&lam_clo_t500, &lam_fun_t499, 1, a_v18285);
  return lam_clo_t500;
}

tll_ptr lam_fun_t522(tll_ptr __v18299, tll_env env) {
  tll_ptr A_v18314; tll_ptr Char_t518; tll_ptr EmptyString_t519;
  tll_ptr String_t520; tll_ptr __v18313; tll_ptr __v18321; tll_ptr a_v18311;
  tll_ptr app_ret_t521; tll_ptr call_ret_t509; tll_ptr call_ret_t510;
  tll_ptr call_ret_t512; tll_ptr call_ret_t513; tll_ptr call_ret_t515;
  tll_ptr call_ret_t516; tll_ptr call_ret_t517; tll_ptr ch_v18312;
  tll_ptr ch_v18315; tll_ptr ch_v18317; tll_ptr ch_v18318;
  tll_ptr close_tmp_t514; tll_ptr pair_struct_t503; tll_ptr pair_struct_t507;
  tll_ptr pf_v18316; tll_ptr recv_msg_t505; tll_ptr s_v18320;
  tll_ptr send_ch_t511; tll_ptr switch_ret_t504; tll_ptr switch_ret_t506;
  tll_ptr switch_ret_t508; tll_ptr x_v18319;
  instr_struct(&pair_struct_t503, 0, 2, 0, env[0]);
  switch(((tll_node)pair_struct_t503)->tag) {
    case 0:
      a_v18311 = ((tll_node)pair_struct_t503)->data[0];
      ch_v18312 = ((tll_node)pair_struct_t503)->data[1];
      instr_free_struct(pair_struct_t503);
      instr_recv(&recv_msg_t505, ch_v18312);
      __v18313 = recv_msg_t505;
      switch(((tll_node)__v18313)->tag) {
        case 0:
          A_v18314 = ((tll_node)__v18313)->data[0];
          ch_v18315 = ((tll_node)__v18313)->data[1];
          instr_free_struct(__v18313);
          instr_struct(&pair_struct_t507, 0, 2, 0, ch_v18315);
          switch(((tll_node)pair_struct_t507)->tag) {
            case 0:
              pf_v18316 = ((tll_node)pair_struct_t507)->data[0];
              ch_v18317 = ((tll_node)pair_struct_t507)->data[1];
              instr_free_struct(pair_struct_t507);
              call_ret_t510 = pow_i43(env[1], env[3]);
              call_ret_t509 = modn_i16(call_ret_t510, env[2]);
              x_v18319 = call_ret_t509;
              instr_send(&send_ch_t511, ch_v18317, x_v18319);
              ch_v18318 = send_ch_t511;
              call_ret_t513 = pow_i43(A_v18314, env[3]);
              call_ret_t512 = modn_i16(call_ret_t513, env[2]);
              s_v18320 = call_ret_t512;
              instr_close(&close_tmp_t514, ch_v18318);
              __v18321 = close_tmp_t514;
              call_ret_t517 = string_of_nat_i39(s_v18320);
              instr_struct(&Char_t518, 5, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t519, 6, 0);
              instr_struct(&String_t520, 7, 2, Char_t518, EmptyString_t519);
              call_ret_t516 = cats_i19(call_ret_t517, String_t520);
              call_ret_t515 = print_i34(call_ret_t516);
              instr_app(&app_ret_t521, call_ret_t515, 0);
              instr_free_clo(call_ret_t515);
              switch_ret_t508 = app_ret_t521;
              break;
          }
          switch_ret_t506 = switch_ret_t508;
          break;
      }
      switch_ret_t504 = switch_ret_t506;
      break;
  }
  return switch_ret_t504;
}

tll_ptr bob_i48(tll_ptr b_v18295, tll_ptr p_v18296, tll_ptr g_v18297, tll_ptr ch_v18298) {
  tll_ptr lam_clo_t523;
  instr_clo(&lam_clo_t523, &lam_fun_t522, 4,
            ch_v18298, g_v18297, p_v18296, b_v18295);
  return lam_clo_t523;
}

tll_ptr lam_fun_t525(tll_ptr ch_v18331, tll_env env) {
  tll_ptr call_ret_t524;
  call_ret_t524 = bob_i48(env[2], env[1], env[0], ch_v18331);
  return call_ret_t524;
}

tll_ptr lam_fun_t527(tll_ptr g_v18329, tll_env env) {
  tll_ptr lam_clo_t526;
  instr_clo(&lam_clo_t526, &lam_fun_t525, 3, g_v18329, env[0], env[1]);
  return lam_clo_t526;
}

tll_ptr lam_fun_t529(tll_ptr p_v18326, tll_env env) {
  tll_ptr lam_clo_t528;
  instr_clo(&lam_clo_t528, &lam_fun_t527, 2, p_v18326, env[0]);
  return lam_clo_t528;
}

tll_ptr lam_fun_t531(tll_ptr b_v18322, tll_env env) {
  tll_ptr lam_clo_t530;
  instr_clo(&lam_clo_t530, &lam_fun_t529, 1, b_v18322);
  return lam_clo_t530;
}

tll_ptr fork_fun_t535(tll_env env) {
  tll_ptr app_ret_t534; tll_ptr call_ret_t533; tll_ptr fork_ret_t537;
  call_ret_t533 = alice_i47((tll_ptr)4, (tll_ptr)23, (tll_ptr)5, env[0]);
  instr_app(&app_ret_t534, call_ret_t533, 0);
  instr_free_clo(call_ret_t533);
  fork_ret_t537 = app_ret_t534;
  instr_free_thread(env);
  return fork_ret_t537;
}

tll_ptr fork_fun_t542(tll_env env) {
  tll_ptr __v18349; tll_ptr app_ret_t541; tll_ptr c0_v18351;
  tll_ptr c_v18350; tll_ptr call_ret_t540; tll_ptr fork_ret_t544;
  tll_ptr recv_msg_t538; tll_ptr switch_ret_t539;
  instr_recv(&recv_msg_t538, env[0]);
  __v18349 = recv_msg_t538;
  switch(((tll_node)__v18349)->tag) {
    case 0:
      c_v18350 = ((tll_node)__v18349)->data[0];
      c0_v18351 = ((tll_node)__v18349)->data[1];
      instr_free_struct(__v18349);
      call_ret_t540 = bob_i48((tll_ptr)3, (tll_ptr)23, (tll_ptr)5, c_v18350);
      instr_app(&app_ret_t541, call_ret_t540, 0);
      instr_free_clo(call_ret_t540);
      switch_ret_t539 = app_ret_t541;
      break;
  }
  fork_ret_t544 = switch_ret_t539;
  instr_free_thread(env);
  return fork_ret_t544;
}

tll_ptr lam_fun_t547(tll_ptr __v18333, tll_env env) {
  tll_ptr c0_v18344; tll_ptr c0_v18352; tll_ptr c_v18342;
  tll_ptr close_tmp_t546; tll_ptr fork_ch_t536; tll_ptr fork_ch_t543;
  tll_ptr send_ch_t545;
  instr_fork(&fork_ch_t536, &fork_fun_t535, 0);
  c_v18342 = fork_ch_t536;
  instr_fork(&fork_ch_t543, &fork_fun_t542, 0);
  c0_v18344 = fork_ch_t543;
  instr_send(&send_ch_t545, c0_v18344, c_v18342);
  c0_v18352 = send_ch_t545;
  instr_close(&close_tmp_t546, c0_v18352);
  return close_tmp_t546;
}

tll_ptr key_exchange_i49(tll_ptr __v18332) {
  tll_ptr lam_clo_t548;
  instr_clo(&lam_clo_t548, &lam_fun_t547, 0);
  return lam_clo_t548;
}

tll_ptr lam_fun_t550(tll_ptr __v18353, tll_env env) {
  tll_ptr call_ret_t549;
  call_ret_t549 = key_exchange_i49(__v18353);
  return call_ret_t549;
}

int main() {
  instr_init();
  tll_ptr Char_t334; tll_ptr Char_t337; tll_ptr Char_t340; tll_ptr Char_t343;
  tll_ptr Char_t346; tll_ptr Char_t349; tll_ptr Char_t352; tll_ptr Char_t355;
  tll_ptr Char_t358; tll_ptr Char_t361; tll_ptr EmptyString_t335;
  tll_ptr EmptyString_t338; tll_ptr EmptyString_t341;
  tll_ptr EmptyString_t344; tll_ptr EmptyString_t347;
  tll_ptr EmptyString_t350; tll_ptr EmptyString_t353;
  tll_ptr EmptyString_t356; tll_ptr EmptyString_t359;
  tll_ptr EmptyString_t362; tll_ptr String_t336; tll_ptr String_t339;
  tll_ptr String_t342; tll_ptr String_t345; tll_ptr String_t348;
  tll_ptr String_t351; tll_ptr String_t354; tll_ptr String_t357;
  tll_ptr String_t360; tll_ptr String_t363; tll_ptr app_ret_t553;
  tll_ptr call_ret_t552; tll_ptr consUU_t365; tll_ptr consUU_t366;
  tll_ptr consUU_t367; tll_ptr consUU_t368; tll_ptr consUU_t369;
  tll_ptr consUU_t370; tll_ptr consUU_t371; tll_ptr consUU_t372;
  tll_ptr consUU_t373; tll_ptr consUU_t374; tll_ptr lam_clo_t101;
  tll_ptr lam_clo_t107; tll_ptr lam_clo_t115; tll_ptr lam_clo_t12;
  tll_ptr lam_clo_t123; tll_ptr lam_clo_t131; tll_ptr lam_clo_t137;
  tll_ptr lam_clo_t148; tll_ptr lam_clo_t16; tll_ptr lam_clo_t164;
  tll_ptr lam_clo_t176; tll_ptr lam_clo_t188; tll_ptr lam_clo_t200;
  tll_ptr lam_clo_t212; tll_ptr lam_clo_t224; tll_ptr lam_clo_t236;
  tll_ptr lam_clo_t249; tll_ptr lam_clo_t262; tll_ptr lam_clo_t275;
  tll_ptr lam_clo_t28; tll_ptr lam_clo_t285; tll_ptr lam_clo_t295;
  tll_ptr lam_clo_t305; tll_ptr lam_clo_t315; tll_ptr lam_clo_t324;
  tll_ptr lam_clo_t333; tll_ptr lam_clo_t34; tll_ptr lam_clo_t388;
  tll_ptr lam_clo_t393; tll_ptr lam_clo_t40; tll_ptr lam_clo_t403;
  tll_ptr lam_clo_t447; tll_ptr lam_clo_t46; tll_ptr lam_clo_t460;
  tll_ptr lam_clo_t464; tll_ptr lam_clo_t473; tll_ptr lam_clo_t502;
  tll_ptr lam_clo_t52; tll_ptr lam_clo_t532; tll_ptr lam_clo_t551;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t6; tll_ptr lam_clo_t72;
  tll_ptr lam_clo_t77; tll_ptr lam_clo_t83; tll_ptr lam_clo_t89;
  tll_ptr lam_clo_t95; tll_ptr nilUU_t364;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i71 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i72 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i73 = lam_clo_t16;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  comparebclo_i74 = lam_clo_t28;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 0);
  ltenclo_i75 = lam_clo_t34;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 0);
  ltnclo_i76 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  gtenclo_i77 = lam_clo_t46;
  instr_clo(&lam_clo_t52, &lam_fun_t51, 0);
  gtnclo_i78 = lam_clo_t52;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  eqnclo_i79 = lam_clo_t58;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  comparenclo_i80 = lam_clo_t72;
  instr_clo(&lam_clo_t77, &lam_fun_t76, 0);
  predclo_i81 = lam_clo_t77;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i82 = lam_clo_t83;
  instr_clo(&lam_clo_t89, &lam_fun_t88, 0);
  subnclo_i83 = lam_clo_t89;
  instr_clo(&lam_clo_t95, &lam_fun_t94, 0);
  mulnclo_i84 = lam_clo_t95;
  instr_clo(&lam_clo_t101, &lam_fun_t100, 0);
  divnclo_i85 = lam_clo_t101;
  instr_clo(&lam_clo_t107, &lam_fun_t106, 0);
  modnclo_i86 = lam_clo_t107;
  instr_clo(&lam_clo_t115, &lam_fun_t114, 0);
  eqcclo_i87 = lam_clo_t115;
  instr_clo(&lam_clo_t123, &lam_fun_t122, 0);
  comparecclo_i88 = lam_clo_t123;
  instr_clo(&lam_clo_t131, &lam_fun_t130, 0);
  catsclo_i89 = lam_clo_t131;
  instr_clo(&lam_clo_t137, &lam_fun_t136, 0);
  strlenclo_i90 = lam_clo_t137;
  instr_clo(&lam_clo_t148, &lam_fun_t147, 0);
  eqsclo_i91 = lam_clo_t148;
  instr_clo(&lam_clo_t164, &lam_fun_t163, 0);
  comparesclo_i92 = lam_clo_t164;
  instr_clo(&lam_clo_t176, &lam_fun_t175, 0);
  and_thenUUUclo_i93 = lam_clo_t176;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 0);
  and_thenUULclo_i94 = lam_clo_t188;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 0);
  and_thenULUclo_i95 = lam_clo_t200;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  and_thenULLclo_i96 = lam_clo_t212;
  instr_clo(&lam_clo_t224, &lam_fun_t223, 0);
  and_thenLULclo_i97 = lam_clo_t224;
  instr_clo(&lam_clo_t236, &lam_fun_t235, 0);
  and_thenLLLclo_i98 = lam_clo_t236;
  instr_clo(&lam_clo_t249, &lam_fun_t248, 0);
  lenUUclo_i99 = lam_clo_t249;
  instr_clo(&lam_clo_t262, &lam_fun_t261, 0);
  lenULclo_i100 = lam_clo_t262;
  instr_clo(&lam_clo_t275, &lam_fun_t274, 0);
  lenLLclo_i101 = lam_clo_t275;
  instr_clo(&lam_clo_t285, &lam_fun_t284, 0);
  appendUUclo_i102 = lam_clo_t285;
  instr_clo(&lam_clo_t295, &lam_fun_t294, 0);
  appendULclo_i103 = lam_clo_t295;
  instr_clo(&lam_clo_t305, &lam_fun_t304, 0);
  appendLLclo_i104 = lam_clo_t305;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 0);
  readlineclo_i105 = lam_clo_t315;
  instr_clo(&lam_clo_t324, &lam_fun_t323, 0);
  printclo_i106 = lam_clo_t324;
  instr_clo(&lam_clo_t333, &lam_fun_t332, 0);
  prerrclo_i107 = lam_clo_t333;
  instr_struct(&Char_t334, 5, 1, (tll_ptr)48);
  instr_struct(&EmptyString_t335, 6, 0);
  instr_struct(&String_t336, 7, 2, Char_t334, EmptyString_t335);
  instr_struct(&Char_t337, 5, 1, (tll_ptr)49);
  instr_struct(&EmptyString_t338, 6, 0);
  instr_struct(&String_t339, 7, 2, Char_t337, EmptyString_t338);
  instr_struct(&Char_t340, 5, 1, (tll_ptr)50);
  instr_struct(&EmptyString_t341, 6, 0);
  instr_struct(&String_t342, 7, 2, Char_t340, EmptyString_t341);
  instr_struct(&Char_t343, 5, 1, (tll_ptr)51);
  instr_struct(&EmptyString_t344, 6, 0);
  instr_struct(&String_t345, 7, 2, Char_t343, EmptyString_t344);
  instr_struct(&Char_t346, 5, 1, (tll_ptr)52);
  instr_struct(&EmptyString_t347, 6, 0);
  instr_struct(&String_t348, 7, 2, Char_t346, EmptyString_t347);
  instr_struct(&Char_t349, 5, 1, (tll_ptr)53);
  instr_struct(&EmptyString_t350, 6, 0);
  instr_struct(&String_t351, 7, 2, Char_t349, EmptyString_t350);
  instr_struct(&Char_t352, 5, 1, (tll_ptr)54);
  instr_struct(&EmptyString_t353, 6, 0);
  instr_struct(&String_t354, 7, 2, Char_t352, EmptyString_t353);
  instr_struct(&Char_t355, 5, 1, (tll_ptr)55);
  instr_struct(&EmptyString_t356, 6, 0);
  instr_struct(&String_t357, 7, 2, Char_t355, EmptyString_t356);
  instr_struct(&Char_t358, 5, 1, (tll_ptr)56);
  instr_struct(&EmptyString_t359, 6, 0);
  instr_struct(&String_t360, 7, 2, Char_t358, EmptyString_t359);
  instr_struct(&Char_t361, 5, 1, (tll_ptr)57);
  instr_struct(&EmptyString_t362, 6, 0);
  instr_struct(&String_t363, 7, 2, Char_t361, EmptyString_t362);
  instr_struct(&nilUU_t364, 26, 0);
  instr_struct(&consUU_t365, 27, 2, String_t363, nilUU_t364);
  instr_struct(&consUU_t366, 27, 2, String_t360, consUU_t365);
  instr_struct(&consUU_t367, 27, 2, String_t357, consUU_t366);
  instr_struct(&consUU_t368, 27, 2, String_t354, consUU_t367);
  instr_struct(&consUU_t369, 27, 2, String_t351, consUU_t368);
  instr_struct(&consUU_t370, 27, 2, String_t348, consUU_t369);
  instr_struct(&consUU_t371, 27, 2, String_t345, consUU_t370);
  instr_struct(&consUU_t372, 27, 2, String_t342, consUU_t371);
  instr_struct(&consUU_t373, 27, 2, String_t339, consUU_t372);
  instr_struct(&consUU_t374, 27, 2, String_t336, consUU_t373);
  digits_i36 = consUU_t374;
  instr_clo(&lam_clo_t388, &lam_fun_t387, 0);
  get_atclo_i108 = lam_clo_t388;
  instr_clo(&lam_clo_t393, &lam_fun_t392, 0);
  string_of_digitclo_i109 = lam_clo_t393;
  instr_clo(&lam_clo_t403, &lam_fun_t402, 0);
  string_of_natclo_i110 = lam_clo_t403;
  instr_clo(&lam_clo_t447, &lam_fun_t446, 0);
  digit_of_charclo_i111 = lam_clo_t447;
  instr_clo(&lam_clo_t460, &lam_fun_t459, 0);
  nat_of_string_loopclo_i112 = lam_clo_t460;
  instr_clo(&lam_clo_t464, &lam_fun_t463, 0);
  nat_of_stringclo_i113 = lam_clo_t464;
  instr_clo(&lam_clo_t473, &lam_fun_t472, 0);
  powclo_i114 = lam_clo_t473;
  instr_clo(&lam_clo_t502, &lam_fun_t501, 0);
  aliceclo_i115 = lam_clo_t502;
  instr_clo(&lam_clo_t532, &lam_fun_t531, 0);
  bobclo_i116 = lam_clo_t532;
  instr_clo(&lam_clo_t551, &lam_fun_t550, 0);
  key_exchangeclo_i117 = lam_clo_t551;
  call_ret_t552 = key_exchange_i49(0);
  instr_app(&app_ret_t553, call_ret_t552, 0);
  instr_free_clo(call_ret_t552);
  instr_exit();
}

