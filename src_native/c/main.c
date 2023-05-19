#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v12022, tll_ptr b2_v12023);
tll_ptr orb_i2(tll_ptr b1_v12027, tll_ptr b2_v12028);
tll_ptr notb_i3(tll_ptr b_v12032);
tll_ptr compareb_i4(tll_ptr b1_v12034, tll_ptr b2_v12035);
tll_ptr lten_i5(tll_ptr x_v12039, tll_ptr y_v12040);
tll_ptr ltn_i6(tll_ptr x_v12044, tll_ptr y_v12045);
tll_ptr gten_i7(tll_ptr x_v12049, tll_ptr y_v12050);
tll_ptr gtn_i8(tll_ptr x_v12054, tll_ptr y_v12055);
tll_ptr eqn_i9(tll_ptr x_v12059, tll_ptr y_v12060);
tll_ptr comparen_i10(tll_ptr n1_v12064, tll_ptr n2_v12065);
tll_ptr pred_i11(tll_ptr x_v12069);
tll_ptr addn_i12(tll_ptr x_v12071, tll_ptr y_v12072);
tll_ptr subn_i13(tll_ptr x_v12076, tll_ptr y_v12077);
tll_ptr muln_i14(tll_ptr x_v12081, tll_ptr y_v12082);
tll_ptr divn_i15(tll_ptr x_v12086, tll_ptr y_v12087);
tll_ptr modn_i16(tll_ptr x_v12091, tll_ptr y_v12092);
tll_ptr eqc_i17(tll_ptr c1_v12096, tll_ptr c2_v12097);
tll_ptr comparec_i18(tll_ptr c1_v12103, tll_ptr c2_v12104);
tll_ptr cats_i19(tll_ptr s1_v12110, tll_ptr s2_v12111);
tll_ptr strlen_i20(tll_ptr s_v12117);
tll_ptr eqs_i21(tll_ptr s1_v12121, tll_ptr s2_v12122);
tll_ptr compares_i22(tll_ptr s1_v12132, tll_ptr s2_v12133);
tll_ptr and_thenUUU_i52(tll_ptr A_v12143, tll_ptr B_v12144, tll_ptr opt_v12145, tll_ptr f_v12146);
tll_ptr and_thenUUL_i51(tll_ptr A_v12158, tll_ptr B_v12159, tll_ptr opt_v12160, tll_ptr f_v12161);
tll_ptr and_thenULU_i50(tll_ptr A_v12173, tll_ptr B_v12174, tll_ptr opt_v12175, tll_ptr f_v12176);
tll_ptr and_thenULL_i49(tll_ptr A_v12188, tll_ptr B_v12189, tll_ptr opt_v12190, tll_ptr f_v12191);
tll_ptr and_thenLUL_i47(tll_ptr A_v12203, tll_ptr B_v12204, tll_ptr opt_v12205, tll_ptr f_v12206);
tll_ptr and_thenLLL_i45(tll_ptr A_v12218, tll_ptr B_v12219, tll_ptr opt_v12220, tll_ptr f_v12221);
tll_ptr lenUU_i60(tll_ptr A_v12233, tll_ptr xs_v12234);
tll_ptr lenUL_i59(tll_ptr A_v12242, tll_ptr xs_v12243);
tll_ptr lenLL_i57(tll_ptr A_v12251, tll_ptr xs_v12252);
tll_ptr appendUU_i64(tll_ptr A_v12260, tll_ptr xs_v12261, tll_ptr ys_v12262);
tll_ptr appendUL_i63(tll_ptr A_v12271, tll_ptr xs_v12272, tll_ptr ys_v12273);
tll_ptr appendLL_i61(tll_ptr A_v12282, tll_ptr xs_v12283, tll_ptr ys_v12284);
tll_ptr readline_i33(tll_ptr __v12293);
tll_ptr print_i34(tll_ptr s_v12308);
tll_ptr prerr_i35(tll_ptr s_v12319);
tll_ptr get_at_i37(tll_ptr A_v12330, tll_ptr n_v12331, tll_ptr xs_v12332, tll_ptr a_v12333);
tll_ptr string_of_digit_i38(tll_ptr n_v12348);
tll_ptr string_of_nat_i39(tll_ptr n_v12350);
tll_ptr digit_of_char_i40(tll_ptr c_v12354);
tll_ptr nat_of_string_loop_i41(tll_ptr s_v12356, tll_ptr acc_v12357);
tll_ptr nat_of_string_i42(tll_ptr s_v12364);
tll_ptr ex_i43(tll_ptr e_v12366);

tll_ptr addnclo_i76;
tll_ptr and_thenLLLclo_i92;
tll_ptr and_thenLULclo_i91;
tll_ptr and_thenULLclo_i90;
tll_ptr and_thenULUclo_i89;
tll_ptr and_thenUULclo_i88;
tll_ptr and_thenUUUclo_i87;
tll_ptr andbclo_i65;
tll_ptr appendLLclo_i98;
tll_ptr appendULclo_i97;
tll_ptr appendUUclo_i96;
tll_ptr catsclo_i83;
tll_ptr comparebclo_i68;
tll_ptr comparecclo_i82;
tll_ptr comparenclo_i74;
tll_ptr comparesclo_i86;
tll_ptr digit_of_charclo_i105;
tll_ptr digits_i36;
tll_ptr divnclo_i79;
tll_ptr eqcclo_i81;
tll_ptr eqnclo_i73;
tll_ptr eqsclo_i85;
tll_ptr exclo_i108;
tll_ptr get_atclo_i102;
tll_ptr gtenclo_i71;
tll_ptr gtnclo_i72;
tll_ptr lenLLclo_i95;
tll_ptr lenULclo_i94;
tll_ptr lenUUclo_i93;
tll_ptr ltenclo_i69;
tll_ptr ltnclo_i70;
tll_ptr modnclo_i80;
tll_ptr mulnclo_i78;
tll_ptr nat_of_string_loopclo_i106;
tll_ptr nat_of_stringclo_i107;
tll_ptr notbclo_i67;
tll_ptr orbclo_i66;
tll_ptr predclo_i75;
tll_ptr prerrclo_i101;
tll_ptr printclo_i100;
tll_ptr readlineclo_i99;
tll_ptr string_of_digitclo_i103;
tll_ptr string_of_natclo_i104;
tll_ptr strlenclo_i84;
tll_ptr subnclo_i77;

tll_ptr andb_i1(tll_ptr b1_v12022, tll_ptr b2_v12023) {
  tll_ptr ifte_ret_t1;
  if (b1_v12022) {
    ifte_ret_t1 = b2_v12023;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v12026, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v12026);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v12024, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v12024);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v12027, tll_ptr b2_v12028) {
  tll_ptr ifte_ret_t7;
  if (b1_v12027) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v12028;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v12031, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v12031);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v12029, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v12029);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v12032) {
  tll_ptr ifte_ret_t13;
  if (b_v12032) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v12033, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v12033);
  return call_ret_t14;
}

tll_ptr compareb_i4(tll_ptr b1_v12034, tll_ptr b2_v12035) {
  tll_ptr EQ_t17; tll_ptr EQ_t21; tll_ptr GT_t18; tll_ptr LT_t20;
  tll_ptr ifte_ret_t19; tll_ptr ifte_ret_t22; tll_ptr ifte_ret_t23;
  if (b1_v12034) {
    if (b2_v12035) {
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
    if (b2_v12035) {
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

tll_ptr lam_fun_t25(tll_ptr b2_v12038, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = compareb_i4(env[0], b2_v12038);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr b1_v12036, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, b1_v12036);
  return lam_clo_t26;
}

tll_ptr lten_i5(tll_ptr x_v12039, tll_ptr y_v12040) {
  tll_ptr lten_ret_t29;
  instr_lten(&lten_ret_t29, x_v12039, y_v12040);
  return lten_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v12043, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = lten_i5(env[0], y_v12043);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v12041, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v12041);
  return lam_clo_t32;
}

tll_ptr ltn_i6(tll_ptr x_v12044, tll_ptr y_v12045) {
  tll_ptr ltn_ret_t35;
  instr_ltn(&ltn_ret_t35, x_v12044, y_v12045);
  return ltn_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v12048, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = ltn_i6(env[0], y_v12048);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v12046, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v12046);
  return lam_clo_t38;
}

tll_ptr gten_i7(tll_ptr x_v12049, tll_ptr y_v12050) {
  tll_ptr gten_ret_t41;
  instr_gten(&gten_ret_t41, x_v12049, y_v12050);
  return gten_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v12053, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = gten_i7(env[0], y_v12053);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v12051, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v12051);
  return lam_clo_t44;
}

tll_ptr gtn_i8(tll_ptr x_v12054, tll_ptr y_v12055) {
  tll_ptr gtn_ret_t47;
  instr_gtn(&gtn_ret_t47, x_v12054, y_v12055);
  return gtn_ret_t47;
}

tll_ptr lam_fun_t49(tll_ptr y_v12058, tll_env env) {
  tll_ptr call_ret_t48;
  call_ret_t48 = gtn_i8(env[0], y_v12058);
  return call_ret_t48;
}

tll_ptr lam_fun_t51(tll_ptr x_v12056, tll_env env) {
  tll_ptr lam_clo_t50;
  instr_clo(&lam_clo_t50, &lam_fun_t49, 1, x_v12056);
  return lam_clo_t50;
}

tll_ptr eqn_i9(tll_ptr x_v12059, tll_ptr y_v12060) {
  tll_ptr eqn_ret_t53;
  instr_eqn(&eqn_ret_t53, x_v12059, y_v12060);
  return eqn_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v12063, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = eqn_i9(env[0], y_v12063);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v12061, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v12061);
  return lam_clo_t56;
}

tll_ptr comparen_i10(tll_ptr n1_v12064, tll_ptr n2_v12065) {
  tll_ptr EQ_t65; tll_ptr GT_t62; tll_ptr LT_t64; tll_ptr add_ret_t60;
  tll_ptr add_ret_t61; tll_ptr call_ret_t59; tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t66; tll_ptr ifte_ret_t67;
  if (n1_v12064) {
    if (n2_v12065) {
      add_ret_t60 = n1_v12064 - 1;
      add_ret_t61 = n2_v12065 - 1;
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
    if (n2_v12065) {
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

tll_ptr lam_fun_t69(tll_ptr n2_v12068, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = comparen_i10(env[0], n2_v12068);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr n1_v12066, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, n1_v12066);
  return lam_clo_t70;
}

tll_ptr pred_i11(tll_ptr x_v12069) {
  tll_ptr add_ret_t73; tll_ptr ifte_ret_t74;
  if (x_v12069) {
    add_ret_t73 = x_v12069 - 1;
    ifte_ret_t74 = add_ret_t73;
  }
  else {
    ifte_ret_t74 = (tll_ptr)0;
  }
  return ifte_ret_t74;
}

tll_ptr lam_fun_t76(tll_ptr x_v12070, tll_env env) {
  tll_ptr call_ret_t75;
  call_ret_t75 = pred_i11(x_v12070);
  return call_ret_t75;
}

tll_ptr addn_i12(tll_ptr x_v12071, tll_ptr y_v12072) {
  tll_ptr addn_ret_t78;
  instr_addn(&addn_ret_t78, x_v12071, y_v12072);
  return addn_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v12075, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i12(env[0], y_v12075);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v12073, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v12073);
  return lam_clo_t81;
}

tll_ptr subn_i13(tll_ptr x_v12076, tll_ptr y_v12077) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v12077) {
    call_ret_t85 = pred_i11(x_v12076);
    add_ret_t86 = y_v12077 - 1;
    call_ret_t84 = subn_i13(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v12076;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v12080, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i13(env[0], y_v12080);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v12078, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v12078);
  return lam_clo_t90;
}

tll_ptr muln_i14(tll_ptr x_v12081, tll_ptr y_v12082) {
  tll_ptr muln_ret_t93;
  instr_muln(&muln_ret_t93, x_v12081, y_v12082);
  return muln_ret_t93;
}

tll_ptr lam_fun_t95(tll_ptr y_v12085, tll_env env) {
  tll_ptr call_ret_t94;
  call_ret_t94 = muln_i14(env[0], y_v12085);
  return call_ret_t94;
}

tll_ptr lam_fun_t97(tll_ptr x_v12083, tll_env env) {
  tll_ptr lam_clo_t96;
  instr_clo(&lam_clo_t96, &lam_fun_t95, 1, x_v12083);
  return lam_clo_t96;
}

tll_ptr divn_i15(tll_ptr x_v12086, tll_ptr y_v12087) {
  tll_ptr divn_ret_t99;
  instr_divn(&divn_ret_t99, x_v12086, y_v12087);
  return divn_ret_t99;
}

tll_ptr lam_fun_t101(tll_ptr y_v12090, tll_env env) {
  tll_ptr call_ret_t100;
  call_ret_t100 = divn_i15(env[0], y_v12090);
  return call_ret_t100;
}

tll_ptr lam_fun_t103(tll_ptr x_v12088, tll_env env) {
  tll_ptr lam_clo_t102;
  instr_clo(&lam_clo_t102, &lam_fun_t101, 1, x_v12088);
  return lam_clo_t102;
}

tll_ptr modn_i16(tll_ptr x_v12091, tll_ptr y_v12092) {
  tll_ptr modn_ret_t105;
  instr_modn(&modn_ret_t105, x_v12091, y_v12092);
  return modn_ret_t105;
}

tll_ptr lam_fun_t107(tll_ptr y_v12095, tll_env env) {
  tll_ptr call_ret_t106;
  call_ret_t106 = modn_i16(env[0], y_v12095);
  return call_ret_t106;
}

tll_ptr lam_fun_t109(tll_ptr x_v12093, tll_env env) {
  tll_ptr lam_clo_t108;
  instr_clo(&lam_clo_t108, &lam_fun_t107, 1, x_v12093);
  return lam_clo_t108;
}

tll_ptr eqc_i17(tll_ptr c1_v12096, tll_ptr c2_v12097) {
  tll_ptr call_ret_t113; tll_ptr n1_v12098; tll_ptr n2_v12099;
  tll_ptr switch_ret_t111; tll_ptr switch_ret_t112;
  switch(((tll_node)c1_v12096)->tag) {
    case 5:
      n1_v12098 = ((tll_node)c1_v12096)->data[0];
      switch(((tll_node)c2_v12097)->tag) {
        case 5:
          n2_v12099 = ((tll_node)c2_v12097)->data[0];
          call_ret_t113 = eqn_i9(n1_v12098, n2_v12099);
          switch_ret_t112 = call_ret_t113;
          break;
      }
      switch_ret_t111 = switch_ret_t112;
      break;
  }
  return switch_ret_t111;
}

tll_ptr lam_fun_t115(tll_ptr c2_v12102, tll_env env) {
  tll_ptr call_ret_t114;
  call_ret_t114 = eqc_i17(env[0], c2_v12102);
  return call_ret_t114;
}

tll_ptr lam_fun_t117(tll_ptr c1_v12100, tll_env env) {
  tll_ptr lam_clo_t116;
  instr_clo(&lam_clo_t116, &lam_fun_t115, 1, c1_v12100);
  return lam_clo_t116;
}

tll_ptr comparec_i18(tll_ptr c1_v12103, tll_ptr c2_v12104) {
  tll_ptr call_ret_t121; tll_ptr n1_v12105; tll_ptr n2_v12106;
  tll_ptr switch_ret_t119; tll_ptr switch_ret_t120;
  switch(((tll_node)c1_v12103)->tag) {
    case 5:
      n1_v12105 = ((tll_node)c1_v12103)->data[0];
      switch(((tll_node)c2_v12104)->tag) {
        case 5:
          n2_v12106 = ((tll_node)c2_v12104)->data[0];
          call_ret_t121 = comparen_i10(n1_v12105, n2_v12106);
          switch_ret_t120 = call_ret_t121;
          break;
      }
      switch_ret_t119 = switch_ret_t120;
      break;
  }
  return switch_ret_t119;
}

tll_ptr lam_fun_t123(tll_ptr c2_v12109, tll_env env) {
  tll_ptr call_ret_t122;
  call_ret_t122 = comparec_i18(env[0], c2_v12109);
  return call_ret_t122;
}

tll_ptr lam_fun_t125(tll_ptr c1_v12107, tll_env env) {
  tll_ptr lam_clo_t124;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 1, c1_v12107);
  return lam_clo_t124;
}

tll_ptr cats_i19(tll_ptr s1_v12110, tll_ptr s2_v12111) {
  tll_ptr String_t129; tll_ptr c_v12112; tll_ptr call_ret_t128;
  tll_ptr s1_v12113; tll_ptr switch_ret_t127;
  switch(((tll_node)s1_v12110)->tag) {
    case 6:
      switch_ret_t127 = s2_v12111;
      break;
    case 7:
      c_v12112 = ((tll_node)s1_v12110)->data[0];
      s1_v12113 = ((tll_node)s1_v12110)->data[1];
      call_ret_t128 = cats_i19(s1_v12113, s2_v12111);
      instr_struct(&String_t129, 7, 2, c_v12112, call_ret_t128);
      switch_ret_t127 = String_t129;
      break;
  }
  return switch_ret_t127;
}

tll_ptr lam_fun_t131(tll_ptr s2_v12116, tll_env env) {
  tll_ptr call_ret_t130;
  call_ret_t130 = cats_i19(env[0], s2_v12116);
  return call_ret_t130;
}

tll_ptr lam_fun_t133(tll_ptr s1_v12114, tll_env env) {
  tll_ptr lam_clo_t132;
  instr_clo(&lam_clo_t132, &lam_fun_t131, 1, s1_v12114);
  return lam_clo_t132;
}

tll_ptr strlen_i20(tll_ptr s_v12117) {
  tll_ptr __v12118; tll_ptr add_ret_t137; tll_ptr call_ret_t136;
  tll_ptr s_v12119; tll_ptr switch_ret_t135;
  switch(((tll_node)s_v12117)->tag) {
    case 6:
      switch_ret_t135 = (tll_ptr)0;
      break;
    case 7:
      __v12118 = ((tll_node)s_v12117)->data[0];
      s_v12119 = ((tll_node)s_v12117)->data[1];
      call_ret_t136 = strlen_i20(s_v12119);
      add_ret_t137 = call_ret_t136 + 1;
      switch_ret_t135 = add_ret_t137;
      break;
  }
  return switch_ret_t135;
}

tll_ptr lam_fun_t139(tll_ptr s_v12120, tll_env env) {
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i20(s_v12120);
  return call_ret_t138;
}

tll_ptr eqs_i21(tll_ptr s1_v12121, tll_ptr s2_v12122) {
  tll_ptr __v12123; tll_ptr __v12124; tll_ptr c1_v12125; tll_ptr c2_v12127;
  tll_ptr call_ret_t144; tll_ptr call_ret_t145; tll_ptr call_ret_t146;
  tll_ptr s1_v12126; tll_ptr s2_v12128; tll_ptr switch_ret_t141;
  tll_ptr switch_ret_t142; tll_ptr switch_ret_t143;
  switch(((tll_node)s1_v12121)->tag) {
    case 6:
      switch(((tll_node)s2_v12122)->tag) {
        case 6:
          switch_ret_t142 = (tll_ptr)1;
          break;
        case 7:
          __v12123 = ((tll_node)s2_v12122)->data[0];
          __v12124 = ((tll_node)s2_v12122)->data[1];
          switch_ret_t142 = (tll_ptr)0;
          break;
      }
      switch_ret_t141 = switch_ret_t142;
      break;
    case 7:
      c1_v12125 = ((tll_node)s1_v12121)->data[0];
      s1_v12126 = ((tll_node)s1_v12121)->data[1];
      switch(((tll_node)s2_v12122)->tag) {
        case 6:
          switch_ret_t143 = (tll_ptr)0;
          break;
        case 7:
          c2_v12127 = ((tll_node)s2_v12122)->data[0];
          s2_v12128 = ((tll_node)s2_v12122)->data[1];
          call_ret_t145 = eqc_i17(c1_v12125, c2_v12127);
          call_ret_t146 = eqs_i21(s1_v12126, s2_v12128);
          call_ret_t144 = andb_i1(call_ret_t145, call_ret_t146);
          switch_ret_t143 = call_ret_t144;
          break;
      }
      switch_ret_t141 = switch_ret_t143;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t148(tll_ptr s2_v12131, tll_env env) {
  tll_ptr call_ret_t147;
  call_ret_t147 = eqs_i21(env[0], s2_v12131);
  return call_ret_t147;
}

tll_ptr lam_fun_t150(tll_ptr s1_v12129, tll_env env) {
  tll_ptr lam_clo_t149;
  instr_clo(&lam_clo_t149, &lam_fun_t148, 1, s1_v12129);
  return lam_clo_t149;
}

tll_ptr compares_i22(tll_ptr s1_v12132, tll_ptr s2_v12133) {
  tll_ptr EQ_t154; tll_ptr GT_t157; tll_ptr GT_t162; tll_ptr LT_t155;
  tll_ptr LT_t161; tll_ptr __v12134; tll_ptr __v12135; tll_ptr c1_v12136;
  tll_ptr c2_v12138; tll_ptr call_ret_t158; tll_ptr call_ret_t160;
  tll_ptr s1_v12137; tll_ptr s2_v12139; tll_ptr switch_ret_t152;
  tll_ptr switch_ret_t153; tll_ptr switch_ret_t156; tll_ptr switch_ret_t159;
  switch(((tll_node)s1_v12132)->tag) {
    case 6:
      switch(((tll_node)s2_v12133)->tag) {
        case 6:
          instr_struct(&EQ_t154, 3, 0);
          switch_ret_t153 = EQ_t154;
          break;
        case 7:
          __v12134 = ((tll_node)s2_v12133)->data[0];
          __v12135 = ((tll_node)s2_v12133)->data[1];
          instr_struct(&LT_t155, 1, 0);
          switch_ret_t153 = LT_t155;
          break;
      }
      switch_ret_t152 = switch_ret_t153;
      break;
    case 7:
      c1_v12136 = ((tll_node)s1_v12132)->data[0];
      s1_v12137 = ((tll_node)s1_v12132)->data[1];
      switch(((tll_node)s2_v12133)->tag) {
        case 6:
          instr_struct(&GT_t157, 2, 0);
          switch_ret_t156 = GT_t157;
          break;
        case 7:
          c2_v12138 = ((tll_node)s2_v12133)->data[0];
          s2_v12139 = ((tll_node)s2_v12133)->data[1];
          call_ret_t158 = comparec_i18(c1_v12136, c2_v12138);
          switch(((tll_node)call_ret_t158)->tag) {
            case 3:
              call_ret_t160 = compares_i22(s1_v12137, s2_v12139);
              switch_ret_t159 = call_ret_t160;
              break;
            case 1:
              instr_struct(&LT_t161, 1, 0);
              switch_ret_t159 = LT_t161;
              break;
            case 2:
              instr_struct(&GT_t162, 2, 0);
              switch_ret_t159 = GT_t162;
              break;
          }
          switch_ret_t156 = switch_ret_t159;
          break;
      }
      switch_ret_t152 = switch_ret_t156;
      break;
  }
  return switch_ret_t152;
}

tll_ptr lam_fun_t164(tll_ptr s2_v12142, tll_env env) {
  tll_ptr call_ret_t163;
  call_ret_t163 = compares_i22(env[0], s2_v12142);
  return call_ret_t163;
}

tll_ptr lam_fun_t166(tll_ptr s1_v12140, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, s1_v12140);
  return lam_clo_t165;
}

tll_ptr and_thenUUU_i52(tll_ptr A_v12143, tll_ptr B_v12144, tll_ptr opt_v12145, tll_ptr f_v12146) {
  tll_ptr NoneUU_t169; tll_ptr app_ret_t170; tll_ptr switch_ret_t168;
  tll_ptr x_v12147;
  switch(((tll_node)opt_v12145)->tag) {
    case 19:
      instr_struct(&NoneUU_t169, 19, 0);
      switch_ret_t168 = NoneUU_t169;
      break;
    case 20:
      x_v12147 = ((tll_node)opt_v12145)->data[0];
      instr_app(&app_ret_t170, f_v12146, x_v12147);
      switch_ret_t168 = app_ret_t170;
      break;
  }
  return switch_ret_t168;
}

tll_ptr lam_fun_t172(tll_ptr f_v12157, tll_env env) {
  tll_ptr call_ret_t171;
  call_ret_t171 = and_thenUUU_i52(env[2], env[1], env[0], f_v12157);
  return call_ret_t171;
}

tll_ptr lam_fun_t174(tll_ptr opt_v12155, tll_env env) {
  tll_ptr lam_clo_t173;
  instr_clo(&lam_clo_t173, &lam_fun_t172, 3, opt_v12155, env[0], env[1]);
  return lam_clo_t173;
}

tll_ptr lam_fun_t176(tll_ptr B_v12152, tll_env env) {
  tll_ptr lam_clo_t175;
  instr_clo(&lam_clo_t175, &lam_fun_t174, 2, B_v12152, env[0]);
  return lam_clo_t175;
}

tll_ptr lam_fun_t178(tll_ptr A_v12148, tll_env env) {
  tll_ptr lam_clo_t177;
  instr_clo(&lam_clo_t177, &lam_fun_t176, 1, A_v12148);
  return lam_clo_t177;
}

tll_ptr and_thenUUL_i51(tll_ptr A_v12158, tll_ptr B_v12159, tll_ptr opt_v12160, tll_ptr f_v12161) {
  tll_ptr NoneUL_t181; tll_ptr app_ret_t182; tll_ptr switch_ret_t180;
  tll_ptr x_v12162;
  switch(((tll_node)opt_v12160)->tag) {
    case 17:
      instr_free_struct(opt_v12160);
      instr_struct(&NoneUL_t181, 17, 0);
      switch_ret_t180 = NoneUL_t181;
      break;
    case 18:
      x_v12162 = ((tll_node)opt_v12160)->data[0];
      instr_free_struct(opt_v12160);
      instr_app(&app_ret_t182, f_v12161, x_v12162);
      switch_ret_t180 = app_ret_t182;
      break;
  }
  return switch_ret_t180;
}

tll_ptr lam_fun_t184(tll_ptr f_v12172, tll_env env) {
  tll_ptr call_ret_t183;
  call_ret_t183 = and_thenUUL_i51(env[2], env[1], env[0], f_v12172);
  return call_ret_t183;
}

tll_ptr lam_fun_t186(tll_ptr opt_v12170, tll_env env) {
  tll_ptr lam_clo_t185;
  instr_clo(&lam_clo_t185, &lam_fun_t184, 3, opt_v12170, env[0], env[1]);
  return lam_clo_t185;
}

tll_ptr lam_fun_t188(tll_ptr B_v12167, tll_env env) {
  tll_ptr lam_clo_t187;
  instr_clo(&lam_clo_t187, &lam_fun_t186, 2, B_v12167, env[0]);
  return lam_clo_t187;
}

tll_ptr lam_fun_t190(tll_ptr A_v12163, tll_env env) {
  tll_ptr lam_clo_t189;
  instr_clo(&lam_clo_t189, &lam_fun_t188, 1, A_v12163);
  return lam_clo_t189;
}

tll_ptr and_thenULU_i50(tll_ptr A_v12173, tll_ptr B_v12174, tll_ptr opt_v12175, tll_ptr f_v12176) {
  tll_ptr NoneLU_t193; tll_ptr app_ret_t194; tll_ptr switch_ret_t192;
  tll_ptr x_v12177;
  switch(((tll_node)opt_v12175)->tag) {
    case 19:
      instr_struct(&NoneLU_t193, 15, 0);
      switch_ret_t192 = NoneLU_t193;
      break;
    case 20:
      x_v12177 = ((tll_node)opt_v12175)->data[0];
      instr_app(&app_ret_t194, f_v12176, x_v12177);
      switch_ret_t192 = app_ret_t194;
      break;
  }
  return switch_ret_t192;
}

tll_ptr lam_fun_t196(tll_ptr f_v12187, tll_env env) {
  tll_ptr call_ret_t195;
  call_ret_t195 = and_thenULU_i50(env[2], env[1], env[0], f_v12187);
  return call_ret_t195;
}

tll_ptr lam_fun_t198(tll_ptr opt_v12185, tll_env env) {
  tll_ptr lam_clo_t197;
  instr_clo(&lam_clo_t197, &lam_fun_t196, 3, opt_v12185, env[0], env[1]);
  return lam_clo_t197;
}

tll_ptr lam_fun_t200(tll_ptr B_v12182, tll_env env) {
  tll_ptr lam_clo_t199;
  instr_clo(&lam_clo_t199, &lam_fun_t198, 2, B_v12182, env[0]);
  return lam_clo_t199;
}

tll_ptr lam_fun_t202(tll_ptr A_v12178, tll_env env) {
  tll_ptr lam_clo_t201;
  instr_clo(&lam_clo_t201, &lam_fun_t200, 1, A_v12178);
  return lam_clo_t201;
}

tll_ptr and_thenULL_i49(tll_ptr A_v12188, tll_ptr B_v12189, tll_ptr opt_v12190, tll_ptr f_v12191) {
  tll_ptr NoneLL_t205; tll_ptr app_ret_t206; tll_ptr switch_ret_t204;
  tll_ptr x_v12192;
  switch(((tll_node)opt_v12190)->tag) {
    case 17:
      instr_free_struct(opt_v12190);
      instr_struct(&NoneLL_t205, 13, 0);
      switch_ret_t204 = NoneLL_t205;
      break;
    case 18:
      x_v12192 = ((tll_node)opt_v12190)->data[0];
      instr_free_struct(opt_v12190);
      instr_app(&app_ret_t206, f_v12191, x_v12192);
      switch_ret_t204 = app_ret_t206;
      break;
  }
  return switch_ret_t204;
}

tll_ptr lam_fun_t208(tll_ptr f_v12202, tll_env env) {
  tll_ptr call_ret_t207;
  call_ret_t207 = and_thenULL_i49(env[2], env[1], env[0], f_v12202);
  return call_ret_t207;
}

tll_ptr lam_fun_t210(tll_ptr opt_v12200, tll_env env) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 3, opt_v12200, env[0], env[1]);
  return lam_clo_t209;
}

tll_ptr lam_fun_t212(tll_ptr B_v12197, tll_env env) {
  tll_ptr lam_clo_t211;
  instr_clo(&lam_clo_t211, &lam_fun_t210, 2, B_v12197, env[0]);
  return lam_clo_t211;
}

tll_ptr lam_fun_t214(tll_ptr A_v12193, tll_env env) {
  tll_ptr lam_clo_t213;
  instr_clo(&lam_clo_t213, &lam_fun_t212, 1, A_v12193);
  return lam_clo_t213;
}

tll_ptr and_thenLUL_i47(tll_ptr A_v12203, tll_ptr B_v12204, tll_ptr opt_v12205, tll_ptr f_v12206) {
  tll_ptr NoneUL_t217; tll_ptr app_ret_t218; tll_ptr switch_ret_t216;
  tll_ptr x_v12207;
  switch(((tll_node)opt_v12205)->tag) {
    case 13:
      instr_free_struct(opt_v12205);
      instr_struct(&NoneUL_t217, 17, 0);
      switch_ret_t216 = NoneUL_t217;
      break;
    case 14:
      x_v12207 = ((tll_node)opt_v12205)->data[0];
      instr_free_struct(opt_v12205);
      instr_app(&app_ret_t218, f_v12206, x_v12207);
      switch_ret_t216 = app_ret_t218;
      break;
  }
  return switch_ret_t216;
}

tll_ptr lam_fun_t220(tll_ptr f_v12217, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = and_thenLUL_i47(env[2], env[1], env[0], f_v12217);
  return call_ret_t219;
}

tll_ptr lam_fun_t222(tll_ptr opt_v12215, tll_env env) {
  tll_ptr lam_clo_t221;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 3, opt_v12215, env[0], env[1]);
  return lam_clo_t221;
}

tll_ptr lam_fun_t224(tll_ptr B_v12212, tll_env env) {
  tll_ptr lam_clo_t223;
  instr_clo(&lam_clo_t223, &lam_fun_t222, 2, B_v12212, env[0]);
  return lam_clo_t223;
}

tll_ptr lam_fun_t226(tll_ptr A_v12208, tll_env env) {
  tll_ptr lam_clo_t225;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 1, A_v12208);
  return lam_clo_t225;
}

tll_ptr and_thenLLL_i45(tll_ptr A_v12218, tll_ptr B_v12219, tll_ptr opt_v12220, tll_ptr f_v12221) {
  tll_ptr NoneLL_t229; tll_ptr app_ret_t230; tll_ptr switch_ret_t228;
  tll_ptr x_v12222;
  switch(((tll_node)opt_v12220)->tag) {
    case 13:
      instr_free_struct(opt_v12220);
      instr_struct(&NoneLL_t229, 13, 0);
      switch_ret_t228 = NoneLL_t229;
      break;
    case 14:
      x_v12222 = ((tll_node)opt_v12220)->data[0];
      instr_free_struct(opt_v12220);
      instr_app(&app_ret_t230, f_v12221, x_v12222);
      switch_ret_t228 = app_ret_t230;
      break;
  }
  return switch_ret_t228;
}

tll_ptr lam_fun_t232(tll_ptr f_v12232, tll_env env) {
  tll_ptr call_ret_t231;
  call_ret_t231 = and_thenLLL_i45(env[2], env[1], env[0], f_v12232);
  return call_ret_t231;
}

tll_ptr lam_fun_t234(tll_ptr opt_v12230, tll_env env) {
  tll_ptr lam_clo_t233;
  instr_clo(&lam_clo_t233, &lam_fun_t232, 3, opt_v12230, env[0], env[1]);
  return lam_clo_t233;
}

tll_ptr lam_fun_t236(tll_ptr B_v12227, tll_env env) {
  tll_ptr lam_clo_t235;
  instr_clo(&lam_clo_t235, &lam_fun_t234, 2, B_v12227, env[0]);
  return lam_clo_t235;
}

tll_ptr lam_fun_t238(tll_ptr A_v12223, tll_env env) {
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, A_v12223);
  return lam_clo_t237;
}

tll_ptr lenUU_i60(tll_ptr A_v12233, tll_ptr xs_v12234) {
  tll_ptr add_ret_t245; tll_ptr call_ret_t243; tll_ptr consUU_t246;
  tll_ptr n_v12237; tll_ptr nilUU_t241; tll_ptr pair_struct_t242;
  tll_ptr pair_struct_t247; tll_ptr switch_ret_t240; tll_ptr switch_ret_t244;
  tll_ptr x_v12235; tll_ptr xs_v12236; tll_ptr xs_v12238;
  switch(((tll_node)xs_v12234)->tag) {
    case 27:
      instr_struct(&nilUU_t241, 27, 0);
      instr_struct(&pair_struct_t242, 0, 2, (tll_ptr)0, nilUU_t241);
      switch_ret_t240 = pair_struct_t242;
      break;
    case 28:
      x_v12235 = ((tll_node)xs_v12234)->data[0];
      xs_v12236 = ((tll_node)xs_v12234)->data[1];
      call_ret_t243 = lenUU_i60(0, xs_v12236);
      switch(((tll_node)call_ret_t243)->tag) {
        case 0:
          n_v12237 = ((tll_node)call_ret_t243)->data[0];
          xs_v12238 = ((tll_node)call_ret_t243)->data[1];
          instr_free_struct(call_ret_t243);
          add_ret_t245 = n_v12237 + 1;
          instr_struct(&consUU_t246, 28, 2, x_v12235, xs_v12238);
          instr_struct(&pair_struct_t247, 0, 2, add_ret_t245, consUU_t246);
          switch_ret_t244 = pair_struct_t247;
          break;
      }
      switch_ret_t240 = switch_ret_t244;
      break;
  }
  return switch_ret_t240;
}

tll_ptr lam_fun_t249(tll_ptr xs_v12241, tll_env env) {
  tll_ptr call_ret_t248;
  call_ret_t248 = lenUU_i60(env[0], xs_v12241);
  return call_ret_t248;
}

tll_ptr lam_fun_t251(tll_ptr A_v12239, tll_env env) {
  tll_ptr lam_clo_t250;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 1, A_v12239);
  return lam_clo_t250;
}

tll_ptr lenUL_i59(tll_ptr A_v12242, tll_ptr xs_v12243) {
  tll_ptr add_ret_t258; tll_ptr call_ret_t256; tll_ptr consUL_t259;
  tll_ptr n_v12246; tll_ptr nilUL_t254; tll_ptr pair_struct_t255;
  tll_ptr pair_struct_t260; tll_ptr switch_ret_t253; tll_ptr switch_ret_t257;
  tll_ptr x_v12244; tll_ptr xs_v12245; tll_ptr xs_v12247;
  switch(((tll_node)xs_v12243)->tag) {
    case 25:
      instr_free_struct(xs_v12243);
      instr_struct(&nilUL_t254, 25, 0);
      instr_struct(&pair_struct_t255, 0, 2, (tll_ptr)0, nilUL_t254);
      switch_ret_t253 = pair_struct_t255;
      break;
    case 26:
      x_v12244 = ((tll_node)xs_v12243)->data[0];
      xs_v12245 = ((tll_node)xs_v12243)->data[1];
      instr_free_struct(xs_v12243);
      call_ret_t256 = lenUL_i59(0, xs_v12245);
      switch(((tll_node)call_ret_t256)->tag) {
        case 0:
          n_v12246 = ((tll_node)call_ret_t256)->data[0];
          xs_v12247 = ((tll_node)call_ret_t256)->data[1];
          instr_free_struct(call_ret_t256);
          add_ret_t258 = n_v12246 + 1;
          instr_struct(&consUL_t259, 26, 2, x_v12244, xs_v12247);
          instr_struct(&pair_struct_t260, 0, 2, add_ret_t258, consUL_t259);
          switch_ret_t257 = pair_struct_t260;
          break;
      }
      switch_ret_t253 = switch_ret_t257;
      break;
  }
  return switch_ret_t253;
}

tll_ptr lam_fun_t262(tll_ptr xs_v12250, tll_env env) {
  tll_ptr call_ret_t261;
  call_ret_t261 = lenUL_i59(env[0], xs_v12250);
  return call_ret_t261;
}

tll_ptr lam_fun_t264(tll_ptr A_v12248, tll_env env) {
  tll_ptr lam_clo_t263;
  instr_clo(&lam_clo_t263, &lam_fun_t262, 1, A_v12248);
  return lam_clo_t263;
}

tll_ptr lenLL_i57(tll_ptr A_v12251, tll_ptr xs_v12252) {
  tll_ptr add_ret_t271; tll_ptr call_ret_t269; tll_ptr consLL_t272;
  tll_ptr n_v12255; tll_ptr nilLL_t267; tll_ptr pair_struct_t268;
  tll_ptr pair_struct_t273; tll_ptr switch_ret_t266; tll_ptr switch_ret_t270;
  tll_ptr x_v12253; tll_ptr xs_v12254; tll_ptr xs_v12256;
  switch(((tll_node)xs_v12252)->tag) {
    case 21:
      instr_free_struct(xs_v12252);
      instr_struct(&nilLL_t267, 21, 0);
      instr_struct(&pair_struct_t268, 0, 2, (tll_ptr)0, nilLL_t267);
      switch_ret_t266 = pair_struct_t268;
      break;
    case 22:
      x_v12253 = ((tll_node)xs_v12252)->data[0];
      xs_v12254 = ((tll_node)xs_v12252)->data[1];
      instr_free_struct(xs_v12252);
      call_ret_t269 = lenLL_i57(0, xs_v12254);
      switch(((tll_node)call_ret_t269)->tag) {
        case 0:
          n_v12255 = ((tll_node)call_ret_t269)->data[0];
          xs_v12256 = ((tll_node)call_ret_t269)->data[1];
          instr_free_struct(call_ret_t269);
          add_ret_t271 = n_v12255 + 1;
          instr_struct(&consLL_t272, 22, 2, x_v12253, xs_v12256);
          instr_struct(&pair_struct_t273, 0, 2, add_ret_t271, consLL_t272);
          switch_ret_t270 = pair_struct_t273;
          break;
      }
      switch_ret_t266 = switch_ret_t270;
      break;
  }
  return switch_ret_t266;
}

tll_ptr lam_fun_t275(tll_ptr xs_v12259, tll_env env) {
  tll_ptr call_ret_t274;
  call_ret_t274 = lenLL_i57(env[0], xs_v12259);
  return call_ret_t274;
}

tll_ptr lam_fun_t277(tll_ptr A_v12257, tll_env env) {
  tll_ptr lam_clo_t276;
  instr_clo(&lam_clo_t276, &lam_fun_t275, 1, A_v12257);
  return lam_clo_t276;
}

tll_ptr appendUU_i64(tll_ptr A_v12260, tll_ptr xs_v12261, tll_ptr ys_v12262) {
  tll_ptr call_ret_t280; tll_ptr consUU_t281; tll_ptr switch_ret_t279;
  tll_ptr x_v12263; tll_ptr xs_v12264;
  switch(((tll_node)xs_v12261)->tag) {
    case 27:
      switch_ret_t279 = ys_v12262;
      break;
    case 28:
      x_v12263 = ((tll_node)xs_v12261)->data[0];
      xs_v12264 = ((tll_node)xs_v12261)->data[1];
      call_ret_t280 = appendUU_i64(0, xs_v12264, ys_v12262);
      instr_struct(&consUU_t281, 28, 2, x_v12263, call_ret_t280);
      switch_ret_t279 = consUU_t281;
      break;
  }
  return switch_ret_t279;
}

tll_ptr lam_fun_t283(tll_ptr ys_v12270, tll_env env) {
  tll_ptr call_ret_t282;
  call_ret_t282 = appendUU_i64(env[1], env[0], ys_v12270);
  return call_ret_t282;
}

tll_ptr lam_fun_t285(tll_ptr xs_v12268, tll_env env) {
  tll_ptr lam_clo_t284;
  instr_clo(&lam_clo_t284, &lam_fun_t283, 2, xs_v12268, env[0]);
  return lam_clo_t284;
}

tll_ptr lam_fun_t287(tll_ptr A_v12265, tll_env env) {
  tll_ptr lam_clo_t286;
  instr_clo(&lam_clo_t286, &lam_fun_t285, 1, A_v12265);
  return lam_clo_t286;
}

tll_ptr appendUL_i63(tll_ptr A_v12271, tll_ptr xs_v12272, tll_ptr ys_v12273) {
  tll_ptr call_ret_t290; tll_ptr consUL_t291; tll_ptr switch_ret_t289;
  tll_ptr x_v12274; tll_ptr xs_v12275;
  switch(((tll_node)xs_v12272)->tag) {
    case 25:
      instr_free_struct(xs_v12272);
      switch_ret_t289 = ys_v12273;
      break;
    case 26:
      x_v12274 = ((tll_node)xs_v12272)->data[0];
      xs_v12275 = ((tll_node)xs_v12272)->data[1];
      instr_free_struct(xs_v12272);
      call_ret_t290 = appendUL_i63(0, xs_v12275, ys_v12273);
      instr_struct(&consUL_t291, 26, 2, x_v12274, call_ret_t290);
      switch_ret_t289 = consUL_t291;
      break;
  }
  return switch_ret_t289;
}

tll_ptr lam_fun_t293(tll_ptr ys_v12281, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = appendUL_i63(env[1], env[0], ys_v12281);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v12279, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 2, xs_v12279, env[0]);
  return lam_clo_t294;
}

tll_ptr lam_fun_t297(tll_ptr A_v12276, tll_env env) {
  tll_ptr lam_clo_t296;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 1, A_v12276);
  return lam_clo_t296;
}

tll_ptr appendLL_i61(tll_ptr A_v12282, tll_ptr xs_v12283, tll_ptr ys_v12284) {
  tll_ptr call_ret_t300; tll_ptr consLL_t301; tll_ptr switch_ret_t299;
  tll_ptr x_v12285; tll_ptr xs_v12286;
  switch(((tll_node)xs_v12283)->tag) {
    case 21:
      instr_free_struct(xs_v12283);
      switch_ret_t299 = ys_v12284;
      break;
    case 22:
      x_v12285 = ((tll_node)xs_v12283)->data[0];
      xs_v12286 = ((tll_node)xs_v12283)->data[1];
      instr_free_struct(xs_v12283);
      call_ret_t300 = appendLL_i61(0, xs_v12286, ys_v12284);
      instr_struct(&consLL_t301, 22, 2, x_v12285, call_ret_t300);
      switch_ret_t299 = consLL_t301;
      break;
  }
  return switch_ret_t299;
}

tll_ptr lam_fun_t303(tll_ptr ys_v12292, tll_env env) {
  tll_ptr call_ret_t302;
  call_ret_t302 = appendLL_i61(env[1], env[0], ys_v12292);
  return call_ret_t302;
}

tll_ptr lam_fun_t305(tll_ptr xs_v12290, tll_env env) {
  tll_ptr lam_clo_t304;
  instr_clo(&lam_clo_t304, &lam_fun_t303, 2, xs_v12290, env[0]);
  return lam_clo_t304;
}

tll_ptr lam_fun_t307(tll_ptr A_v12287, tll_env env) {
  tll_ptr lam_clo_t306;
  instr_clo(&lam_clo_t306, &lam_fun_t305, 1, A_v12287);
  return lam_clo_t306;
}

tll_ptr lam_fun_t314(tll_ptr __v12294, tll_env env) {
  tll_ptr __v12303; tll_ptr ch_v12301; tll_ptr ch_v12302; tll_ptr ch_v12305;
  tll_ptr ch_v12306; tll_ptr prim_ch_t309; tll_ptr recv_msg_t311;
  tll_ptr s_v12304; tll_ptr send_ch_t310; tll_ptr send_ch_t313;
  tll_ptr switch_ret_t312;
  instr_open(&prim_ch_t309, &proc_stdin);
  ch_v12301 = prim_ch_t309;
  instr_send(&send_ch_t310, ch_v12301, (tll_ptr)1);
  ch_v12302 = send_ch_t310;
  instr_recv(&recv_msg_t311, ch_v12302);
  __v12303 = recv_msg_t311;
  switch(((tll_node)__v12303)->tag) {
    case 0:
      s_v12304 = ((tll_node)__v12303)->data[0];
      ch_v12305 = ((tll_node)__v12303)->data[1];
      instr_free_struct(__v12303);
      instr_send(&send_ch_t313, ch_v12305, (tll_ptr)0);
      ch_v12306 = send_ch_t313;
      switch_ret_t312 = s_v12304;
      break;
  }
  return switch_ret_t312;
}

tll_ptr readline_i33(tll_ptr __v12293) {
  tll_ptr lam_clo_t315;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 0);
  return lam_clo_t315;
}

tll_ptr lam_fun_t317(tll_ptr __v12307, tll_env env) {
  tll_ptr call_ret_t316;
  call_ret_t316 = readline_i33(__v12307);
  return call_ret_t316;
}

tll_ptr lam_fun_t323(tll_ptr __v12309, tll_env env) {
  tll_ptr ch_v12314; tll_ptr ch_v12315; tll_ptr ch_v12316; tll_ptr ch_v12317;
  tll_ptr prim_ch_t319; tll_ptr send_ch_t320; tll_ptr send_ch_t321;
  tll_ptr send_ch_t322;
  instr_open(&prim_ch_t319, &proc_stdout);
  ch_v12314 = prim_ch_t319;
  instr_send(&send_ch_t320, ch_v12314, (tll_ptr)1);
  ch_v12315 = send_ch_t320;
  instr_send(&send_ch_t321, ch_v12315, env[0]);
  ch_v12316 = send_ch_t321;
  instr_send(&send_ch_t322, ch_v12316, (tll_ptr)0);
  ch_v12317 = send_ch_t322;
  return 0;
}

tll_ptr print_i34(tll_ptr s_v12308) {
  tll_ptr lam_clo_t324;
  instr_clo(&lam_clo_t324, &lam_fun_t323, 1, s_v12308);
  return lam_clo_t324;
}

tll_ptr lam_fun_t326(tll_ptr s_v12318, tll_env env) {
  tll_ptr call_ret_t325;
  call_ret_t325 = print_i34(s_v12318);
  return call_ret_t325;
}

tll_ptr lam_fun_t332(tll_ptr __v12320, tll_env env) {
  tll_ptr ch_v12325; tll_ptr ch_v12326; tll_ptr ch_v12327; tll_ptr ch_v12328;
  tll_ptr prim_ch_t328; tll_ptr send_ch_t329; tll_ptr send_ch_t330;
  tll_ptr send_ch_t331;
  instr_open(&prim_ch_t328, &proc_stderr);
  ch_v12325 = prim_ch_t328;
  instr_send(&send_ch_t329, ch_v12325, (tll_ptr)1);
  ch_v12326 = send_ch_t329;
  instr_send(&send_ch_t330, ch_v12326, env[0]);
  ch_v12327 = send_ch_t330;
  instr_send(&send_ch_t331, ch_v12327, (tll_ptr)0);
  ch_v12328 = send_ch_t331;
  return 0;
}

tll_ptr prerr_i35(tll_ptr s_v12319) {
  tll_ptr lam_clo_t333;
  instr_clo(&lam_clo_t333, &lam_fun_t332, 1, s_v12319);
  return lam_clo_t333;
}

tll_ptr lam_fun_t335(tll_ptr s_v12329, tll_env env) {
  tll_ptr call_ret_t334;
  call_ret_t334 = prerr_i35(s_v12329);
  return call_ret_t334;
}

tll_ptr get_at_i37(tll_ptr A_v12330, tll_ptr n_v12331, tll_ptr xs_v12332, tll_ptr a_v12333) {
  tll_ptr __v12334; tll_ptr __v12337; tll_ptr add_ret_t380;
  tll_ptr call_ret_t379; tll_ptr ifte_ret_t382; tll_ptr switch_ret_t378;
  tll_ptr switch_ret_t381; tll_ptr x_v12336; tll_ptr xs_v12335;
  if (n_v12331) {
    switch(((tll_node)xs_v12332)->tag) {
      case 27:
        switch_ret_t378 = a_v12333;
        break;
      case 28:
        __v12334 = ((tll_node)xs_v12332)->data[0];
        xs_v12335 = ((tll_node)xs_v12332)->data[1];
        add_ret_t380 = n_v12331 - 1;
        call_ret_t379 = get_at_i37(0, add_ret_t380, xs_v12335, a_v12333);
        switch_ret_t378 = call_ret_t379;
        break;
    }
    ifte_ret_t382 = switch_ret_t378;
  }
  else {
    switch(((tll_node)xs_v12332)->tag) {
      case 27:
        switch_ret_t381 = a_v12333;
        break;
      case 28:
        x_v12336 = ((tll_node)xs_v12332)->data[0];
        __v12337 = ((tll_node)xs_v12332)->data[1];
        switch_ret_t381 = x_v12336;
        break;
    }
    ifte_ret_t382 = switch_ret_t381;
  }
  return ifte_ret_t382;
}

tll_ptr lam_fun_t384(tll_ptr a_v12347, tll_env env) {
  tll_ptr call_ret_t383;
  call_ret_t383 = get_at_i37(env[2], env[1], env[0], a_v12347);
  return call_ret_t383;
}

tll_ptr lam_fun_t386(tll_ptr xs_v12345, tll_env env) {
  tll_ptr lam_clo_t385;
  instr_clo(&lam_clo_t385, &lam_fun_t384, 3, xs_v12345, env[0], env[1]);
  return lam_clo_t385;
}

tll_ptr lam_fun_t388(tll_ptr n_v12342, tll_env env) {
  tll_ptr lam_clo_t387;
  instr_clo(&lam_clo_t387, &lam_fun_t386, 2, n_v12342, env[0]);
  return lam_clo_t387;
}

tll_ptr lam_fun_t390(tll_ptr A_v12338, tll_env env) {
  tll_ptr lam_clo_t389;
  instr_clo(&lam_clo_t389, &lam_fun_t388, 1, A_v12338);
  return lam_clo_t389;
}

tll_ptr string_of_digit_i38(tll_ptr n_v12348) {
  tll_ptr EmptyString_t393; tll_ptr call_ret_t392;
  instr_struct(&EmptyString_t393, 6, 0);
  call_ret_t392 = get_at_i37(0, n_v12348, digits_i36, EmptyString_t393);
  return call_ret_t392;
}

tll_ptr lam_fun_t395(tll_ptr n_v12349, tll_env env) {
  tll_ptr call_ret_t394;
  call_ret_t394 = string_of_digit_i38(n_v12349);
  return call_ret_t394;
}

tll_ptr string_of_nat_i39(tll_ptr n_v12350) {
  tll_ptr call_ret_t397; tll_ptr call_ret_t398; tll_ptr call_ret_t399;
  tll_ptr call_ret_t400; tll_ptr call_ret_t401; tll_ptr call_ret_t402;
  tll_ptr ifte_ret_t403; tll_ptr n_v12352; tll_ptr s_v12351;
  call_ret_t398 = modn_i16(n_v12350, (tll_ptr)10);
  call_ret_t397 = string_of_digit_i38(call_ret_t398);
  s_v12351 = call_ret_t397;
  call_ret_t399 = divn_i15(n_v12350, (tll_ptr)10);
  n_v12352 = call_ret_t399;
  call_ret_t400 = ltn_i6((tll_ptr)0, n_v12352);
  if (call_ret_t400) {
    call_ret_t402 = string_of_nat_i39(n_v12352);
    call_ret_t401 = cats_i19(call_ret_t402, s_v12351);
    ifte_ret_t403 = call_ret_t401;
  }
  else {
    ifte_ret_t403 = s_v12351;
  }
  return ifte_ret_t403;
}

tll_ptr lam_fun_t405(tll_ptr n_v12353, tll_env env) {
  tll_ptr call_ret_t404;
  call_ret_t404 = string_of_nat_i39(n_v12353);
  return call_ret_t404;
}

tll_ptr digit_of_char_i40(tll_ptr c_v12354) {
  tll_ptr Char_t408; tll_ptr Char_t411; tll_ptr Char_t414; tll_ptr Char_t417;
  tll_ptr Char_t420; tll_ptr Char_t423; tll_ptr Char_t426; tll_ptr Char_t429;
  tll_ptr Char_t432; tll_ptr Char_t435; tll_ptr NoneUL_t437;
  tll_ptr SomeUL_t409; tll_ptr SomeUL_t412; tll_ptr SomeUL_t415;
  tll_ptr SomeUL_t418; tll_ptr SomeUL_t421; tll_ptr SomeUL_t424;
  tll_ptr SomeUL_t427; tll_ptr SomeUL_t430; tll_ptr SomeUL_t433;
  tll_ptr SomeUL_t436; tll_ptr call_ret_t407; tll_ptr call_ret_t410;
  tll_ptr call_ret_t413; tll_ptr call_ret_t416; tll_ptr call_ret_t419;
  tll_ptr call_ret_t422; tll_ptr call_ret_t425; tll_ptr call_ret_t428;
  tll_ptr call_ret_t431; tll_ptr call_ret_t434; tll_ptr ifte_ret_t438;
  tll_ptr ifte_ret_t439; tll_ptr ifte_ret_t440; tll_ptr ifte_ret_t441;
  tll_ptr ifte_ret_t442; tll_ptr ifte_ret_t443; tll_ptr ifte_ret_t444;
  tll_ptr ifte_ret_t445; tll_ptr ifte_ret_t446; tll_ptr ifte_ret_t447;
  instr_struct(&Char_t408, 5, 1, (tll_ptr)48);
  call_ret_t407 = eqc_i17(c_v12354, Char_t408);
  if (call_ret_t407) {
    instr_struct(&SomeUL_t409, 18, 1, (tll_ptr)0);
    ifte_ret_t447 = SomeUL_t409;
  }
  else {
    instr_struct(&Char_t411, 5, 1, (tll_ptr)49);
    call_ret_t410 = eqc_i17(c_v12354, Char_t411);
    if (call_ret_t410) {
      instr_struct(&SomeUL_t412, 18, 1, (tll_ptr)1);
      ifte_ret_t446 = SomeUL_t412;
    }
    else {
      instr_struct(&Char_t414, 5, 1, (tll_ptr)50);
      call_ret_t413 = eqc_i17(c_v12354, Char_t414);
      if (call_ret_t413) {
        instr_struct(&SomeUL_t415, 18, 1, (tll_ptr)2);
        ifte_ret_t445 = SomeUL_t415;
      }
      else {
        instr_struct(&Char_t417, 5, 1, (tll_ptr)51);
        call_ret_t416 = eqc_i17(c_v12354, Char_t417);
        if (call_ret_t416) {
          instr_struct(&SomeUL_t418, 18, 1, (tll_ptr)3);
          ifte_ret_t444 = SomeUL_t418;
        }
        else {
          instr_struct(&Char_t420, 5, 1, (tll_ptr)52);
          call_ret_t419 = eqc_i17(c_v12354, Char_t420);
          if (call_ret_t419) {
            instr_struct(&SomeUL_t421, 18, 1, (tll_ptr)4);
            ifte_ret_t443 = SomeUL_t421;
          }
          else {
            instr_struct(&Char_t423, 5, 1, (tll_ptr)53);
            call_ret_t422 = eqc_i17(c_v12354, Char_t423);
            if (call_ret_t422) {
              instr_struct(&SomeUL_t424, 18, 1, (tll_ptr)5);
              ifte_ret_t442 = SomeUL_t424;
            }
            else {
              instr_struct(&Char_t426, 5, 1, (tll_ptr)54);
              call_ret_t425 = eqc_i17(c_v12354, Char_t426);
              if (call_ret_t425) {
                instr_struct(&SomeUL_t427, 18, 1, (tll_ptr)6);
                ifte_ret_t441 = SomeUL_t427;
              }
              else {
                instr_struct(&Char_t429, 5, 1, (tll_ptr)55);
                call_ret_t428 = eqc_i17(c_v12354, Char_t429);
                if (call_ret_t428) {
                  instr_struct(&SomeUL_t430, 18, 1, (tll_ptr)7);
                  ifte_ret_t440 = SomeUL_t430;
                }
                else {
                  instr_struct(&Char_t432, 5, 1, (tll_ptr)56);
                  call_ret_t431 = eqc_i17(c_v12354, Char_t432);
                  if (call_ret_t431) {
                    instr_struct(&SomeUL_t433, 18, 1, (tll_ptr)8);
                    ifte_ret_t439 = SomeUL_t433;
                  }
                  else {
                    instr_struct(&Char_t435, 5, 1, (tll_ptr)57);
                    call_ret_t434 = eqc_i17(c_v12354, Char_t435);
                    if (call_ret_t434) {
                      instr_struct(&SomeUL_t436, 18, 1, (tll_ptr)9);
                      ifte_ret_t438 = SomeUL_t436;
                    }
                    else {
                      instr_struct(&NoneUL_t437, 17, 0);
                      ifte_ret_t438 = NoneUL_t437;
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
        ifte_ret_t445 = ifte_ret_t444;
      }
      ifte_ret_t446 = ifte_ret_t445;
    }
    ifte_ret_t447 = ifte_ret_t446;
  }
  return ifte_ret_t447;
}

tll_ptr lam_fun_t449(tll_ptr c_v12355, tll_env env) {
  tll_ptr call_ret_t448;
  call_ret_t448 = digit_of_char_i40(c_v12355);
  return call_ret_t448;
}

tll_ptr nat_of_string_loop_i41(tll_ptr s_v12356, tll_ptr acc_v12357) {
  tll_ptr NoneUL_t455; tll_ptr SomeUL_t452; tll_ptr c_v12358;
  tll_ptr call_ret_t453; tll_ptr call_ret_t456; tll_ptr call_ret_t457;
  tll_ptr call_ret_t458; tll_ptr n_v12360; tll_ptr s_v12359;
  tll_ptr switch_ret_t451; tll_ptr switch_ret_t454;
  switch(((tll_node)s_v12356)->tag) {
    case 6:
      instr_struct(&SomeUL_t452, 18, 1, acc_v12357);
      switch_ret_t451 = SomeUL_t452;
      break;
    case 7:
      c_v12358 = ((tll_node)s_v12356)->data[0];
      s_v12359 = ((tll_node)s_v12356)->data[1];
      call_ret_t453 = digit_of_char_i40(c_v12358);
      switch(((tll_node)call_ret_t453)->tag) {
        case 17:
          instr_free_struct(call_ret_t453);
          instr_struct(&NoneUL_t455, 17, 0);
          switch_ret_t454 = NoneUL_t455;
          break;
        case 18:
          n_v12360 = ((tll_node)call_ret_t453)->data[0];
          instr_free_struct(call_ret_t453);
          call_ret_t458 = muln_i14(acc_v12357, (tll_ptr)10);
          call_ret_t457 = addn_i12(call_ret_t458, n_v12360);
          call_ret_t456 = nat_of_string_loop_i41(s_v12359, call_ret_t457);
          switch_ret_t454 = call_ret_t456;
          break;
      }
      switch_ret_t451 = switch_ret_t454;
      break;
  }
  return switch_ret_t451;
}

tll_ptr lam_fun_t460(tll_ptr acc_v12363, tll_env env) {
  tll_ptr call_ret_t459;
  call_ret_t459 = nat_of_string_loop_i41(env[0], acc_v12363);
  return call_ret_t459;
}

tll_ptr lam_fun_t462(tll_ptr s_v12361, tll_env env) {
  tll_ptr lam_clo_t461;
  instr_clo(&lam_clo_t461, &lam_fun_t460, 1, s_v12361);
  return lam_clo_t461;
}

tll_ptr nat_of_string_i42(tll_ptr s_v12364) {
  tll_ptr call_ret_t464;
  call_ret_t464 = nat_of_string_loop_i41(s_v12364, (tll_ptr)0);
  return call_ret_t464;
}

tll_ptr lam_fun_t466(tll_ptr s_v12365, tll_env env) {
  tll_ptr call_ret_t465;
  call_ret_t465 = nat_of_string_i42(s_v12365);
  return call_ret_t465;
}

tll_ptr ex_i43(tll_ptr e_v12366) {
  tll_ptr Char_t469; tll_ptr Char_t470; tll_ptr Char_t471; tll_ptr Char_t472;
  tll_ptr Char_t473; tll_ptr Char_t480; tll_ptr Char_t481; tll_ptr Char_t482;
  tll_ptr Char_t483; tll_ptr Char_t484; tll_ptr EmptyString_t474;
  tll_ptr EmptyString_t485; tll_ptr String_t475; tll_ptr String_t476;
  tll_ptr String_t477; tll_ptr String_t478; tll_ptr String_t479;
  tll_ptr String_t486; tll_ptr String_t487; tll_ptr String_t488;
  tll_ptr String_t489; tll_ptr String_t490; tll_ptr call_ret_t468;
  instr_struct(&Char_t469, 5, 1, (tll_ptr)104);
  instr_struct(&Char_t470, 5, 1, (tll_ptr)101);
  instr_struct(&Char_t471, 5, 1, (tll_ptr)108);
  instr_struct(&Char_t472, 5, 1, (tll_ptr)108);
  instr_struct(&Char_t473, 5, 1, (tll_ptr)111);
  instr_struct(&EmptyString_t474, 6, 0);
  instr_struct(&String_t475, 7, 2, Char_t473, EmptyString_t474);
  instr_struct(&String_t476, 7, 2, Char_t472, String_t475);
  instr_struct(&String_t477, 7, 2, Char_t471, String_t476);
  instr_struct(&String_t478, 7, 2, Char_t470, String_t477);
  instr_struct(&String_t479, 7, 2, Char_t469, String_t478);
  instr_struct(&Char_t480, 5, 1, (tll_ptr)119);
  instr_struct(&Char_t481, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t482, 5, 1, (tll_ptr)114);
  instr_struct(&Char_t483, 5, 1, (tll_ptr)108);
  instr_struct(&Char_t484, 5, 1, (tll_ptr)100);
  instr_struct(&EmptyString_t485, 6, 0);
  instr_struct(&String_t486, 7, 2, Char_t484, EmptyString_t485);
  instr_struct(&String_t487, 7, 2, Char_t483, String_t486);
  instr_struct(&String_t488, 7, 2, Char_t482, String_t487);
  instr_struct(&String_t489, 7, 2, Char_t481, String_t488);
  instr_struct(&String_t490, 7, 2, Char_t480, String_t489);
  call_ret_t468 = cats_i19(String_t479, String_t490);
  return call_ret_t468;
}

tll_ptr lam_fun_t492(tll_ptr e_v12367, tll_env env) {
  tll_ptr call_ret_t491;
  call_ret_t491 = ex_i43(e_v12367);
  return call_ret_t491;
}

int main() {
  instr_init();
  tll_ptr Char_t337; tll_ptr Char_t340; tll_ptr Char_t343; tll_ptr Char_t346;
  tll_ptr Char_t349; tll_ptr Char_t352; tll_ptr Char_t355; tll_ptr Char_t358;
  tll_ptr Char_t361; tll_ptr Char_t364; tll_ptr EmptyString_t338;
  tll_ptr EmptyString_t341; tll_ptr EmptyString_t344;
  tll_ptr EmptyString_t347; tll_ptr EmptyString_t350;
  tll_ptr EmptyString_t353; tll_ptr EmptyString_t356;
  tll_ptr EmptyString_t359; tll_ptr EmptyString_t362;
  tll_ptr EmptyString_t365; tll_ptr String_t339; tll_ptr String_t342;
  tll_ptr String_t345; tll_ptr String_t348; tll_ptr String_t351;
  tll_ptr String_t354; tll_ptr String_t357; tll_ptr String_t360;
  tll_ptr String_t363; tll_ptr String_t366; tll_ptr app_ret_t496;
  tll_ptr call_ret_t494; tll_ptr call_ret_t495; tll_ptr consUU_t368;
  tll_ptr consUU_t369; tll_ptr consUU_t370; tll_ptr consUU_t371;
  tll_ptr consUU_t372; tll_ptr consUU_t373; tll_ptr consUU_t374;
  tll_ptr consUU_t375; tll_ptr consUU_t376; tll_ptr consUU_t377;
  tll_ptr lam_clo_t104; tll_ptr lam_clo_t110; tll_ptr lam_clo_t118;
  tll_ptr lam_clo_t12; tll_ptr lam_clo_t126; tll_ptr lam_clo_t134;
  tll_ptr lam_clo_t140; tll_ptr lam_clo_t151; tll_ptr lam_clo_t16;
  tll_ptr lam_clo_t167; tll_ptr lam_clo_t179; tll_ptr lam_clo_t191;
  tll_ptr lam_clo_t203; tll_ptr lam_clo_t215; tll_ptr lam_clo_t227;
  tll_ptr lam_clo_t239; tll_ptr lam_clo_t252; tll_ptr lam_clo_t265;
  tll_ptr lam_clo_t278; tll_ptr lam_clo_t28; tll_ptr lam_clo_t288;
  tll_ptr lam_clo_t298; tll_ptr lam_clo_t308; tll_ptr lam_clo_t318;
  tll_ptr lam_clo_t327; tll_ptr lam_clo_t336; tll_ptr lam_clo_t34;
  tll_ptr lam_clo_t391; tll_ptr lam_clo_t396; tll_ptr lam_clo_t40;
  tll_ptr lam_clo_t406; tll_ptr lam_clo_t450; tll_ptr lam_clo_t46;
  tll_ptr lam_clo_t463; tll_ptr lam_clo_t467; tll_ptr lam_clo_t493;
  tll_ptr lam_clo_t52; tll_ptr lam_clo_t58; tll_ptr lam_clo_t6;
  tll_ptr lam_clo_t72; tll_ptr lam_clo_t77; tll_ptr lam_clo_t83;
  tll_ptr lam_clo_t92; tll_ptr lam_clo_t98; tll_ptr nilUU_t367;
  tll_ptr s_v12368;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i65 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i66 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i67 = lam_clo_t16;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  comparebclo_i68 = lam_clo_t28;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 0);
  ltenclo_i69 = lam_clo_t34;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 0);
  ltnclo_i70 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  gtenclo_i71 = lam_clo_t46;
  instr_clo(&lam_clo_t52, &lam_fun_t51, 0);
  gtnclo_i72 = lam_clo_t52;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  eqnclo_i73 = lam_clo_t58;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  comparenclo_i74 = lam_clo_t72;
  instr_clo(&lam_clo_t77, &lam_fun_t76, 0);
  predclo_i75 = lam_clo_t77;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i76 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i77 = lam_clo_t92;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  mulnclo_i78 = lam_clo_t98;
  instr_clo(&lam_clo_t104, &lam_fun_t103, 0);
  divnclo_i79 = lam_clo_t104;
  instr_clo(&lam_clo_t110, &lam_fun_t109, 0);
  modnclo_i80 = lam_clo_t110;
  instr_clo(&lam_clo_t118, &lam_fun_t117, 0);
  eqcclo_i81 = lam_clo_t118;
  instr_clo(&lam_clo_t126, &lam_fun_t125, 0);
  comparecclo_i82 = lam_clo_t126;
  instr_clo(&lam_clo_t134, &lam_fun_t133, 0);
  catsclo_i83 = lam_clo_t134;
  instr_clo(&lam_clo_t140, &lam_fun_t139, 0);
  strlenclo_i84 = lam_clo_t140;
  instr_clo(&lam_clo_t151, &lam_fun_t150, 0);
  eqsclo_i85 = lam_clo_t151;
  instr_clo(&lam_clo_t167, &lam_fun_t166, 0);
  comparesclo_i86 = lam_clo_t167;
  instr_clo(&lam_clo_t179, &lam_fun_t178, 0);
  and_thenUUUclo_i87 = lam_clo_t179;
  instr_clo(&lam_clo_t191, &lam_fun_t190, 0);
  and_thenUULclo_i88 = lam_clo_t191;
  instr_clo(&lam_clo_t203, &lam_fun_t202, 0);
  and_thenULUclo_i89 = lam_clo_t203;
  instr_clo(&lam_clo_t215, &lam_fun_t214, 0);
  and_thenULLclo_i90 = lam_clo_t215;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 0);
  and_thenLULclo_i91 = lam_clo_t227;
  instr_clo(&lam_clo_t239, &lam_fun_t238, 0);
  and_thenLLLclo_i92 = lam_clo_t239;
  instr_clo(&lam_clo_t252, &lam_fun_t251, 0);
  lenUUclo_i93 = lam_clo_t252;
  instr_clo(&lam_clo_t265, &lam_fun_t264, 0);
  lenULclo_i94 = lam_clo_t265;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 0);
  lenLLclo_i95 = lam_clo_t278;
  instr_clo(&lam_clo_t288, &lam_fun_t287, 0);
  appendUUclo_i96 = lam_clo_t288;
  instr_clo(&lam_clo_t298, &lam_fun_t297, 0);
  appendULclo_i97 = lam_clo_t298;
  instr_clo(&lam_clo_t308, &lam_fun_t307, 0);
  appendLLclo_i98 = lam_clo_t308;
  instr_clo(&lam_clo_t318, &lam_fun_t317, 0);
  readlineclo_i99 = lam_clo_t318;
  instr_clo(&lam_clo_t327, &lam_fun_t326, 0);
  printclo_i100 = lam_clo_t327;
  instr_clo(&lam_clo_t336, &lam_fun_t335, 0);
  prerrclo_i101 = lam_clo_t336;
  instr_struct(&Char_t337, 5, 1, (tll_ptr)48);
  instr_struct(&EmptyString_t338, 6, 0);
  instr_struct(&String_t339, 7, 2, Char_t337, EmptyString_t338);
  instr_struct(&Char_t340, 5, 1, (tll_ptr)49);
  instr_struct(&EmptyString_t341, 6, 0);
  instr_struct(&String_t342, 7, 2, Char_t340, EmptyString_t341);
  instr_struct(&Char_t343, 5, 1, (tll_ptr)50);
  instr_struct(&EmptyString_t344, 6, 0);
  instr_struct(&String_t345, 7, 2, Char_t343, EmptyString_t344);
  instr_struct(&Char_t346, 5, 1, (tll_ptr)51);
  instr_struct(&EmptyString_t347, 6, 0);
  instr_struct(&String_t348, 7, 2, Char_t346, EmptyString_t347);
  instr_struct(&Char_t349, 5, 1, (tll_ptr)52);
  instr_struct(&EmptyString_t350, 6, 0);
  instr_struct(&String_t351, 7, 2, Char_t349, EmptyString_t350);
  instr_struct(&Char_t352, 5, 1, (tll_ptr)53);
  instr_struct(&EmptyString_t353, 6, 0);
  instr_struct(&String_t354, 7, 2, Char_t352, EmptyString_t353);
  instr_struct(&Char_t355, 5, 1, (tll_ptr)54);
  instr_struct(&EmptyString_t356, 6, 0);
  instr_struct(&String_t357, 7, 2, Char_t355, EmptyString_t356);
  instr_struct(&Char_t358, 5, 1, (tll_ptr)55);
  instr_struct(&EmptyString_t359, 6, 0);
  instr_struct(&String_t360, 7, 2, Char_t358, EmptyString_t359);
  instr_struct(&Char_t361, 5, 1, (tll_ptr)56);
  instr_struct(&EmptyString_t362, 6, 0);
  instr_struct(&String_t363, 7, 2, Char_t361, EmptyString_t362);
  instr_struct(&Char_t364, 5, 1, (tll_ptr)57);
  instr_struct(&EmptyString_t365, 6, 0);
  instr_struct(&String_t366, 7, 2, Char_t364, EmptyString_t365);
  instr_struct(&nilUU_t367, 27, 0);
  instr_struct(&consUU_t368, 28, 2, String_t366, nilUU_t367);
  instr_struct(&consUU_t369, 28, 2, String_t363, consUU_t368);
  instr_struct(&consUU_t370, 28, 2, String_t360, consUU_t369);
  instr_struct(&consUU_t371, 28, 2, String_t357, consUU_t370);
  instr_struct(&consUU_t372, 28, 2, String_t354, consUU_t371);
  instr_struct(&consUU_t373, 28, 2, String_t351, consUU_t372);
  instr_struct(&consUU_t374, 28, 2, String_t348, consUU_t373);
  instr_struct(&consUU_t375, 28, 2, String_t345, consUU_t374);
  instr_struct(&consUU_t376, 28, 2, String_t342, consUU_t375);
  instr_struct(&consUU_t377, 28, 2, String_t339, consUU_t376);
  digits_i36 = consUU_t377;
  instr_clo(&lam_clo_t391, &lam_fun_t390, 0);
  get_atclo_i102 = lam_clo_t391;
  instr_clo(&lam_clo_t396, &lam_fun_t395, 0);
  string_of_digitclo_i103 = lam_clo_t396;
  instr_clo(&lam_clo_t406, &lam_fun_t405, 0);
  string_of_natclo_i104 = lam_clo_t406;
  instr_clo(&lam_clo_t450, &lam_fun_t449, 0);
  digit_of_charclo_i105 = lam_clo_t450;
  instr_clo(&lam_clo_t463, &lam_fun_t462, 0);
  nat_of_string_loopclo_i106 = lam_clo_t463;
  instr_clo(&lam_clo_t467, &lam_fun_t466, 0);
  nat_of_stringclo_i107 = lam_clo_t467;
  instr_clo(&lam_clo_t493, &lam_fun_t492, 0);
  exclo_i108 = lam_clo_t493;
  call_ret_t494 = ex_i43(0);
  s_v12368 = call_ret_t494;
  call_ret_t495 = print_i34(s_v12368);
  instr_app(&app_ret_t496, call_ret_t495, 0);
  instr_free_clo(call_ret_t495);
  return 0;
}

