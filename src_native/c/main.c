#include"runtime.h"

tll_ptr andb_i2(tll_ptr b1_v157586, tll_ptr b2_v157587);
tll_ptr orb_i3(tll_ptr b1_v157591, tll_ptr b2_v157592);
tll_ptr notb_i4(tll_ptr b_v157596);
tll_ptr compareb_i5(tll_ptr b1_v157598, tll_ptr b2_v157599);
tll_ptr lten_i6(tll_ptr x_v157603, tll_ptr y_v157604);
tll_ptr gten_i7(tll_ptr x_v157608, tll_ptr y_v157609);
tll_ptr ltn_i8(tll_ptr x_v157613, tll_ptr y_v157614);
tll_ptr gtn_i9(tll_ptr x_v157618, tll_ptr y_v157619);
tll_ptr eqn_i10(tll_ptr x_v157623, tll_ptr y_v157624);
tll_ptr comparen_i11(tll_ptr n1_v157628, tll_ptr n2_v157629);
tll_ptr pred_i12(tll_ptr x_v157633);
tll_ptr addn_i13(tll_ptr x_v157635, tll_ptr y_v157636);
tll_ptr subn_i14(tll_ptr x_v157640, tll_ptr y_v157641);
tll_ptr muln_i15(tll_ptr x_v157645, tll_ptr y_v157646);
tll_ptr divn_i16(tll_ptr x_v157650, tll_ptr y_v157651);
tll_ptr modn_i17(tll_ptr x_v157655, tll_ptr y_v157656);
tll_ptr eqc_i18(tll_ptr c1_v157660, tll_ptr c2_v157661);
tll_ptr comparec_i19(tll_ptr c1_v157667, tll_ptr c2_v157668);
tll_ptr cats_i20(tll_ptr s1_v157674, tll_ptr s2_v157675);
tll_ptr strlen_i21(tll_ptr s_v157681);
tll_ptr eqs_i22(tll_ptr s1_v157685, tll_ptr s2_v157686);
tll_ptr compares_i23(tll_ptr s1_v157696, tll_ptr s2_v157697);
tll_ptr and_thenUUU_i75(tll_ptr A_v157707, tll_ptr B_v157708, tll_ptr opt_v157709, tll_ptr f_v157710);
tll_ptr and_thenUUL_i74(tll_ptr A_v157722, tll_ptr B_v157723, tll_ptr opt_v157724, tll_ptr f_v157725);
tll_ptr and_thenULU_i73(tll_ptr A_v157737, tll_ptr B_v157738, tll_ptr opt_v157739, tll_ptr f_v157740);
tll_ptr and_thenULL_i72(tll_ptr A_v157752, tll_ptr B_v157753, tll_ptr opt_v157754, tll_ptr f_v157755);
tll_ptr and_thenLUL_i70(tll_ptr A_v157767, tll_ptr B_v157768, tll_ptr opt_v157769, tll_ptr f_v157770);
tll_ptr and_thenLLL_i68(tll_ptr A_v157782, tll_ptr B_v157783, tll_ptr opt_v157784, tll_ptr f_v157785);
tll_ptr lenUU_i79(tll_ptr A_v157797, tll_ptr xs_v157798);
tll_ptr lenUL_i78(tll_ptr A_v157806, tll_ptr xs_v157807);
tll_ptr lenLL_i76(tll_ptr A_v157815, tll_ptr xs_v157816);
tll_ptr appendUU_i83(tll_ptr A_v157824, tll_ptr xs_v157825, tll_ptr ys_v157826);
tll_ptr appendUL_i82(tll_ptr A_v157835, tll_ptr xs_v157836, tll_ptr ys_v157837);
tll_ptr appendLL_i80(tll_ptr A_v157846, tll_ptr xs_v157847, tll_ptr ys_v157848);
tll_ptr readline_i33(tll_ptr __v157857);
tll_ptr print_i34(tll_ptr s_v157872);
tll_ptr prerr_i35(tll_ptr s_v157883);
tll_ptr get_at_i37(tll_ptr A_v157894, tll_ptr n_v157895, tll_ptr xs_v157896, tll_ptr a_v157897);
tll_ptr string_of_digit_i38(tll_ptr n_v157912);
tll_ptr string_of_nat_i39(tll_ptr n_v157914);
tll_ptr digit_of_char_i40(tll_ptr c_v157918);
tll_ptr nat_of_string_loop_i41(tll_ptr s_v157920, tll_ptr acc_v157921);
tll_ptr nat_of_string_i42(tll_ptr s_v157928);
tll_ptr contains_i49(tll_ptr c_v157930, tll_ptr s_v157931);
tll_ptr string_diff_i50(tll_ptr ans_v157937, tll_ptr s1_v157938, tll_ptr s2_v157939);
tll_ptr wordle_diff_i52(tll_ptr ans_v157950, tll_ptr guess_v157951);
tll_ptr eqw_i53(tll_ptr w1_v157959, tll_ptr w2_v157960);
tll_ptr read_word_i60(tll_ptr __v157968);
tll_ptr player_loop_i61(tll_ptr ans_v157987, tll_ptr repeat_v157988, tll_ptr c_v157989);
tll_ptr player_i62(tll_ptr c_v158106);
tll_ptr server_loop_i63(tll_ptr ans_v158125, tll_ptr repeat_v158126, tll_ptr c_v158127);
tll_ptr server_i64(tll_ptr c_v158182);

tll_ptr addnclo_i101;
tll_ptr and_thenLLLclo_i117;
tll_ptr and_thenLULclo_i116;
tll_ptr and_thenULLclo_i115;
tll_ptr and_thenULUclo_i114;
tll_ptr and_thenUULclo_i113;
tll_ptr and_thenUUUclo_i112;
tll_ptr andbclo_i90;
tll_ptr appendLLclo_i123;
tll_ptr appendULclo_i122;
tll_ptr appendUUclo_i121;
tll_ptr catsclo_i108;
tll_ptr comparebclo_i93;
tll_ptr comparecclo_i107;
tll_ptr comparenclo_i99;
tll_ptr comparesclo_i111;
tll_ptr containsclo_i133;
tll_ptr digit_of_charclo_i130;
tll_ptr digits_i36;
tll_ptr divnclo_i104;
tll_ptr eqcclo_i106;
tll_ptr eqnclo_i98;
tll_ptr eqsclo_i110;
tll_ptr eqwclo_i136;
tll_ptr get_atclo_i127;
tll_ptr gtenclo_i95;
tll_ptr gtnclo_i97;
tll_ptr lenLLclo_i120;
tll_ptr lenULclo_i119;
tll_ptr lenUUclo_i118;
tll_ptr ltenclo_i94;
tll_ptr ltnclo_i96;
tll_ptr modnclo_i105;
tll_ptr mulnclo_i103;
tll_ptr nat_of_string_loopclo_i131;
tll_ptr nat_of_stringclo_i132;
tll_ptr notbclo_i92;
tll_ptr orbclo_i91;
tll_ptr player_loopclo_i138;
tll_ptr playerclo_i139;
tll_ptr predclo_i100;
tll_ptr prerrclo_i126;
tll_ptr printclo_i125;
tll_ptr read_wordclo_i137;
tll_ptr readlineclo_i124;
tll_ptr server_loopclo_i140;
tll_ptr serverclo_i141;
tll_ptr string_diffclo_i134;
tll_ptr string_of_digitclo_i128;
tll_ptr string_of_natclo_i129;
tll_ptr strlenclo_i109;
tll_ptr subnclo_i102;
tll_ptr wordle_diffclo_i135;

tll_ptr andb_i2(tll_ptr b1_v157586, tll_ptr b2_v157587) {
  tll_ptr ifte_ret_t1;
  if (b1_v157586) {
    ifte_ret_t1 = b2_v157587;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v157590, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i2(env[0], b2_v157590);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v157588, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v157588);
  return lam_clo_t4;
}

tll_ptr orb_i3(tll_ptr b1_v157591, tll_ptr b2_v157592) {
  tll_ptr ifte_ret_t7;
  if (b1_v157591) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v157592;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v157595, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i3(env[0], b2_v157595);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v157593, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v157593);
  return lam_clo_t10;
}

tll_ptr notb_i4(tll_ptr b_v157596) {
  tll_ptr ifte_ret_t13;
  if (b_v157596) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v157597, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i4(b_v157597);
  return call_ret_t14;
}

tll_ptr compareb_i5(tll_ptr b1_v157598, tll_ptr b2_v157599) {
  tll_ptr EQ_t17; tll_ptr EQ_t21; tll_ptr GT_t18; tll_ptr LT_t20;
  tll_ptr ifte_ret_t19; tll_ptr ifte_ret_t22; tll_ptr ifte_ret_t23;
  if (b1_v157598) {
    if (b2_v157599) {
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
    if (b2_v157599) {
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

tll_ptr lam_fun_t25(tll_ptr b2_v157602, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = compareb_i5(env[0], b2_v157602);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr b1_v157600, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, b1_v157600);
  return lam_clo_t26;
}

tll_ptr lten_i6(tll_ptr x_v157603, tll_ptr y_v157604) {
  tll_ptr lten_ret_t29;
  instr_lten(&lten_ret_t29, x_v157603, y_v157604);
  return lten_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v157607, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = lten_i6(env[0], y_v157607);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v157605, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v157605);
  return lam_clo_t32;
}

tll_ptr gten_i7(tll_ptr x_v157608, tll_ptr y_v157609) {
  tll_ptr gten_ret_t35;
  instr_gten(&gten_ret_t35, x_v157608, y_v157609);
  return gten_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v157612, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = gten_i7(env[0], y_v157612);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v157610, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v157610);
  return lam_clo_t38;
}

tll_ptr ltn_i8(tll_ptr x_v157613, tll_ptr y_v157614) {
  tll_ptr ltn_ret_t41;
  instr_ltn(&ltn_ret_t41, x_v157613, y_v157614);
  return ltn_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v157617, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = ltn_i8(env[0], y_v157617);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v157615, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v157615);
  return lam_clo_t44;
}

tll_ptr gtn_i9(tll_ptr x_v157618, tll_ptr y_v157619) {
  tll_ptr gtn_ret_t47;
  instr_gtn(&gtn_ret_t47, x_v157618, y_v157619);
  return gtn_ret_t47;
}

tll_ptr lam_fun_t49(tll_ptr y_v157622, tll_env env) {
  tll_ptr call_ret_t48;
  call_ret_t48 = gtn_i9(env[0], y_v157622);
  return call_ret_t48;
}

tll_ptr lam_fun_t51(tll_ptr x_v157620, tll_env env) {
  tll_ptr lam_clo_t50;
  instr_clo(&lam_clo_t50, &lam_fun_t49, 1, x_v157620);
  return lam_clo_t50;
}

tll_ptr eqn_i10(tll_ptr x_v157623, tll_ptr y_v157624) {
  tll_ptr eqn_ret_t53;
  instr_eqn(&eqn_ret_t53, x_v157623, y_v157624);
  return eqn_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v157627, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = eqn_i10(env[0], y_v157627);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v157625, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v157625);
  return lam_clo_t56;
}

tll_ptr comparen_i11(tll_ptr n1_v157628, tll_ptr n2_v157629) {
  tll_ptr EQ_t65; tll_ptr GT_t62; tll_ptr LT_t64; tll_ptr add_ret_t60;
  tll_ptr add_ret_t61; tll_ptr call_ret_t59; tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t66; tll_ptr ifte_ret_t67;
  if (n1_v157628) {
    if (n2_v157629) {
      add_ret_t60 = n1_v157628 - 1;
      add_ret_t61 = n2_v157629 - 1;
      call_ret_t59 = comparen_i11(add_ret_t60, add_ret_t61);
      ifte_ret_t63 = call_ret_t59;
    }
    else {
      instr_struct(&GT_t62, 2, 0);
      ifte_ret_t63 = GT_t62;
    }
    ifte_ret_t67 = ifte_ret_t63;
  }
  else {
    if (n2_v157629) {
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

tll_ptr lam_fun_t69(tll_ptr n2_v157632, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = comparen_i11(env[0], n2_v157632);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr n1_v157630, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, n1_v157630);
  return lam_clo_t70;
}

tll_ptr pred_i12(tll_ptr x_v157633) {
  tll_ptr add_ret_t73; tll_ptr ifte_ret_t74;
  if (x_v157633) {
    add_ret_t73 = x_v157633 - 1;
    ifte_ret_t74 = add_ret_t73;
  }
  else {
    ifte_ret_t74 = (tll_ptr)0;
  }
  return ifte_ret_t74;
}

tll_ptr lam_fun_t76(tll_ptr x_v157634, tll_env env) {
  tll_ptr call_ret_t75;
  call_ret_t75 = pred_i12(x_v157634);
  return call_ret_t75;
}

tll_ptr addn_i13(tll_ptr x_v157635, tll_ptr y_v157636) {
  tll_ptr addn_ret_t78;
  instr_addn(&addn_ret_t78, x_v157635, y_v157636);
  return addn_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v157639, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i13(env[0], y_v157639);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v157637, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v157637);
  return lam_clo_t81;
}

tll_ptr subn_i14(tll_ptr x_v157640, tll_ptr y_v157641) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v157641) {
    call_ret_t85 = pred_i12(x_v157640);
    add_ret_t86 = y_v157641 - 1;
    call_ret_t84 = subn_i14(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v157640;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v157644, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i14(env[0], y_v157644);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v157642, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v157642);
  return lam_clo_t90;
}

tll_ptr muln_i15(tll_ptr x_v157645, tll_ptr y_v157646) {
  tll_ptr muln_ret_t93;
  instr_muln(&muln_ret_t93, x_v157645, y_v157646);
  return muln_ret_t93;
}

tll_ptr lam_fun_t95(tll_ptr y_v157649, tll_env env) {
  tll_ptr call_ret_t94;
  call_ret_t94 = muln_i15(env[0], y_v157649);
  return call_ret_t94;
}

tll_ptr lam_fun_t97(tll_ptr x_v157647, tll_env env) {
  tll_ptr lam_clo_t96;
  instr_clo(&lam_clo_t96, &lam_fun_t95, 1, x_v157647);
  return lam_clo_t96;
}

tll_ptr divn_i16(tll_ptr x_v157650, tll_ptr y_v157651) {
  tll_ptr divn_ret_t99;
  instr_divn(&divn_ret_t99, x_v157650, y_v157651);
  return divn_ret_t99;
}

tll_ptr lam_fun_t101(tll_ptr y_v157654, tll_env env) {
  tll_ptr call_ret_t100;
  call_ret_t100 = divn_i16(env[0], y_v157654);
  return call_ret_t100;
}

tll_ptr lam_fun_t103(tll_ptr x_v157652, tll_env env) {
  tll_ptr lam_clo_t102;
  instr_clo(&lam_clo_t102, &lam_fun_t101, 1, x_v157652);
  return lam_clo_t102;
}

tll_ptr modn_i17(tll_ptr x_v157655, tll_ptr y_v157656) {
  tll_ptr modn_ret_t105;
  instr_modn(&modn_ret_t105, x_v157655, y_v157656);
  return modn_ret_t105;
}

tll_ptr lam_fun_t107(tll_ptr y_v157659, tll_env env) {
  tll_ptr call_ret_t106;
  call_ret_t106 = modn_i17(env[0], y_v157659);
  return call_ret_t106;
}

tll_ptr lam_fun_t109(tll_ptr x_v157657, tll_env env) {
  tll_ptr lam_clo_t108;
  instr_clo(&lam_clo_t108, &lam_fun_t107, 1, x_v157657);
  return lam_clo_t108;
}

tll_ptr eqc_i18(tll_ptr c1_v157660, tll_ptr c2_v157661) {
  tll_ptr call_ret_t113; tll_ptr n1_v157662; tll_ptr n2_v157663;
  tll_ptr switch_ret_t111; tll_ptr switch_ret_t112;
  switch(((tll_node)c1_v157660)->tag) {
    case 5:
      n1_v157662 = ((tll_node)c1_v157660)->data[0];
      switch(((tll_node)c2_v157661)->tag) {
        case 5:
          n2_v157663 = ((tll_node)c2_v157661)->data[0];
          call_ret_t113 = eqn_i10(n1_v157662, n2_v157663);
          switch_ret_t112 = call_ret_t113;
          break;
      }
      switch_ret_t111 = switch_ret_t112;
      break;
  }
  return switch_ret_t111;
}

tll_ptr lam_fun_t115(tll_ptr c2_v157666, tll_env env) {
  tll_ptr call_ret_t114;
  call_ret_t114 = eqc_i18(env[0], c2_v157666);
  return call_ret_t114;
}

tll_ptr lam_fun_t117(tll_ptr c1_v157664, tll_env env) {
  tll_ptr lam_clo_t116;
  instr_clo(&lam_clo_t116, &lam_fun_t115, 1, c1_v157664);
  return lam_clo_t116;
}

tll_ptr comparec_i19(tll_ptr c1_v157667, tll_ptr c2_v157668) {
  tll_ptr call_ret_t121; tll_ptr n1_v157669; tll_ptr n2_v157670;
  tll_ptr switch_ret_t119; tll_ptr switch_ret_t120;
  switch(((tll_node)c1_v157667)->tag) {
    case 5:
      n1_v157669 = ((tll_node)c1_v157667)->data[0];
      switch(((tll_node)c2_v157668)->tag) {
        case 5:
          n2_v157670 = ((tll_node)c2_v157668)->data[0];
          call_ret_t121 = comparen_i11(n1_v157669, n2_v157670);
          switch_ret_t120 = call_ret_t121;
          break;
      }
      switch_ret_t119 = switch_ret_t120;
      break;
  }
  return switch_ret_t119;
}

tll_ptr lam_fun_t123(tll_ptr c2_v157673, tll_env env) {
  tll_ptr call_ret_t122;
  call_ret_t122 = comparec_i19(env[0], c2_v157673);
  return call_ret_t122;
}

tll_ptr lam_fun_t125(tll_ptr c1_v157671, tll_env env) {
  tll_ptr lam_clo_t124;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 1, c1_v157671);
  return lam_clo_t124;
}

tll_ptr cats_i20(tll_ptr s1_v157674, tll_ptr s2_v157675) {
  tll_ptr String_t129; tll_ptr c_v157676; tll_ptr call_ret_t128;
  tll_ptr s1_v157677; tll_ptr switch_ret_t127;
  switch(((tll_node)s1_v157674)->tag) {
    case 6:
      switch_ret_t127 = s2_v157675;
      break;
    case 7:
      c_v157676 = ((tll_node)s1_v157674)->data[0];
      s1_v157677 = ((tll_node)s1_v157674)->data[1];
      call_ret_t128 = cats_i20(s1_v157677, s2_v157675);
      instr_struct(&String_t129, 7, 2, c_v157676, call_ret_t128);
      switch_ret_t127 = String_t129;
      break;
  }
  return switch_ret_t127;
}

tll_ptr lam_fun_t131(tll_ptr s2_v157680, tll_env env) {
  tll_ptr call_ret_t130;
  call_ret_t130 = cats_i20(env[0], s2_v157680);
  return call_ret_t130;
}

tll_ptr lam_fun_t133(tll_ptr s1_v157678, tll_env env) {
  tll_ptr lam_clo_t132;
  instr_clo(&lam_clo_t132, &lam_fun_t131, 1, s1_v157678);
  return lam_clo_t132;
}

tll_ptr strlen_i21(tll_ptr s_v157681) {
  tll_ptr __v157682; tll_ptr add_ret_t137; tll_ptr call_ret_t136;
  tll_ptr s_v157683; tll_ptr switch_ret_t135;
  switch(((tll_node)s_v157681)->tag) {
    case 6:
      switch_ret_t135 = (tll_ptr)0;
      break;
    case 7:
      __v157682 = ((tll_node)s_v157681)->data[0];
      s_v157683 = ((tll_node)s_v157681)->data[1];
      call_ret_t136 = strlen_i21(s_v157683);
      add_ret_t137 = call_ret_t136 + 1;
      switch_ret_t135 = add_ret_t137;
      break;
  }
  return switch_ret_t135;
}

tll_ptr lam_fun_t139(tll_ptr s_v157684, tll_env env) {
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i21(s_v157684);
  return call_ret_t138;
}

tll_ptr eqs_i22(tll_ptr s1_v157685, tll_ptr s2_v157686) {
  tll_ptr __v157687; tll_ptr __v157688; tll_ptr c1_v157689;
  tll_ptr c2_v157691; tll_ptr call_ret_t144; tll_ptr call_ret_t145;
  tll_ptr call_ret_t146; tll_ptr s1_v157690; tll_ptr s2_v157692;
  tll_ptr switch_ret_t141; tll_ptr switch_ret_t142; tll_ptr switch_ret_t143;
  switch(((tll_node)s1_v157685)->tag) {
    case 6:
      switch(((tll_node)s2_v157686)->tag) {
        case 6:
          switch_ret_t142 = (tll_ptr)1;
          break;
        case 7:
          __v157687 = ((tll_node)s2_v157686)->data[0];
          __v157688 = ((tll_node)s2_v157686)->data[1];
          switch_ret_t142 = (tll_ptr)0;
          break;
      }
      switch_ret_t141 = switch_ret_t142;
      break;
    case 7:
      c1_v157689 = ((tll_node)s1_v157685)->data[0];
      s1_v157690 = ((tll_node)s1_v157685)->data[1];
      switch(((tll_node)s2_v157686)->tag) {
        case 6:
          switch_ret_t143 = (tll_ptr)0;
          break;
        case 7:
          c2_v157691 = ((tll_node)s2_v157686)->data[0];
          s2_v157692 = ((tll_node)s2_v157686)->data[1];
          call_ret_t145 = eqc_i18(c1_v157689, c2_v157691);
          call_ret_t146 = eqs_i22(s1_v157690, s2_v157692);
          call_ret_t144 = andb_i2(call_ret_t145, call_ret_t146);
          switch_ret_t143 = call_ret_t144;
          break;
      }
      switch_ret_t141 = switch_ret_t143;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t148(tll_ptr s2_v157695, tll_env env) {
  tll_ptr call_ret_t147;
  call_ret_t147 = eqs_i22(env[0], s2_v157695);
  return call_ret_t147;
}

tll_ptr lam_fun_t150(tll_ptr s1_v157693, tll_env env) {
  tll_ptr lam_clo_t149;
  instr_clo(&lam_clo_t149, &lam_fun_t148, 1, s1_v157693);
  return lam_clo_t149;
}

tll_ptr compares_i23(tll_ptr s1_v157696, tll_ptr s2_v157697) {
  tll_ptr EQ_t154; tll_ptr GT_t157; tll_ptr GT_t162; tll_ptr LT_t155;
  tll_ptr LT_t161; tll_ptr __v157698; tll_ptr __v157699; tll_ptr c1_v157700;
  tll_ptr c2_v157702; tll_ptr call_ret_t158; tll_ptr call_ret_t160;
  tll_ptr s1_v157701; tll_ptr s2_v157703; tll_ptr switch_ret_t152;
  tll_ptr switch_ret_t153; tll_ptr switch_ret_t156; tll_ptr switch_ret_t159;
  switch(((tll_node)s1_v157696)->tag) {
    case 6:
      switch(((tll_node)s2_v157697)->tag) {
        case 6:
          instr_struct(&EQ_t154, 3, 0);
          switch_ret_t153 = EQ_t154;
          break;
        case 7:
          __v157698 = ((tll_node)s2_v157697)->data[0];
          __v157699 = ((tll_node)s2_v157697)->data[1];
          instr_struct(&LT_t155, 1, 0);
          switch_ret_t153 = LT_t155;
          break;
      }
      switch_ret_t152 = switch_ret_t153;
      break;
    case 7:
      c1_v157700 = ((tll_node)s1_v157696)->data[0];
      s1_v157701 = ((tll_node)s1_v157696)->data[1];
      switch(((tll_node)s2_v157697)->tag) {
        case 6:
          instr_struct(&GT_t157, 2, 0);
          switch_ret_t156 = GT_t157;
          break;
        case 7:
          c2_v157702 = ((tll_node)s2_v157697)->data[0];
          s2_v157703 = ((tll_node)s2_v157697)->data[1];
          call_ret_t158 = comparec_i19(c1_v157700, c2_v157702);
          switch(((tll_node)call_ret_t158)->tag) {
            case 3:
              call_ret_t160 = compares_i23(s1_v157701, s2_v157703);
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

tll_ptr lam_fun_t164(tll_ptr s2_v157706, tll_env env) {
  tll_ptr call_ret_t163;
  call_ret_t163 = compares_i23(env[0], s2_v157706);
  return call_ret_t163;
}

tll_ptr lam_fun_t166(tll_ptr s1_v157704, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, s1_v157704);
  return lam_clo_t165;
}

tll_ptr and_thenUUU_i75(tll_ptr A_v157707, tll_ptr B_v157708, tll_ptr opt_v157709, tll_ptr f_v157710) {
  tll_ptr NoneUU_t169; tll_ptr app_ret_t170; tll_ptr switch_ret_t168;
  tll_ptr x_v157711;
  switch(((tll_node)opt_v157709)->tag) {
    case 19:
      instr_struct(&NoneUU_t169, 19, 0);
      switch_ret_t168 = NoneUU_t169;
      break;
    case 20:
      x_v157711 = ((tll_node)opt_v157709)->data[0];
      instr_app(&app_ret_t170, f_v157710, x_v157711);
      switch_ret_t168 = app_ret_t170;
      break;
  }
  return switch_ret_t168;
}

tll_ptr lam_fun_t172(tll_ptr f_v157721, tll_env env) {
  tll_ptr call_ret_t171;
  call_ret_t171 = and_thenUUU_i75(env[2], env[1], env[0], f_v157721);
  return call_ret_t171;
}

tll_ptr lam_fun_t174(tll_ptr opt_v157719, tll_env env) {
  tll_ptr lam_clo_t173;
  instr_clo(&lam_clo_t173, &lam_fun_t172, 3, opt_v157719, env[0], env[1]);
  return lam_clo_t173;
}

tll_ptr lam_fun_t176(tll_ptr B_v157716, tll_env env) {
  tll_ptr lam_clo_t175;
  instr_clo(&lam_clo_t175, &lam_fun_t174, 2, B_v157716, env[0]);
  return lam_clo_t175;
}

tll_ptr lam_fun_t178(tll_ptr A_v157712, tll_env env) {
  tll_ptr lam_clo_t177;
  instr_clo(&lam_clo_t177, &lam_fun_t176, 1, A_v157712);
  return lam_clo_t177;
}

tll_ptr and_thenUUL_i74(tll_ptr A_v157722, tll_ptr B_v157723, tll_ptr opt_v157724, tll_ptr f_v157725) {
  tll_ptr NoneUL_t181; tll_ptr app_ret_t182; tll_ptr switch_ret_t180;
  tll_ptr x_v157726;
  switch(((tll_node)opt_v157724)->tag) {
    case 17:
      instr_free_struct(opt_v157724);
      instr_struct(&NoneUL_t181, 17, 0);
      switch_ret_t180 = NoneUL_t181;
      break;
    case 18:
      x_v157726 = ((tll_node)opt_v157724)->data[0];
      instr_free_struct(opt_v157724);
      instr_app(&app_ret_t182, f_v157725, x_v157726);
      switch_ret_t180 = app_ret_t182;
      break;
  }
  return switch_ret_t180;
}

tll_ptr lam_fun_t184(tll_ptr f_v157736, tll_env env) {
  tll_ptr call_ret_t183;
  call_ret_t183 = and_thenUUL_i74(env[2], env[1], env[0], f_v157736);
  return call_ret_t183;
}

tll_ptr lam_fun_t186(tll_ptr opt_v157734, tll_env env) {
  tll_ptr lam_clo_t185;
  instr_clo(&lam_clo_t185, &lam_fun_t184, 3, opt_v157734, env[0], env[1]);
  return lam_clo_t185;
}

tll_ptr lam_fun_t188(tll_ptr B_v157731, tll_env env) {
  tll_ptr lam_clo_t187;
  instr_clo(&lam_clo_t187, &lam_fun_t186, 2, B_v157731, env[0]);
  return lam_clo_t187;
}

tll_ptr lam_fun_t190(tll_ptr A_v157727, tll_env env) {
  tll_ptr lam_clo_t189;
  instr_clo(&lam_clo_t189, &lam_fun_t188, 1, A_v157727);
  return lam_clo_t189;
}

tll_ptr and_thenULU_i73(tll_ptr A_v157737, tll_ptr B_v157738, tll_ptr opt_v157739, tll_ptr f_v157740) {
  tll_ptr NoneLU_t193; tll_ptr app_ret_t194; tll_ptr switch_ret_t192;
  tll_ptr x_v157741;
  switch(((tll_node)opt_v157739)->tag) {
    case 19:
      instr_struct(&NoneLU_t193, 15, 0);
      switch_ret_t192 = NoneLU_t193;
      break;
    case 20:
      x_v157741 = ((tll_node)opt_v157739)->data[0];
      instr_app(&app_ret_t194, f_v157740, x_v157741);
      switch_ret_t192 = app_ret_t194;
      break;
  }
  return switch_ret_t192;
}

tll_ptr lam_fun_t196(tll_ptr f_v157751, tll_env env) {
  tll_ptr call_ret_t195;
  call_ret_t195 = and_thenULU_i73(env[2], env[1], env[0], f_v157751);
  return call_ret_t195;
}

tll_ptr lam_fun_t198(tll_ptr opt_v157749, tll_env env) {
  tll_ptr lam_clo_t197;
  instr_clo(&lam_clo_t197, &lam_fun_t196, 3, opt_v157749, env[0], env[1]);
  return lam_clo_t197;
}

tll_ptr lam_fun_t200(tll_ptr B_v157746, tll_env env) {
  tll_ptr lam_clo_t199;
  instr_clo(&lam_clo_t199, &lam_fun_t198, 2, B_v157746, env[0]);
  return lam_clo_t199;
}

tll_ptr lam_fun_t202(tll_ptr A_v157742, tll_env env) {
  tll_ptr lam_clo_t201;
  instr_clo(&lam_clo_t201, &lam_fun_t200, 1, A_v157742);
  return lam_clo_t201;
}

tll_ptr and_thenULL_i72(tll_ptr A_v157752, tll_ptr B_v157753, tll_ptr opt_v157754, tll_ptr f_v157755) {
  tll_ptr NoneLL_t205; tll_ptr app_ret_t206; tll_ptr switch_ret_t204;
  tll_ptr x_v157756;
  switch(((tll_node)opt_v157754)->tag) {
    case 17:
      instr_free_struct(opt_v157754);
      instr_struct(&NoneLL_t205, 13, 0);
      switch_ret_t204 = NoneLL_t205;
      break;
    case 18:
      x_v157756 = ((tll_node)opt_v157754)->data[0];
      instr_free_struct(opt_v157754);
      instr_app(&app_ret_t206, f_v157755, x_v157756);
      switch_ret_t204 = app_ret_t206;
      break;
  }
  return switch_ret_t204;
}

tll_ptr lam_fun_t208(tll_ptr f_v157766, tll_env env) {
  tll_ptr call_ret_t207;
  call_ret_t207 = and_thenULL_i72(env[2], env[1], env[0], f_v157766);
  return call_ret_t207;
}

tll_ptr lam_fun_t210(tll_ptr opt_v157764, tll_env env) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 3, opt_v157764, env[0], env[1]);
  return lam_clo_t209;
}

tll_ptr lam_fun_t212(tll_ptr B_v157761, tll_env env) {
  tll_ptr lam_clo_t211;
  instr_clo(&lam_clo_t211, &lam_fun_t210, 2, B_v157761, env[0]);
  return lam_clo_t211;
}

tll_ptr lam_fun_t214(tll_ptr A_v157757, tll_env env) {
  tll_ptr lam_clo_t213;
  instr_clo(&lam_clo_t213, &lam_fun_t212, 1, A_v157757);
  return lam_clo_t213;
}

tll_ptr and_thenLUL_i70(tll_ptr A_v157767, tll_ptr B_v157768, tll_ptr opt_v157769, tll_ptr f_v157770) {
  tll_ptr NoneUL_t217; tll_ptr app_ret_t218; tll_ptr switch_ret_t216;
  tll_ptr x_v157771;
  switch(((tll_node)opt_v157769)->tag) {
    case 13:
      instr_free_struct(opt_v157769);
      instr_struct(&NoneUL_t217, 17, 0);
      switch_ret_t216 = NoneUL_t217;
      break;
    case 14:
      x_v157771 = ((tll_node)opt_v157769)->data[0];
      instr_free_struct(opt_v157769);
      instr_app(&app_ret_t218, f_v157770, x_v157771);
      switch_ret_t216 = app_ret_t218;
      break;
  }
  return switch_ret_t216;
}

tll_ptr lam_fun_t220(tll_ptr f_v157781, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = and_thenLUL_i70(env[2], env[1], env[0], f_v157781);
  return call_ret_t219;
}

tll_ptr lam_fun_t222(tll_ptr opt_v157779, tll_env env) {
  tll_ptr lam_clo_t221;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 3, opt_v157779, env[0], env[1]);
  return lam_clo_t221;
}

tll_ptr lam_fun_t224(tll_ptr B_v157776, tll_env env) {
  tll_ptr lam_clo_t223;
  instr_clo(&lam_clo_t223, &lam_fun_t222, 2, B_v157776, env[0]);
  return lam_clo_t223;
}

tll_ptr lam_fun_t226(tll_ptr A_v157772, tll_env env) {
  tll_ptr lam_clo_t225;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 1, A_v157772);
  return lam_clo_t225;
}

tll_ptr and_thenLLL_i68(tll_ptr A_v157782, tll_ptr B_v157783, tll_ptr opt_v157784, tll_ptr f_v157785) {
  tll_ptr NoneLL_t229; tll_ptr app_ret_t230; tll_ptr switch_ret_t228;
  tll_ptr x_v157786;
  switch(((tll_node)opt_v157784)->tag) {
    case 13:
      instr_free_struct(opt_v157784);
      instr_struct(&NoneLL_t229, 13, 0);
      switch_ret_t228 = NoneLL_t229;
      break;
    case 14:
      x_v157786 = ((tll_node)opt_v157784)->data[0];
      instr_free_struct(opt_v157784);
      instr_app(&app_ret_t230, f_v157785, x_v157786);
      switch_ret_t228 = app_ret_t230;
      break;
  }
  return switch_ret_t228;
}

tll_ptr lam_fun_t232(tll_ptr f_v157796, tll_env env) {
  tll_ptr call_ret_t231;
  call_ret_t231 = and_thenLLL_i68(env[2], env[1], env[0], f_v157796);
  return call_ret_t231;
}

tll_ptr lam_fun_t234(tll_ptr opt_v157794, tll_env env) {
  tll_ptr lam_clo_t233;
  instr_clo(&lam_clo_t233, &lam_fun_t232, 3, opt_v157794, env[0], env[1]);
  return lam_clo_t233;
}

tll_ptr lam_fun_t236(tll_ptr B_v157791, tll_env env) {
  tll_ptr lam_clo_t235;
  instr_clo(&lam_clo_t235, &lam_fun_t234, 2, B_v157791, env[0]);
  return lam_clo_t235;
}

tll_ptr lam_fun_t238(tll_ptr A_v157787, tll_env env) {
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, A_v157787);
  return lam_clo_t237;
}

tll_ptr lenUU_i79(tll_ptr A_v157797, tll_ptr xs_v157798) {
  tll_ptr add_ret_t245; tll_ptr call_ret_t243; tll_ptr consUU_t246;
  tll_ptr n_v157801; tll_ptr nilUU_t241; tll_ptr pair_struct_t242;
  tll_ptr pair_struct_t247; tll_ptr switch_ret_t240; tll_ptr switch_ret_t244;
  tll_ptr x_v157799; tll_ptr xs_v157800; tll_ptr xs_v157802;
  switch(((tll_node)xs_v157798)->tag) {
    case 27:
      instr_struct(&nilUU_t241, 27, 0);
      instr_struct(&pair_struct_t242, 0, 2, (tll_ptr)0, nilUU_t241);
      switch_ret_t240 = pair_struct_t242;
      break;
    case 28:
      x_v157799 = ((tll_node)xs_v157798)->data[0];
      xs_v157800 = ((tll_node)xs_v157798)->data[1];
      call_ret_t243 = lenUU_i79(0, xs_v157800);
      switch(((tll_node)call_ret_t243)->tag) {
        case 0:
          n_v157801 = ((tll_node)call_ret_t243)->data[0];
          xs_v157802 = ((tll_node)call_ret_t243)->data[1];
          instr_free_struct(call_ret_t243);
          add_ret_t245 = n_v157801 + 1;
          instr_struct(&consUU_t246, 28, 2, x_v157799, xs_v157802);
          instr_struct(&pair_struct_t247, 0, 2, add_ret_t245, consUU_t246);
          switch_ret_t244 = pair_struct_t247;
          break;
      }
      switch_ret_t240 = switch_ret_t244;
      break;
  }
  return switch_ret_t240;
}

tll_ptr lam_fun_t249(tll_ptr xs_v157805, tll_env env) {
  tll_ptr call_ret_t248;
  call_ret_t248 = lenUU_i79(env[0], xs_v157805);
  return call_ret_t248;
}

tll_ptr lam_fun_t251(tll_ptr A_v157803, tll_env env) {
  tll_ptr lam_clo_t250;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 1, A_v157803);
  return lam_clo_t250;
}

tll_ptr lenUL_i78(tll_ptr A_v157806, tll_ptr xs_v157807) {
  tll_ptr add_ret_t258; tll_ptr call_ret_t256; tll_ptr consUL_t259;
  tll_ptr n_v157810; tll_ptr nilUL_t254; tll_ptr pair_struct_t255;
  tll_ptr pair_struct_t260; tll_ptr switch_ret_t253; tll_ptr switch_ret_t257;
  tll_ptr x_v157808; tll_ptr xs_v157809; tll_ptr xs_v157811;
  switch(((tll_node)xs_v157807)->tag) {
    case 25:
      instr_free_struct(xs_v157807);
      instr_struct(&nilUL_t254, 25, 0);
      instr_struct(&pair_struct_t255, 0, 2, (tll_ptr)0, nilUL_t254);
      switch_ret_t253 = pair_struct_t255;
      break;
    case 26:
      x_v157808 = ((tll_node)xs_v157807)->data[0];
      xs_v157809 = ((tll_node)xs_v157807)->data[1];
      instr_free_struct(xs_v157807);
      call_ret_t256 = lenUL_i78(0, xs_v157809);
      switch(((tll_node)call_ret_t256)->tag) {
        case 0:
          n_v157810 = ((tll_node)call_ret_t256)->data[0];
          xs_v157811 = ((tll_node)call_ret_t256)->data[1];
          instr_free_struct(call_ret_t256);
          add_ret_t258 = n_v157810 + 1;
          instr_struct(&consUL_t259, 26, 2, x_v157808, xs_v157811);
          instr_struct(&pair_struct_t260, 0, 2, add_ret_t258, consUL_t259);
          switch_ret_t257 = pair_struct_t260;
          break;
      }
      switch_ret_t253 = switch_ret_t257;
      break;
  }
  return switch_ret_t253;
}

tll_ptr lam_fun_t262(tll_ptr xs_v157814, tll_env env) {
  tll_ptr call_ret_t261;
  call_ret_t261 = lenUL_i78(env[0], xs_v157814);
  return call_ret_t261;
}

tll_ptr lam_fun_t264(tll_ptr A_v157812, tll_env env) {
  tll_ptr lam_clo_t263;
  instr_clo(&lam_clo_t263, &lam_fun_t262, 1, A_v157812);
  return lam_clo_t263;
}

tll_ptr lenLL_i76(tll_ptr A_v157815, tll_ptr xs_v157816) {
  tll_ptr add_ret_t271; tll_ptr call_ret_t269; tll_ptr consLL_t272;
  tll_ptr n_v157819; tll_ptr nilLL_t267; tll_ptr pair_struct_t268;
  tll_ptr pair_struct_t273; tll_ptr switch_ret_t266; tll_ptr switch_ret_t270;
  tll_ptr x_v157817; tll_ptr xs_v157818; tll_ptr xs_v157820;
  switch(((tll_node)xs_v157816)->tag) {
    case 21:
      instr_free_struct(xs_v157816);
      instr_struct(&nilLL_t267, 21, 0);
      instr_struct(&pair_struct_t268, 0, 2, (tll_ptr)0, nilLL_t267);
      switch_ret_t266 = pair_struct_t268;
      break;
    case 22:
      x_v157817 = ((tll_node)xs_v157816)->data[0];
      xs_v157818 = ((tll_node)xs_v157816)->data[1];
      instr_free_struct(xs_v157816);
      call_ret_t269 = lenLL_i76(0, xs_v157818);
      switch(((tll_node)call_ret_t269)->tag) {
        case 0:
          n_v157819 = ((tll_node)call_ret_t269)->data[0];
          xs_v157820 = ((tll_node)call_ret_t269)->data[1];
          instr_free_struct(call_ret_t269);
          add_ret_t271 = n_v157819 + 1;
          instr_struct(&consLL_t272, 22, 2, x_v157817, xs_v157820);
          instr_struct(&pair_struct_t273, 0, 2, add_ret_t271, consLL_t272);
          switch_ret_t270 = pair_struct_t273;
          break;
      }
      switch_ret_t266 = switch_ret_t270;
      break;
  }
  return switch_ret_t266;
}

tll_ptr lam_fun_t275(tll_ptr xs_v157823, tll_env env) {
  tll_ptr call_ret_t274;
  call_ret_t274 = lenLL_i76(env[0], xs_v157823);
  return call_ret_t274;
}

tll_ptr lam_fun_t277(tll_ptr A_v157821, tll_env env) {
  tll_ptr lam_clo_t276;
  instr_clo(&lam_clo_t276, &lam_fun_t275, 1, A_v157821);
  return lam_clo_t276;
}

tll_ptr appendUU_i83(tll_ptr A_v157824, tll_ptr xs_v157825, tll_ptr ys_v157826) {
  tll_ptr call_ret_t280; tll_ptr consUU_t281; tll_ptr switch_ret_t279;
  tll_ptr x_v157827; tll_ptr xs_v157828;
  switch(((tll_node)xs_v157825)->tag) {
    case 27:
      switch_ret_t279 = ys_v157826;
      break;
    case 28:
      x_v157827 = ((tll_node)xs_v157825)->data[0];
      xs_v157828 = ((tll_node)xs_v157825)->data[1];
      call_ret_t280 = appendUU_i83(0, xs_v157828, ys_v157826);
      instr_struct(&consUU_t281, 28, 2, x_v157827, call_ret_t280);
      switch_ret_t279 = consUU_t281;
      break;
  }
  return switch_ret_t279;
}

tll_ptr lam_fun_t283(tll_ptr ys_v157834, tll_env env) {
  tll_ptr call_ret_t282;
  call_ret_t282 = appendUU_i83(env[1], env[0], ys_v157834);
  return call_ret_t282;
}

tll_ptr lam_fun_t285(tll_ptr xs_v157832, tll_env env) {
  tll_ptr lam_clo_t284;
  instr_clo(&lam_clo_t284, &lam_fun_t283, 2, xs_v157832, env[0]);
  return lam_clo_t284;
}

tll_ptr lam_fun_t287(tll_ptr A_v157829, tll_env env) {
  tll_ptr lam_clo_t286;
  instr_clo(&lam_clo_t286, &lam_fun_t285, 1, A_v157829);
  return lam_clo_t286;
}

tll_ptr appendUL_i82(tll_ptr A_v157835, tll_ptr xs_v157836, tll_ptr ys_v157837) {
  tll_ptr call_ret_t290; tll_ptr consUL_t291; tll_ptr switch_ret_t289;
  tll_ptr x_v157838; tll_ptr xs_v157839;
  switch(((tll_node)xs_v157836)->tag) {
    case 25:
      instr_free_struct(xs_v157836);
      switch_ret_t289 = ys_v157837;
      break;
    case 26:
      x_v157838 = ((tll_node)xs_v157836)->data[0];
      xs_v157839 = ((tll_node)xs_v157836)->data[1];
      instr_free_struct(xs_v157836);
      call_ret_t290 = appendUL_i82(0, xs_v157839, ys_v157837);
      instr_struct(&consUL_t291, 26, 2, x_v157838, call_ret_t290);
      switch_ret_t289 = consUL_t291;
      break;
  }
  return switch_ret_t289;
}

tll_ptr lam_fun_t293(tll_ptr ys_v157845, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = appendUL_i82(env[1], env[0], ys_v157845);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v157843, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 2, xs_v157843, env[0]);
  return lam_clo_t294;
}

tll_ptr lam_fun_t297(tll_ptr A_v157840, tll_env env) {
  tll_ptr lam_clo_t296;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 1, A_v157840);
  return lam_clo_t296;
}

tll_ptr appendLL_i80(tll_ptr A_v157846, tll_ptr xs_v157847, tll_ptr ys_v157848) {
  tll_ptr call_ret_t300; tll_ptr consLL_t301; tll_ptr switch_ret_t299;
  tll_ptr x_v157849; tll_ptr xs_v157850;
  switch(((tll_node)xs_v157847)->tag) {
    case 21:
      instr_free_struct(xs_v157847);
      switch_ret_t299 = ys_v157848;
      break;
    case 22:
      x_v157849 = ((tll_node)xs_v157847)->data[0];
      xs_v157850 = ((tll_node)xs_v157847)->data[1];
      instr_free_struct(xs_v157847);
      call_ret_t300 = appendLL_i80(0, xs_v157850, ys_v157848);
      instr_struct(&consLL_t301, 22, 2, x_v157849, call_ret_t300);
      switch_ret_t299 = consLL_t301;
      break;
  }
  return switch_ret_t299;
}

tll_ptr lam_fun_t303(tll_ptr ys_v157856, tll_env env) {
  tll_ptr call_ret_t302;
  call_ret_t302 = appendLL_i80(env[1], env[0], ys_v157856);
  return call_ret_t302;
}

tll_ptr lam_fun_t305(tll_ptr xs_v157854, tll_env env) {
  tll_ptr lam_clo_t304;
  instr_clo(&lam_clo_t304, &lam_fun_t303, 2, xs_v157854, env[0]);
  return lam_clo_t304;
}

tll_ptr lam_fun_t307(tll_ptr A_v157851, tll_env env) {
  tll_ptr lam_clo_t306;
  instr_clo(&lam_clo_t306, &lam_fun_t305, 1, A_v157851);
  return lam_clo_t306;
}

tll_ptr lam_fun_t314(tll_ptr __v157858, tll_env env) {
  tll_ptr __v157867; tll_ptr ch_v157865; tll_ptr ch_v157866;
  tll_ptr ch_v157869; tll_ptr ch_v157870; tll_ptr prim_ch_t309;
  tll_ptr recv_msg_t311; tll_ptr s_v157868; tll_ptr send_ch_t310;
  tll_ptr send_ch_t313; tll_ptr switch_ret_t312;
  instr_open(&prim_ch_t309, &proc_stdin);
  ch_v157865 = prim_ch_t309;
  instr_send(&send_ch_t310, ch_v157865, (tll_ptr)1);
  ch_v157866 = send_ch_t310;
  instr_recv(&recv_msg_t311, ch_v157866);
  __v157867 = recv_msg_t311;
  switch(((tll_node)__v157867)->tag) {
    case 0:
      s_v157868 = ((tll_node)__v157867)->data[0];
      ch_v157869 = ((tll_node)__v157867)->data[1];
      instr_free_struct(__v157867);
      instr_send(&send_ch_t313, ch_v157869, (tll_ptr)0);
      ch_v157870 = send_ch_t313;
      switch_ret_t312 = s_v157868;
      break;
  }
  return switch_ret_t312;
}

tll_ptr readline_i33(tll_ptr __v157857) {
  tll_ptr lam_clo_t315;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 0);
  return lam_clo_t315;
}

tll_ptr lam_fun_t317(tll_ptr __v157871, tll_env env) {
  tll_ptr call_ret_t316;
  call_ret_t316 = readline_i33(__v157871);
  return call_ret_t316;
}

tll_ptr lam_fun_t323(tll_ptr __v157873, tll_env env) {
  tll_ptr ch_v157878; tll_ptr ch_v157879; tll_ptr ch_v157880;
  tll_ptr ch_v157881; tll_ptr prim_ch_t319; tll_ptr send_ch_t320;
  tll_ptr send_ch_t321; tll_ptr send_ch_t322;
  instr_open(&prim_ch_t319, &proc_stdout);
  ch_v157878 = prim_ch_t319;
  instr_send(&send_ch_t320, ch_v157878, (tll_ptr)1);
  ch_v157879 = send_ch_t320;
  instr_send(&send_ch_t321, ch_v157879, env[0]);
  ch_v157880 = send_ch_t321;
  instr_send(&send_ch_t322, ch_v157880, (tll_ptr)0);
  ch_v157881 = send_ch_t322;
  return 0;
}

tll_ptr print_i34(tll_ptr s_v157872) {
  tll_ptr lam_clo_t324;
  instr_clo(&lam_clo_t324, &lam_fun_t323, 1, s_v157872);
  return lam_clo_t324;
}

tll_ptr lam_fun_t326(tll_ptr s_v157882, tll_env env) {
  tll_ptr call_ret_t325;
  call_ret_t325 = print_i34(s_v157882);
  return call_ret_t325;
}

tll_ptr lam_fun_t332(tll_ptr __v157884, tll_env env) {
  tll_ptr ch_v157889; tll_ptr ch_v157890; tll_ptr ch_v157891;
  tll_ptr ch_v157892; tll_ptr prim_ch_t328; tll_ptr send_ch_t329;
  tll_ptr send_ch_t330; tll_ptr send_ch_t331;
  instr_open(&prim_ch_t328, &proc_stderr);
  ch_v157889 = prim_ch_t328;
  instr_send(&send_ch_t329, ch_v157889, (tll_ptr)1);
  ch_v157890 = send_ch_t329;
  instr_send(&send_ch_t330, ch_v157890, env[0]);
  ch_v157891 = send_ch_t330;
  instr_send(&send_ch_t331, ch_v157891, (tll_ptr)0);
  ch_v157892 = send_ch_t331;
  return 0;
}

tll_ptr prerr_i35(tll_ptr s_v157883) {
  tll_ptr lam_clo_t333;
  instr_clo(&lam_clo_t333, &lam_fun_t332, 1, s_v157883);
  return lam_clo_t333;
}

tll_ptr lam_fun_t335(tll_ptr s_v157893, tll_env env) {
  tll_ptr call_ret_t334;
  call_ret_t334 = prerr_i35(s_v157893);
  return call_ret_t334;
}

tll_ptr get_at_i37(tll_ptr A_v157894, tll_ptr n_v157895, tll_ptr xs_v157896, tll_ptr a_v157897) {
  tll_ptr __v157898; tll_ptr __v157901; tll_ptr add_ret_t380;
  tll_ptr call_ret_t379; tll_ptr ifte_ret_t382; tll_ptr switch_ret_t378;
  tll_ptr switch_ret_t381; tll_ptr x_v157900; tll_ptr xs_v157899;
  if (n_v157895) {
    switch(((tll_node)xs_v157896)->tag) {
      case 27:
        switch_ret_t378 = a_v157897;
        break;
      case 28:
        __v157898 = ((tll_node)xs_v157896)->data[0];
        xs_v157899 = ((tll_node)xs_v157896)->data[1];
        add_ret_t380 = n_v157895 - 1;
        call_ret_t379 = get_at_i37(0, add_ret_t380, xs_v157899, a_v157897);
        switch_ret_t378 = call_ret_t379;
        break;
    }
    ifte_ret_t382 = switch_ret_t378;
  }
  else {
    switch(((tll_node)xs_v157896)->tag) {
      case 27:
        switch_ret_t381 = a_v157897;
        break;
      case 28:
        x_v157900 = ((tll_node)xs_v157896)->data[0];
        __v157901 = ((tll_node)xs_v157896)->data[1];
        switch_ret_t381 = x_v157900;
        break;
    }
    ifte_ret_t382 = switch_ret_t381;
  }
  return ifte_ret_t382;
}

tll_ptr lam_fun_t384(tll_ptr a_v157911, tll_env env) {
  tll_ptr call_ret_t383;
  call_ret_t383 = get_at_i37(env[2], env[1], env[0], a_v157911);
  return call_ret_t383;
}

tll_ptr lam_fun_t386(tll_ptr xs_v157909, tll_env env) {
  tll_ptr lam_clo_t385;
  instr_clo(&lam_clo_t385, &lam_fun_t384, 3, xs_v157909, env[0], env[1]);
  return lam_clo_t385;
}

tll_ptr lam_fun_t388(tll_ptr n_v157906, tll_env env) {
  tll_ptr lam_clo_t387;
  instr_clo(&lam_clo_t387, &lam_fun_t386, 2, n_v157906, env[0]);
  return lam_clo_t387;
}

tll_ptr lam_fun_t390(tll_ptr A_v157902, tll_env env) {
  tll_ptr lam_clo_t389;
  instr_clo(&lam_clo_t389, &lam_fun_t388, 1, A_v157902);
  return lam_clo_t389;
}

tll_ptr string_of_digit_i38(tll_ptr n_v157912) {
  tll_ptr EmptyString_t393; tll_ptr call_ret_t392;
  instr_struct(&EmptyString_t393, 6, 0);
  call_ret_t392 = get_at_i37(0, n_v157912, digits_i36, EmptyString_t393);
  return call_ret_t392;
}

tll_ptr lam_fun_t395(tll_ptr n_v157913, tll_env env) {
  tll_ptr call_ret_t394;
  call_ret_t394 = string_of_digit_i38(n_v157913);
  return call_ret_t394;
}

tll_ptr string_of_nat_i39(tll_ptr n_v157914) {
  tll_ptr call_ret_t397; tll_ptr call_ret_t398; tll_ptr call_ret_t399;
  tll_ptr call_ret_t400; tll_ptr call_ret_t401; tll_ptr call_ret_t402;
  tll_ptr ifte_ret_t403; tll_ptr n_v157916; tll_ptr s_v157915;
  call_ret_t398 = modn_i17(n_v157914, (tll_ptr)10);
  call_ret_t397 = string_of_digit_i38(call_ret_t398);
  s_v157915 = call_ret_t397;
  call_ret_t399 = divn_i16(n_v157914, (tll_ptr)10);
  n_v157916 = call_ret_t399;
  call_ret_t400 = ltn_i8((tll_ptr)0, n_v157916);
  if (call_ret_t400) {
    call_ret_t402 = string_of_nat_i39(n_v157916);
    call_ret_t401 = cats_i20(call_ret_t402, s_v157915);
    ifte_ret_t403 = call_ret_t401;
  }
  else {
    ifte_ret_t403 = s_v157915;
  }
  return ifte_ret_t403;
}

tll_ptr lam_fun_t405(tll_ptr n_v157917, tll_env env) {
  tll_ptr call_ret_t404;
  call_ret_t404 = string_of_nat_i39(n_v157917);
  return call_ret_t404;
}

tll_ptr digit_of_char_i40(tll_ptr c_v157918) {
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
  call_ret_t407 = eqc_i18(c_v157918, Char_t408);
  if (call_ret_t407) {
    instr_struct(&SomeUL_t409, 18, 1, (tll_ptr)0);
    ifte_ret_t447 = SomeUL_t409;
  }
  else {
    instr_struct(&Char_t411, 5, 1, (tll_ptr)49);
    call_ret_t410 = eqc_i18(c_v157918, Char_t411);
    if (call_ret_t410) {
      instr_struct(&SomeUL_t412, 18, 1, (tll_ptr)1);
      ifte_ret_t446 = SomeUL_t412;
    }
    else {
      instr_struct(&Char_t414, 5, 1, (tll_ptr)50);
      call_ret_t413 = eqc_i18(c_v157918, Char_t414);
      if (call_ret_t413) {
        instr_struct(&SomeUL_t415, 18, 1, (tll_ptr)2);
        ifte_ret_t445 = SomeUL_t415;
      }
      else {
        instr_struct(&Char_t417, 5, 1, (tll_ptr)51);
        call_ret_t416 = eqc_i18(c_v157918, Char_t417);
        if (call_ret_t416) {
          instr_struct(&SomeUL_t418, 18, 1, (tll_ptr)3);
          ifte_ret_t444 = SomeUL_t418;
        }
        else {
          instr_struct(&Char_t420, 5, 1, (tll_ptr)52);
          call_ret_t419 = eqc_i18(c_v157918, Char_t420);
          if (call_ret_t419) {
            instr_struct(&SomeUL_t421, 18, 1, (tll_ptr)4);
            ifte_ret_t443 = SomeUL_t421;
          }
          else {
            instr_struct(&Char_t423, 5, 1, (tll_ptr)53);
            call_ret_t422 = eqc_i18(c_v157918, Char_t423);
            if (call_ret_t422) {
              instr_struct(&SomeUL_t424, 18, 1, (tll_ptr)5);
              ifte_ret_t442 = SomeUL_t424;
            }
            else {
              instr_struct(&Char_t426, 5, 1, (tll_ptr)54);
              call_ret_t425 = eqc_i18(c_v157918, Char_t426);
              if (call_ret_t425) {
                instr_struct(&SomeUL_t427, 18, 1, (tll_ptr)6);
                ifte_ret_t441 = SomeUL_t427;
              }
              else {
                instr_struct(&Char_t429, 5, 1, (tll_ptr)55);
                call_ret_t428 = eqc_i18(c_v157918, Char_t429);
                if (call_ret_t428) {
                  instr_struct(&SomeUL_t430, 18, 1, (tll_ptr)7);
                  ifte_ret_t440 = SomeUL_t430;
                }
                else {
                  instr_struct(&Char_t432, 5, 1, (tll_ptr)56);
                  call_ret_t431 = eqc_i18(c_v157918, Char_t432);
                  if (call_ret_t431) {
                    instr_struct(&SomeUL_t433, 18, 1, (tll_ptr)8);
                    ifte_ret_t439 = SomeUL_t433;
                  }
                  else {
                    instr_struct(&Char_t435, 5, 1, (tll_ptr)57);
                    call_ret_t434 = eqc_i18(c_v157918, Char_t435);
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

tll_ptr lam_fun_t449(tll_ptr c_v157919, tll_env env) {
  tll_ptr call_ret_t448;
  call_ret_t448 = digit_of_char_i40(c_v157919);
  return call_ret_t448;
}

tll_ptr nat_of_string_loop_i41(tll_ptr s_v157920, tll_ptr acc_v157921) {
  tll_ptr NoneUL_t455; tll_ptr SomeUL_t452; tll_ptr c_v157922;
  tll_ptr call_ret_t453; tll_ptr call_ret_t456; tll_ptr call_ret_t457;
  tll_ptr call_ret_t458; tll_ptr n_v157924; tll_ptr s_v157923;
  tll_ptr switch_ret_t451; tll_ptr switch_ret_t454;
  switch(((tll_node)s_v157920)->tag) {
    case 6:
      instr_struct(&SomeUL_t452, 18, 1, acc_v157921);
      switch_ret_t451 = SomeUL_t452;
      break;
    case 7:
      c_v157922 = ((tll_node)s_v157920)->data[0];
      s_v157923 = ((tll_node)s_v157920)->data[1];
      call_ret_t453 = digit_of_char_i40(c_v157922);
      switch(((tll_node)call_ret_t453)->tag) {
        case 17:
          instr_free_struct(call_ret_t453);
          instr_struct(&NoneUL_t455, 17, 0);
          switch_ret_t454 = NoneUL_t455;
          break;
        case 18:
          n_v157924 = ((tll_node)call_ret_t453)->data[0];
          instr_free_struct(call_ret_t453);
          call_ret_t458 = muln_i15(acc_v157921, (tll_ptr)10);
          call_ret_t457 = addn_i13(call_ret_t458, n_v157924);
          call_ret_t456 = nat_of_string_loop_i41(s_v157923, call_ret_t457);
          switch_ret_t454 = call_ret_t456;
          break;
      }
      switch_ret_t451 = switch_ret_t454;
      break;
  }
  return switch_ret_t451;
}

tll_ptr lam_fun_t460(tll_ptr acc_v157927, tll_env env) {
  tll_ptr call_ret_t459;
  call_ret_t459 = nat_of_string_loop_i41(env[0], acc_v157927);
  return call_ret_t459;
}

tll_ptr lam_fun_t462(tll_ptr s_v157925, tll_env env) {
  tll_ptr lam_clo_t461;
  instr_clo(&lam_clo_t461, &lam_fun_t460, 1, s_v157925);
  return lam_clo_t461;
}

tll_ptr nat_of_string_i42(tll_ptr s_v157928) {
  tll_ptr call_ret_t464;
  call_ret_t464 = nat_of_string_loop_i41(s_v157928, (tll_ptr)0);
  return call_ret_t464;
}

tll_ptr lam_fun_t466(tll_ptr s_v157929, tll_env env) {
  tll_ptr call_ret_t465;
  call_ret_t465 = nat_of_string_i42(s_v157929);
  return call_ret_t465;
}

tll_ptr contains_i49(tll_ptr c_v157930, tll_ptr s_v157931) {
  tll_ptr c0_v157932; tll_ptr call_ret_t469; tll_ptr call_ret_t470;
  tll_ptr ifte_ret_t471; tll_ptr s_v157933; tll_ptr switch_ret_t468;
  switch(((tll_node)s_v157931)->tag) {
    case 6:
      switch_ret_t468 = (tll_ptr)0;
      break;
    case 7:
      c0_v157932 = ((tll_node)s_v157931)->data[0];
      s_v157933 = ((tll_node)s_v157931)->data[1];
      call_ret_t469 = eqc_i18(c_v157930, c0_v157932);
      if (call_ret_t469) {
        ifte_ret_t471 = (tll_ptr)1;
      }
      else {
        call_ret_t470 = contains_i49(c_v157930, s_v157933);
        ifte_ret_t471 = call_ret_t470;
      }
      switch_ret_t468 = ifte_ret_t471;
      break;
  }
  return switch_ret_t468;
}

tll_ptr lam_fun_t473(tll_ptr s_v157936, tll_env env) {
  tll_ptr call_ret_t472;
  call_ret_t472 = contains_i49(env[0], s_v157936);
  return call_ret_t472;
}

tll_ptr lam_fun_t475(tll_ptr c_v157934, tll_env env) {
  tll_ptr lam_clo_t474;
  instr_clo(&lam_clo_t474, &lam_fun_t473, 1, c_v157934);
  return lam_clo_t474;
}

tll_ptr string_diff_i50(tll_ptr ans_v157937, tll_ptr s1_v157938, tll_ptr s2_v157939) {
  tll_ptr Char_t483; tll_ptr Char_t489; tll_ptr Char_t494;
  tll_ptr EmptyString_t478; tll_ptr EmptyString_t480;
  tll_ptr EmptyString_t484; tll_ptr EmptyString_t490;
  tll_ptr EmptyString_t495; tll_ptr String_t485; tll_ptr String_t491;
  tll_ptr String_t496; tll_ptr c1_v157940; tll_ptr c2_v157942;
  tll_ptr call_ret_t481; tll_ptr call_ret_t482; tll_ptr call_ret_t486;
  tll_ptr call_ret_t487; tll_ptr call_ret_t488; tll_ptr call_ret_t492;
  tll_ptr call_ret_t493; tll_ptr call_ret_t497; tll_ptr ifte_ret_t498;
  tll_ptr ifte_ret_t499; tll_ptr s1_v157941; tll_ptr s2_v157943;
  tll_ptr switch_ret_t477; tll_ptr switch_ret_t479;
  switch(((tll_node)s1_v157938)->tag) {
    case 6:
      instr_struct(&EmptyString_t478, 6, 0);
      switch_ret_t477 = EmptyString_t478;
      break;
    case 7:
      c1_v157940 = ((tll_node)s1_v157938)->data[0];
      s1_v157941 = ((tll_node)s1_v157938)->data[1];
      switch(((tll_node)s2_v157939)->tag) {
        case 6:
          instr_struct(&EmptyString_t480, 6, 0);
          switch_ret_t479 = EmptyString_t480;
          break;
        case 7:
          c2_v157942 = ((tll_node)s2_v157939)->data[0];
          s2_v157943 = ((tll_node)s2_v157939)->data[1];
          call_ret_t481 = eqc_i18(c1_v157940, c2_v157942);
          if (call_ret_t481) {
            instr_struct(&Char_t483, 5, 1, (tll_ptr)89);
            instr_struct(&EmptyString_t484, 6, 0);
            instr_struct(&String_t485, 7, 2, Char_t483, EmptyString_t484);
            call_ret_t486 = string_diff_i50(ans_v157937, s1_v157941,
                                            s2_v157943);
            call_ret_t482 = cats_i20(String_t485, call_ret_t486);
            ifte_ret_t499 = call_ret_t482;
          }
          else {
            call_ret_t487 = contains_i49(c2_v157942, ans_v157937);
            if (call_ret_t487) {
              instr_struct(&Char_t489, 5, 1, (tll_ptr)73);
              instr_struct(&EmptyString_t490, 6, 0);
              instr_struct(&String_t491, 7, 2, Char_t489, EmptyString_t490);
              call_ret_t492 = string_diff_i50(ans_v157937, s1_v157941,
                                              s2_v157943);
              call_ret_t488 = cats_i20(String_t491, call_ret_t492);
              ifte_ret_t498 = call_ret_t488;
            }
            else {
              instr_struct(&Char_t494, 5, 1, (tll_ptr)78);
              instr_struct(&EmptyString_t495, 6, 0);
              instr_struct(&String_t496, 7, 2, Char_t494, EmptyString_t495);
              call_ret_t497 = string_diff_i50(ans_v157937, s1_v157941,
                                              s2_v157943);
              call_ret_t493 = cats_i20(String_t496, call_ret_t497);
              ifte_ret_t498 = call_ret_t493;
            }
            ifte_ret_t499 = ifte_ret_t498;
          }
          switch_ret_t479 = ifte_ret_t499;
          break;
      }
      switch_ret_t477 = switch_ret_t479;
      break;
  }
  return switch_ret_t477;
}

tll_ptr lam_fun_t501(tll_ptr s2_v157949, tll_env env) {
  tll_ptr call_ret_t500;
  call_ret_t500 = string_diff_i50(env[1], env[0], s2_v157949);
  return call_ret_t500;
}

tll_ptr lam_fun_t503(tll_ptr s1_v157947, tll_env env) {
  tll_ptr lam_clo_t502;
  instr_clo(&lam_clo_t502, &lam_fun_t501, 2, s1_v157947, env[0]);
  return lam_clo_t502;
}

tll_ptr lam_fun_t505(tll_ptr ans_v157944, tll_env env) {
  tll_ptr lam_clo_t504;
  instr_clo(&lam_clo_t504, &lam_fun_t503, 1, ans_v157944);
  return lam_clo_t504;
}

tll_ptr wordle_diff_i52(tll_ptr ans_v157950, tll_ptr guess_v157951) {
  tll_ptr Word_t510; tll_ptr ans_v157952; tll_ptr call_ret_t509;
  tll_ptr guess_v157954; tll_ptr pf1_v157953; tll_ptr pf2_v157955;
  tll_ptr switch_ret_t507; tll_ptr switch_ret_t508;
  switch(((tll_node)ans_v157950)->tag) {
    case 12:
      ans_v157952 = ((tll_node)ans_v157950)->data[0];
      pf1_v157953 = ((tll_node)ans_v157950)->data[1];
      switch(((tll_node)guess_v157951)->tag) {
        case 12:
          guess_v157954 = ((tll_node)guess_v157951)->data[0];
          pf2_v157955 = ((tll_node)guess_v157951)->data[1];
          call_ret_t509 = string_diff_i50(ans_v157952, ans_v157952,
                                          guess_v157954);
          instr_struct(&Word_t510, 12, 2, call_ret_t509, 0);
          switch_ret_t508 = Word_t510;
          break;
      }
      switch_ret_t507 = switch_ret_t508;
      break;
  }
  return switch_ret_t507;
}

tll_ptr lam_fun_t512(tll_ptr guess_v157958, tll_env env) {
  tll_ptr call_ret_t511;
  call_ret_t511 = wordle_diff_i52(env[0], guess_v157958);
  return call_ret_t511;
}

tll_ptr lam_fun_t514(tll_ptr ans_v157956, tll_env env) {
  tll_ptr lam_clo_t513;
  instr_clo(&lam_clo_t513, &lam_fun_t512, 1, ans_v157956);
  return lam_clo_t513;
}

tll_ptr eqw_i53(tll_ptr w1_v157959, tll_ptr w2_v157960) {
  tll_ptr __v157962; tll_ptr __v157964; tll_ptr call_ret_t518;
  tll_ptr s1_v157961; tll_ptr s2_v157963; tll_ptr switch_ret_t516;
  tll_ptr switch_ret_t517;
  switch(((tll_node)w1_v157959)->tag) {
    case 12:
      s1_v157961 = ((tll_node)w1_v157959)->data[0];
      __v157962 = ((tll_node)w1_v157959)->data[1];
      switch(((tll_node)w2_v157960)->tag) {
        case 12:
          s2_v157963 = ((tll_node)w2_v157960)->data[0];
          __v157964 = ((tll_node)w2_v157960)->data[1];
          call_ret_t518 = eqs_i22(s1_v157961, s2_v157963);
          switch_ret_t517 = call_ret_t518;
          break;
      }
      switch_ret_t516 = switch_ret_t517;
      break;
  }
  return switch_ret_t516;
}

tll_ptr lam_fun_t520(tll_ptr w2_v157967, tll_env env) {
  tll_ptr call_ret_t519;
  call_ret_t519 = eqw_i53(env[0], w2_v157967);
  return call_ret_t519;
}

tll_ptr lam_fun_t522(tll_ptr w1_v157965, tll_env env) {
  tll_ptr lam_clo_t521;
  instr_clo(&lam_clo_t521, &lam_fun_t520, 1, w1_v157965);
  return lam_clo_t521;
}

tll_ptr lam_fun_t529(tll_ptr __v157979, tll_env env) {
  tll_ptr Word_t528;
  instr_struct(&Word_t528, 12, 2, env[0], 0);
  return Word_t528;
}

tll_ptr lam_fun_t531(tll_ptr e_v157977, tll_env env) {
  tll_ptr lam_clo_t530;
  instr_clo(&lam_clo_t530, &lam_fun_t529, 1, env[0]);
  return lam_clo_t530;
}

tll_ptr lam_fun_t612(tll_ptr __v157983, tll_env env) {
  tll_ptr Char_t534; tll_ptr Char_t535; tll_ptr Char_t536; tll_ptr Char_t537;
  tll_ptr Char_t538; tll_ptr Char_t539; tll_ptr Char_t540; tll_ptr Char_t541;
  tll_ptr Char_t542; tll_ptr Char_t543; tll_ptr Char_t544; tll_ptr Char_t545;
  tll_ptr Char_t546; tll_ptr Char_t547; tll_ptr Char_t548; tll_ptr Char_t549;
  tll_ptr Char_t550; tll_ptr Char_t551; tll_ptr Char_t552; tll_ptr Char_t553;
  tll_ptr Char_t554; tll_ptr Char_t555; tll_ptr Char_t556; tll_ptr Char_t557;
  tll_ptr Char_t558; tll_ptr Char_t559; tll_ptr Char_t560; tll_ptr Char_t561;
  tll_ptr Char_t562; tll_ptr Char_t563; tll_ptr Char_t564; tll_ptr Char_t565;
  tll_ptr Char_t566; tll_ptr Char_t567; tll_ptr Char_t568; tll_ptr Char_t569;
  tll_ptr Char_t570; tll_ptr EmptyString_t571; tll_ptr String_t572;
  tll_ptr String_t573; tll_ptr String_t574; tll_ptr String_t575;
  tll_ptr String_t576; tll_ptr String_t577; tll_ptr String_t578;
  tll_ptr String_t579; tll_ptr String_t580; tll_ptr String_t581;
  tll_ptr String_t582; tll_ptr String_t583; tll_ptr String_t584;
  tll_ptr String_t585; tll_ptr String_t586; tll_ptr String_t587;
  tll_ptr String_t588; tll_ptr String_t589; tll_ptr String_t590;
  tll_ptr String_t591; tll_ptr String_t592; tll_ptr String_t593;
  tll_ptr String_t594; tll_ptr String_t595; tll_ptr String_t596;
  tll_ptr String_t597; tll_ptr String_t598; tll_ptr String_t599;
  tll_ptr String_t600; tll_ptr String_t601; tll_ptr String_t602;
  tll_ptr String_t603; tll_ptr String_t604; tll_ptr String_t605;
  tll_ptr String_t606; tll_ptr String_t607; tll_ptr String_t608;
  tll_ptr __v157985; tll_ptr app_ret_t609; tll_ptr app_ret_t611;
  tll_ptr call_ret_t533; tll_ptr call_ret_t610;
  instr_struct(&Char_t534, 5, 1, (tll_ptr)112);
  instr_struct(&Char_t535, 5, 1, (tll_ptr)108);
  instr_struct(&Char_t536, 5, 1, (tll_ptr)101);
  instr_struct(&Char_t537, 5, 1, (tll_ptr)97);
  instr_struct(&Char_t538, 5, 1, (tll_ptr)115);
  instr_struct(&Char_t539, 5, 1, (tll_ptr)101);
  instr_struct(&Char_t540, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t541, 5, 1, (tll_ptr)105);
  instr_struct(&Char_t542, 5, 1, (tll_ptr)110);
  instr_struct(&Char_t543, 5, 1, (tll_ptr)112);
  instr_struct(&Char_t544, 5, 1, (tll_ptr)117);
  instr_struct(&Char_t545, 5, 1, (tll_ptr)116);
  instr_struct(&Char_t546, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t547, 5, 1, (tll_ptr)97);
  instr_struct(&Char_t548, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t549, 5, 1, (tll_ptr)119);
  instr_struct(&Char_t550, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t551, 5, 1, (tll_ptr)114);
  instr_struct(&Char_t552, 5, 1, (tll_ptr)100);
  instr_struct(&Char_t553, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t554, 5, 1, (tll_ptr)119);
  instr_struct(&Char_t555, 5, 1, (tll_ptr)105);
  instr_struct(&Char_t556, 5, 1, (tll_ptr)116);
  instr_struct(&Char_t557, 5, 1, (tll_ptr)104);
  instr_struct(&Char_t558, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t559, 5, 1, (tll_ptr)108);
  instr_struct(&Char_t560, 5, 1, (tll_ptr)101);
  instr_struct(&Char_t561, 5, 1, (tll_ptr)110);
  instr_struct(&Char_t562, 5, 1, (tll_ptr)103);
  instr_struct(&Char_t563, 5, 1, (tll_ptr)116);
  instr_struct(&Char_t564, 5, 1, (tll_ptr)104);
  instr_struct(&Char_t565, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t566, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t567, 5, 1, (tll_ptr)102);
  instr_struct(&Char_t568, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t569, 5, 1, (tll_ptr)53);
  instr_struct(&Char_t570, 5, 1, (tll_ptr)10);
  instr_struct(&EmptyString_t571, 6, 0);
  instr_struct(&String_t572, 7, 2, Char_t570, EmptyString_t571);
  instr_struct(&String_t573, 7, 2, Char_t569, String_t572);
  instr_struct(&String_t574, 7, 2, Char_t568, String_t573);
  instr_struct(&String_t575, 7, 2, Char_t567, String_t574);
  instr_struct(&String_t576, 7, 2, Char_t566, String_t575);
  instr_struct(&String_t577, 7, 2, Char_t565, String_t576);
  instr_struct(&String_t578, 7, 2, Char_t564, String_t577);
  instr_struct(&String_t579, 7, 2, Char_t563, String_t578);
  instr_struct(&String_t580, 7, 2, Char_t562, String_t579);
  instr_struct(&String_t581, 7, 2, Char_t561, String_t580);
  instr_struct(&String_t582, 7, 2, Char_t560, String_t581);
  instr_struct(&String_t583, 7, 2, Char_t559, String_t582);
  instr_struct(&String_t584, 7, 2, Char_t558, String_t583);
  instr_struct(&String_t585, 7, 2, Char_t557, String_t584);
  instr_struct(&String_t586, 7, 2, Char_t556, String_t585);
  instr_struct(&String_t587, 7, 2, Char_t555, String_t586);
  instr_struct(&String_t588, 7, 2, Char_t554, String_t587);
  instr_struct(&String_t589, 7, 2, Char_t553, String_t588);
  instr_struct(&String_t590, 7, 2, Char_t552, String_t589);
  instr_struct(&String_t591, 7, 2, Char_t551, String_t590);
  instr_struct(&String_t592, 7, 2, Char_t550, String_t591);
  instr_struct(&String_t593, 7, 2, Char_t549, String_t592);
  instr_struct(&String_t594, 7, 2, Char_t548, String_t593);
  instr_struct(&String_t595, 7, 2, Char_t547, String_t594);
  instr_struct(&String_t596, 7, 2, Char_t546, String_t595);
  instr_struct(&String_t597, 7, 2, Char_t545, String_t596);
  instr_struct(&String_t598, 7, 2, Char_t544, String_t597);
  instr_struct(&String_t599, 7, 2, Char_t543, String_t598);
  instr_struct(&String_t600, 7, 2, Char_t542, String_t599);
  instr_struct(&String_t601, 7, 2, Char_t541, String_t600);
  instr_struct(&String_t602, 7, 2, Char_t540, String_t601);
  instr_struct(&String_t603, 7, 2, Char_t539, String_t602);
  instr_struct(&String_t604, 7, 2, Char_t538, String_t603);
  instr_struct(&String_t605, 7, 2, Char_t537, String_t604);
  instr_struct(&String_t606, 7, 2, Char_t536, String_t605);
  instr_struct(&String_t607, 7, 2, Char_t535, String_t606);
  instr_struct(&String_t608, 7, 2, Char_t534, String_t607);
  call_ret_t533 = print_i34(String_t608);
  instr_app(&app_ret_t609, call_ret_t533, 0);
  instr_free_clo(call_ret_t533);
  __v157985 = app_ret_t609;
  call_ret_t610 = read_word_i60(0);
  instr_app(&app_ret_t611, call_ret_t610, 0);
  instr_free_clo(call_ret_t610);
  return app_ret_t611;
}

tll_ptr lam_fun_t614(tll_ptr __v157980, tll_env env) {
  tll_ptr lam_clo_t613;
  instr_clo(&lam_clo_t613, &lam_fun_t612, 0);
  return lam_clo_t613;
}

tll_ptr lam_fun_t619(tll_ptr __v157969, tll_env env) {
  tll_ptr app_ret_t525; tll_ptr app_ret_t617; tll_ptr app_ret_t618;
  tll_ptr call_ret_t524; tll_ptr call_ret_t526; tll_ptr call_ret_t527;
  tll_ptr ifte_ret_t616; tll_ptr lam_clo_t532; tll_ptr lam_clo_t615;
  tll_ptr s_v157976;
  call_ret_t524 = readline_i33(0);
  instr_app(&app_ret_t525, call_ret_t524, 0);
  instr_free_clo(call_ret_t524);
  s_v157976 = app_ret_t525;
  call_ret_t527 = strlen_i21(s_v157976);
  call_ret_t526 = eqn_i10(call_ret_t527, (tll_ptr)5);
  if (call_ret_t526) {
    instr_clo(&lam_clo_t532, &lam_fun_t531, 1, s_v157976);
    ifte_ret_t616 = lam_clo_t532;
  }
  else {
    instr_clo(&lam_clo_t615, &lam_fun_t614, 0);
    ifte_ret_t616 = lam_clo_t615;
  }
  instr_app(&app_ret_t617, ifte_ret_t616, 0);
  instr_app(&app_ret_t618, app_ret_t617, 0);
  instr_free_clo(app_ret_t617);
  return app_ret_t618;
}

tll_ptr read_word_i60(tll_ptr __v157968) {
  tll_ptr lam_clo_t620;
  instr_clo(&lam_clo_t620, &lam_fun_t619, 0);
  return lam_clo_t620;
}

tll_ptr lam_fun_t622(tll_ptr __v157986, tll_env env) {
  tll_ptr call_ret_t621;
  call_ret_t621 = read_word_i60(__v157986);
  return call_ret_t621;
}

tll_ptr lam_fun_t653(tll_ptr __v158043, tll_env env) {
  tll_ptr Char_t632; tll_ptr Char_t633; tll_ptr Char_t634; tll_ptr Char_t635;
  tll_ptr Char_t636; tll_ptr Char_t637; tll_ptr Char_t638; tll_ptr Char_t639;
  tll_ptr Char_t640; tll_ptr EmptyString_t641; tll_ptr String_t642;
  tll_ptr String_t643; tll_ptr String_t644; tll_ptr String_t645;
  tll_ptr String_t646; tll_ptr String_t647; tll_ptr String_t648;
  tll_ptr String_t649; tll_ptr String_t650; tll_ptr __v158045;
  tll_ptr app_ret_t651; tll_ptr call_ret_t631; tll_ptr close_tmp_t652;
  instr_struct(&Char_t632, 5, 1, (tll_ptr)89);
  instr_struct(&Char_t633, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t634, 5, 1, (tll_ptr)117);
  instr_struct(&Char_t635, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t636, 5, 1, (tll_ptr)87);
  instr_struct(&Char_t637, 5, 1, (tll_ptr)105);
  instr_struct(&Char_t638, 5, 1, (tll_ptr)110);
  instr_struct(&Char_t639, 5, 1, (tll_ptr)33);
  instr_struct(&Char_t640, 5, 1, (tll_ptr)10);
  instr_struct(&EmptyString_t641, 6, 0);
  instr_struct(&String_t642, 7, 2, Char_t640, EmptyString_t641);
  instr_struct(&String_t643, 7, 2, Char_t639, String_t642);
  instr_struct(&String_t644, 7, 2, Char_t638, String_t643);
  instr_struct(&String_t645, 7, 2, Char_t637, String_t644);
  instr_struct(&String_t646, 7, 2, Char_t636, String_t645);
  instr_struct(&String_t647, 7, 2, Char_t635, String_t646);
  instr_struct(&String_t648, 7, 2, Char_t634, String_t647);
  instr_struct(&String_t649, 7, 2, Char_t633, String_t648);
  instr_struct(&String_t650, 7, 2, Char_t632, String_t649);
  call_ret_t631 = print_i34(String_t650);
  instr_app(&app_ret_t651, call_ret_t631, 0);
  instr_free_clo(call_ret_t631);
  __v158045 = app_ret_t651;
  instr_close(&close_tmp_t652, env[0]);
  return close_tmp_t652;
}

tll_ptr lam_fun_t655(tll_ptr c_v158040, tll_env env) {
  tll_ptr lam_clo_t654;
  instr_clo(&lam_clo_t654, &lam_fun_t653, 1, c_v158040);
  return lam_clo_t654;
}

tll_ptr lam_fun_t758(tll_ptr __v158056, tll_env env) {
  tll_ptr Char_t667; tll_ptr Char_t668; tll_ptr Char_t669; tll_ptr Char_t670;
  tll_ptr Char_t671; tll_ptr Char_t672; tll_ptr Char_t673; tll_ptr Char_t674;
  tll_ptr Char_t675; tll_ptr Char_t676; tll_ptr Char_t677; tll_ptr Char_t678;
  tll_ptr Char_t679; tll_ptr Char_t680; tll_ptr Char_t681; tll_ptr Char_t682;
  tll_ptr Char_t683; tll_ptr Char_t702; tll_ptr Char_t703; tll_ptr Char_t704;
  tll_ptr Char_t705; tll_ptr Char_t706; tll_ptr Char_t707; tll_ptr Char_t708;
  tll_ptr Char_t709; tll_ptr Char_t710; tll_ptr Char_t711; tll_ptr Char_t712;
  tll_ptr Char_t727; tll_ptr Char_t728; tll_ptr Char_t729; tll_ptr Char_t730;
  tll_ptr Char_t731; tll_ptr Char_t732; tll_ptr Char_t733; tll_ptr Char_t734;
  tll_ptr Char_t735; tll_ptr Char_t736; tll_ptr Char_t737; tll_ptr Char_t738;
  tll_ptr Char_t739; tll_ptr EmptyString_t684; tll_ptr EmptyString_t713;
  tll_ptr EmptyString_t740; tll_ptr String_t685; tll_ptr String_t686;
  tll_ptr String_t687; tll_ptr String_t688; tll_ptr String_t689;
  tll_ptr String_t690; tll_ptr String_t691; tll_ptr String_t692;
  tll_ptr String_t693; tll_ptr String_t694; tll_ptr String_t695;
  tll_ptr String_t696; tll_ptr String_t697; tll_ptr String_t698;
  tll_ptr String_t699; tll_ptr String_t700; tll_ptr String_t701;
  tll_ptr String_t714; tll_ptr String_t715; tll_ptr String_t716;
  tll_ptr String_t717; tll_ptr String_t718; tll_ptr String_t719;
  tll_ptr String_t720; tll_ptr String_t721; tll_ptr String_t722;
  tll_ptr String_t723; tll_ptr String_t724; tll_ptr String_t741;
  tll_ptr String_t742; tll_ptr String_t743; tll_ptr String_t744;
  tll_ptr String_t745; tll_ptr String_t746; tll_ptr String_t747;
  tll_ptr String_t748; tll_ptr String_t749; tll_ptr String_t750;
  tll_ptr String_t751; tll_ptr String_t752; tll_ptr String_t753;
  tll_ptr __v158065; tll_ptr __v158071; tll_ptr __v158072;
  tll_ptr add_ret_t726; tll_ptr add_ret_t756; tll_ptr app_ret_t754;
  tll_ptr app_ret_t757; tll_ptr c_v158067; tll_ptr c_v158069;
  tll_ptr call_ret_t662; tll_ptr call_ret_t663; tll_ptr call_ret_t664;
  tll_ptr call_ret_t665; tll_ptr call_ret_t666; tll_ptr call_ret_t725;
  tll_ptr call_ret_t755; tll_ptr diff_v158066; tll_ptr pair_struct_t659;
  tll_ptr pf_v158068; tll_ptr recv_msg_t657; tll_ptr s_v158070;
  tll_ptr switch_ret_t658; tll_ptr switch_ret_t660; tll_ptr switch_ret_t661;
  instr_recv(&recv_msg_t657, env[0]);
  __v158065 = recv_msg_t657;
  switch(((tll_node)__v158065)->tag) {
    case 0:
      diff_v158066 = ((tll_node)__v158065)->data[0];
      c_v158067 = ((tll_node)__v158065)->data[1];
      instr_free_struct(__v158065);
      instr_struct(&pair_struct_t659, 0, 2, 0, c_v158067);
      switch(((tll_node)pair_struct_t659)->tag) {
        case 0:
          pf_v158068 = ((tll_node)pair_struct_t659)->data[0];
          c_v158069 = ((tll_node)pair_struct_t659)->data[1];
          instr_free_struct(pair_struct_t659);
          switch(((tll_node)diff_v158066)->tag) {
            case 12:
              s_v158070 = ((tll_node)diff_v158066)->data[0];
              __v158071 = ((tll_node)diff_v158066)->data[1];
              instr_struct(&Char_t667, 5, 1, (tll_ptr)73);
              instr_struct(&Char_t668, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t669, 5, 1, (tll_ptr)99);
              instr_struct(&Char_t670, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t671, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t672, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t673, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t674, 5, 1, (tll_ptr)99);
              instr_struct(&Char_t675, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t676, 5, 1, (tll_ptr)44);
              instr_struct(&Char_t677, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t678, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t679, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t680, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t681, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t682, 5, 1, (tll_ptr)58);
              instr_struct(&Char_t683, 5, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t684, 6, 0);
              instr_struct(&String_t685, 7, 2, Char_t683, EmptyString_t684);
              instr_struct(&String_t686, 7, 2, Char_t682, String_t685);
              instr_struct(&String_t687, 7, 2, Char_t681, String_t686);
              instr_struct(&String_t688, 7, 2, Char_t680, String_t687);
              instr_struct(&String_t689, 7, 2, Char_t679, String_t688);
              instr_struct(&String_t690, 7, 2, Char_t678, String_t689);
              instr_struct(&String_t691, 7, 2, Char_t677, String_t690);
              instr_struct(&String_t692, 7, 2, Char_t676, String_t691);
              instr_struct(&String_t693, 7, 2, Char_t675, String_t692);
              instr_struct(&String_t694, 7, 2, Char_t674, String_t693);
              instr_struct(&String_t695, 7, 2, Char_t673, String_t694);
              instr_struct(&String_t696, 7, 2, Char_t672, String_t695);
              instr_struct(&String_t697, 7, 2, Char_t671, String_t696);
              instr_struct(&String_t698, 7, 2, Char_t670, String_t697);
              instr_struct(&String_t699, 7, 2, Char_t669, String_t698);
              instr_struct(&String_t700, 7, 2, Char_t668, String_t699);
              instr_struct(&String_t701, 7, 2, Char_t667, String_t700);
              call_ret_t666 = cats_i20(String_t701, s_v158070);
              instr_struct(&Char_t702, 5, 1, (tll_ptr)46);
              instr_struct(&Char_t703, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t704, 5, 1, (tll_ptr)89);
              instr_struct(&Char_t705, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t706, 5, 1, (tll_ptr)117);
              instr_struct(&Char_t707, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t708, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t709, 5, 1, (tll_ptr)97);
              instr_struct(&Char_t710, 5, 1, (tll_ptr)118);
              instr_struct(&Char_t711, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t712, 5, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t713, 6, 0);
              instr_struct(&String_t714, 7, 2, Char_t712, EmptyString_t713);
              instr_struct(&String_t715, 7, 2, Char_t711, String_t714);
              instr_struct(&String_t716, 7, 2, Char_t710, String_t715);
              instr_struct(&String_t717, 7, 2, Char_t709, String_t716);
              instr_struct(&String_t718, 7, 2, Char_t708, String_t717);
              instr_struct(&String_t719, 7, 2, Char_t707, String_t718);
              instr_struct(&String_t720, 7, 2, Char_t706, String_t719);
              instr_struct(&String_t721, 7, 2, Char_t705, String_t720);
              instr_struct(&String_t722, 7, 2, Char_t704, String_t721);
              instr_struct(&String_t723, 7, 2, Char_t703, String_t722);
              instr_struct(&String_t724, 7, 2, Char_t702, String_t723);
              call_ret_t665 = cats_i20(call_ret_t666, String_t724);
              add_ret_t726 = env[1] - 1;
              call_ret_t725 = string_of_nat_i39(add_ret_t726);
              call_ret_t664 = cats_i20(call_ret_t665, call_ret_t725);
              instr_struct(&Char_t727, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t728, 5, 1, (tll_ptr)109);
              instr_struct(&Char_t729, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t730, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t731, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t732, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t733, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t734, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t735, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t736, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t737, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t738, 5, 1, (tll_ptr)46);
              instr_struct(&Char_t739, 5, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t740, 6, 0);
              instr_struct(&String_t741, 7, 2, Char_t739, EmptyString_t740);
              instr_struct(&String_t742, 7, 2, Char_t738, String_t741);
              instr_struct(&String_t743, 7, 2, Char_t737, String_t742);
              instr_struct(&String_t744, 7, 2, Char_t736, String_t743);
              instr_struct(&String_t745, 7, 2, Char_t735, String_t744);
              instr_struct(&String_t746, 7, 2, Char_t734, String_t745);
              instr_struct(&String_t747, 7, 2, Char_t733, String_t746);
              instr_struct(&String_t748, 7, 2, Char_t732, String_t747);
              instr_struct(&String_t749, 7, 2, Char_t731, String_t748);
              instr_struct(&String_t750, 7, 2, Char_t730, String_t749);
              instr_struct(&String_t751, 7, 2, Char_t729, String_t750);
              instr_struct(&String_t752, 7, 2, Char_t728, String_t751);
              instr_struct(&String_t753, 7, 2, Char_t727, String_t752);
              call_ret_t663 = cats_i20(call_ret_t664, String_t753);
              call_ret_t662 = print_i34(call_ret_t663);
              instr_app(&app_ret_t754, call_ret_t662, 0);
              instr_free_clo(call_ret_t662);
              __v158072 = app_ret_t754;
              add_ret_t756 = env[1] - 1;
              call_ret_t755 = player_loop_i61(0, add_ret_t756, c_v158069);
              instr_app(&app_ret_t757, call_ret_t755, 0);
              instr_free_clo(call_ret_t755);
              switch_ret_t661 = app_ret_t757;
              break;
          }
          switch_ret_t660 = switch_ret_t661;
          break;
      }
      switch_ret_t658 = switch_ret_t660;
      break;
  }
  return switch_ret_t658;
}

tll_ptr lam_fun_t760(tll_ptr c_v158046, tll_env env) {
  tll_ptr lam_clo_t759;
  instr_clo(&lam_clo_t759, &lam_fun_t758, 2, c_v158046, env[0]);
  return lam_clo_t759;
}

tll_ptr lam_fun_t765(tll_ptr __v158012, tll_env env) {
  tll_ptr __v158035; tll_ptr app_ret_t625; tll_ptr app_ret_t763;
  tll_ptr app_ret_t764; tll_ptr b_v158036; tll_ptr c_v158034;
  tll_ptr c_v158037; tll_ptr c_v158039; tll_ptr call_ret_t624;
  tll_ptr guess_v158033; tll_ptr ifte_ret_t762; tll_ptr lam_clo_t656;
  tll_ptr lam_clo_t761; tll_ptr pair_struct_t629; tll_ptr pf_v158038;
  tll_ptr recv_msg_t627; tll_ptr send_ch_t626; tll_ptr switch_ret_t628;
  tll_ptr switch_ret_t630;
  call_ret_t624 = read_word_i60(0);
  instr_app(&app_ret_t625, call_ret_t624, 0);
  instr_free_clo(call_ret_t624);
  guess_v158033 = app_ret_t625;
  instr_send(&send_ch_t626, env[0], guess_v158033);
  c_v158034 = send_ch_t626;
  instr_recv(&recv_msg_t627, c_v158034);
  __v158035 = recv_msg_t627;
  switch(((tll_node)__v158035)->tag) {
    case 0:
      b_v158036 = ((tll_node)__v158035)->data[0];
      c_v158037 = ((tll_node)__v158035)->data[1];
      instr_free_struct(__v158035);
      instr_struct(&pair_struct_t629, 0, 2, 0, c_v158037);
      switch(((tll_node)pair_struct_t629)->tag) {
        case 0:
          pf_v158038 = ((tll_node)pair_struct_t629)->data[0];
          c_v158039 = ((tll_node)pair_struct_t629)->data[1];
          instr_free_struct(pair_struct_t629);
          if (b_v158036) {
            instr_clo(&lam_clo_t656, &lam_fun_t655, 0);
            ifte_ret_t762 = lam_clo_t656;
          }
          else {
            instr_clo(&lam_clo_t761, &lam_fun_t760, 1, env[1]);
            ifte_ret_t762 = lam_clo_t761;
          }
          instr_app(&app_ret_t763, ifte_ret_t762, c_v158039);
          instr_free_clo(ifte_ret_t762);
          instr_app(&app_ret_t764, app_ret_t763, 0);
          instr_free_clo(app_ret_t763);
          switch_ret_t630 = app_ret_t764;
          break;
      }
      switch_ret_t628 = switch_ret_t630;
      break;
  }
  return switch_ret_t628;
}

tll_ptr lam_fun_t767(tll_ptr c_v157990, tll_env env) {
  tll_ptr lam_clo_t766;
  instr_clo(&lam_clo_t766, &lam_fun_t765, 2, c_v157990, env[0]);
  return lam_clo_t766;
}

tll_ptr lam_fun_t833(tll_ptr __v158083, tll_env env) {
  tll_ptr Char_t777; tll_ptr Char_t778; tll_ptr Char_t779; tll_ptr Char_t780;
  tll_ptr Char_t781; tll_ptr Char_t782; tll_ptr Char_t783; tll_ptr Char_t784;
  tll_ptr Char_t785; tll_ptr Char_t786; tll_ptr Char_t787; tll_ptr Char_t788;
  tll_ptr Char_t789; tll_ptr Char_t790; tll_ptr Char_t791; tll_ptr Char_t792;
  tll_ptr Char_t793; tll_ptr Char_t794; tll_ptr Char_t795; tll_ptr Char_t796;
  tll_ptr Char_t797; tll_ptr Char_t798; tll_ptr Char_t799; tll_ptr Char_t800;
  tll_ptr Char_t826; tll_ptr Char_t827; tll_ptr EmptyString_t801;
  tll_ptr EmptyString_t828; tll_ptr String_t802; tll_ptr String_t803;
  tll_ptr String_t804; tll_ptr String_t805; tll_ptr String_t806;
  tll_ptr String_t807; tll_ptr String_t808; tll_ptr String_t809;
  tll_ptr String_t810; tll_ptr String_t811; tll_ptr String_t812;
  tll_ptr String_t813; tll_ptr String_t814; tll_ptr String_t815;
  tll_ptr String_t816; tll_ptr String_t817; tll_ptr String_t818;
  tll_ptr String_t819; tll_ptr String_t820; tll_ptr String_t821;
  tll_ptr String_t822; tll_ptr String_t823; tll_ptr String_t824;
  tll_ptr String_t825; tll_ptr String_t829; tll_ptr String_t830;
  tll_ptr __v158092; tll_ptr __v158098; tll_ptr __v158099;
  tll_ptr ans_v158093; tll_ptr app_ret_t831; tll_ptr c_v158094;
  tll_ptr c_v158096; tll_ptr call_ret_t774; tll_ptr call_ret_t775;
  tll_ptr call_ret_t776; tll_ptr close_tmp_t832; tll_ptr pair_struct_t771;
  tll_ptr pf_v158095; tll_ptr recv_msg_t769; tll_ptr s_v158097;
  tll_ptr switch_ret_t770; tll_ptr switch_ret_t772; tll_ptr switch_ret_t773;
  instr_recv(&recv_msg_t769, env[0]);
  __v158092 = recv_msg_t769;
  switch(((tll_node)__v158092)->tag) {
    case 0:
      ans_v158093 = ((tll_node)__v158092)->data[0];
      c_v158094 = ((tll_node)__v158092)->data[1];
      instr_free_struct(__v158092);
      instr_struct(&pair_struct_t771, 0, 2, 0, c_v158094);
      switch(((tll_node)pair_struct_t771)->tag) {
        case 0:
          pf_v158095 = ((tll_node)pair_struct_t771)->data[0];
          c_v158096 = ((tll_node)pair_struct_t771)->data[1];
          instr_free_struct(pair_struct_t771);
          switch(((tll_node)ans_v158093)->tag) {
            case 12:
              s_v158097 = ((tll_node)ans_v158093)->data[0];
              __v158098 = ((tll_node)ans_v158093)->data[1];
              instr_struct(&Char_t777, 5, 1, (tll_ptr)89);
              instr_struct(&Char_t778, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t779, 5, 1, (tll_ptr)117);
              instr_struct(&Char_t780, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t781, 5, 1, (tll_ptr)76);
              instr_struct(&Char_t782, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t783, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t784, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t785, 5, 1, (tll_ptr)33);
              instr_struct(&Char_t786, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t787, 5, 1, (tll_ptr)84);
              instr_struct(&Char_t788, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t789, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t790, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t791, 5, 1, (tll_ptr)97);
              instr_struct(&Char_t792, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t793, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t794, 5, 1, (tll_ptr)119);
              instr_struct(&Char_t795, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t796, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t797, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t798, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t799, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t800, 5, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t801, 6, 0);
              instr_struct(&String_t802, 7, 2, Char_t800, EmptyString_t801);
              instr_struct(&String_t803, 7, 2, Char_t799, String_t802);
              instr_struct(&String_t804, 7, 2, Char_t798, String_t803);
              instr_struct(&String_t805, 7, 2, Char_t797, String_t804);
              instr_struct(&String_t806, 7, 2, Char_t796, String_t805);
              instr_struct(&String_t807, 7, 2, Char_t795, String_t806);
              instr_struct(&String_t808, 7, 2, Char_t794, String_t807);
              instr_struct(&String_t809, 7, 2, Char_t793, String_t808);
              instr_struct(&String_t810, 7, 2, Char_t792, String_t809);
              instr_struct(&String_t811, 7, 2, Char_t791, String_t810);
              instr_struct(&String_t812, 7, 2, Char_t790, String_t811);
              instr_struct(&String_t813, 7, 2, Char_t789, String_t812);
              instr_struct(&String_t814, 7, 2, Char_t788, String_t813);
              instr_struct(&String_t815, 7, 2, Char_t787, String_t814);
              instr_struct(&String_t816, 7, 2, Char_t786, String_t815);
              instr_struct(&String_t817, 7, 2, Char_t785, String_t816);
              instr_struct(&String_t818, 7, 2, Char_t784, String_t817);
              instr_struct(&String_t819, 7, 2, Char_t783, String_t818);
              instr_struct(&String_t820, 7, 2, Char_t782, String_t819);
              instr_struct(&String_t821, 7, 2, Char_t781, String_t820);
              instr_struct(&String_t822, 7, 2, Char_t780, String_t821);
              instr_struct(&String_t823, 7, 2, Char_t779, String_t822);
              instr_struct(&String_t824, 7, 2, Char_t778, String_t823);
              instr_struct(&String_t825, 7, 2, Char_t777, String_t824);
              call_ret_t776 = cats_i20(String_t825, s_v158097);
              instr_struct(&Char_t826, 5, 1, (tll_ptr)46);
              instr_struct(&Char_t827, 5, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t828, 6, 0);
              instr_struct(&String_t829, 7, 2, Char_t827, EmptyString_t828);
              instr_struct(&String_t830, 7, 2, Char_t826, String_t829);
              call_ret_t775 = cats_i20(call_ret_t776, String_t830);
              call_ret_t774 = print_i34(call_ret_t775);
              instr_app(&app_ret_t831, call_ret_t774, 0);
              instr_free_clo(call_ret_t774);
              __v158099 = app_ret_t831;
              instr_close(&close_tmp_t832, c_v158096);
              switch_ret_t773 = close_tmp_t832;
              break;
          }
          switch_ret_t772 = switch_ret_t773;
          break;
      }
      switch_ret_t770 = switch_ret_t772;
      break;
  }
  return switch_ret_t770;
}

tll_ptr lam_fun_t835(tll_ptr c_v158073, tll_env env) {
  tll_ptr lam_clo_t834;
  instr_clo(&lam_clo_t834, &lam_fun_t833, 1, c_v158073);
  return lam_clo_t834;
}

tll_ptr player_loop_i61(tll_ptr ans_v157987, tll_ptr repeat_v157988, tll_ptr c_v157989) {
  tll_ptr app_ret_t838; tll_ptr ifte_ret_t837; tll_ptr lam_clo_t768;
  tll_ptr lam_clo_t836;
  if (repeat_v157988) {
    instr_clo(&lam_clo_t768, &lam_fun_t767, 1, repeat_v157988);
    ifte_ret_t837 = lam_clo_t768;
  }
  else {
    instr_clo(&lam_clo_t836, &lam_fun_t835, 0);
    ifte_ret_t837 = lam_clo_t836;
  }
  instr_app(&app_ret_t838, ifte_ret_t837, c_v157989);
  return app_ret_t838;
}

tll_ptr lam_fun_t840(tll_ptr c_v158105, tll_env env) {
  tll_ptr call_ret_t839;
  call_ret_t839 = player_loop_i61(env[1], env[0], c_v158105);
  return call_ret_t839;
}

tll_ptr lam_fun_t842(tll_ptr repeat_v158103, tll_env env) {
  tll_ptr lam_clo_t841;
  instr_clo(&lam_clo_t841, &lam_fun_t840, 2, repeat_v158103, env[0]);
  return lam_clo_t841;
}

tll_ptr lam_fun_t844(tll_ptr ans_v158100, tll_env env) {
  tll_ptr lam_clo_t843;
  instr_clo(&lam_clo_t843, &lam_fun_t842, 1, ans_v158100);
  return lam_clo_t843;
}

tll_ptr lam_fun_t989(tll_ptr __v158107, tll_env env) {
  tll_ptr Char_t851; tll_ptr Char_t852; tll_ptr Char_t853; tll_ptr Char_t854;
  tll_ptr Char_t855; tll_ptr Char_t856; tll_ptr Char_t857; tll_ptr Char_t858;
  tll_ptr Char_t859; tll_ptr Char_t860; tll_ptr Char_t861; tll_ptr Char_t862;
  tll_ptr Char_t878; tll_ptr Char_t879; tll_ptr Char_t880; tll_ptr Char_t881;
  tll_ptr Char_t882; tll_ptr Char_t883; tll_ptr Char_t884; tll_ptr Char_t885;
  tll_ptr Char_t886; tll_ptr Char_t887; tll_ptr Char_t888; tll_ptr Char_t889;
  tll_ptr Char_t890; tll_ptr Char_t891; tll_ptr Char_t892; tll_ptr Char_t893;
  tll_ptr Char_t894; tll_ptr Char_t895; tll_ptr Char_t896; tll_ptr Char_t897;
  tll_ptr Char_t898; tll_ptr Char_t899; tll_ptr Char_t900; tll_ptr Char_t901;
  tll_ptr Char_t902; tll_ptr Char_t903; tll_ptr Char_t904; tll_ptr Char_t905;
  tll_ptr Char_t906; tll_ptr Char_t907; tll_ptr Char_t908; tll_ptr Char_t909;
  tll_ptr Char_t910; tll_ptr Char_t949; tll_ptr Char_t950; tll_ptr Char_t951;
  tll_ptr Char_t952; tll_ptr Char_t953; tll_ptr Char_t954; tll_ptr Char_t955;
  tll_ptr Char_t956; tll_ptr Char_t957; tll_ptr Char_t969; tll_ptr Char_t970;
  tll_ptr Char_t971; tll_ptr Char_t972; tll_ptr Char_t973; tll_ptr Char_t974;
  tll_ptr Char_t975; tll_ptr Char_t976; tll_ptr EmptyString_t863;
  tll_ptr EmptyString_t911; tll_ptr EmptyString_t958;
  tll_ptr EmptyString_t977; tll_ptr String_t864; tll_ptr String_t865;
  tll_ptr String_t866; tll_ptr String_t867; tll_ptr String_t868;
  tll_ptr String_t869; tll_ptr String_t870; tll_ptr String_t871;
  tll_ptr String_t872; tll_ptr String_t873; tll_ptr String_t874;
  tll_ptr String_t875; tll_ptr String_t912; tll_ptr String_t913;
  tll_ptr String_t914; tll_ptr String_t915; tll_ptr String_t916;
  tll_ptr String_t917; tll_ptr String_t918; tll_ptr String_t919;
  tll_ptr String_t920; tll_ptr String_t921; tll_ptr String_t922;
  tll_ptr String_t923; tll_ptr String_t924; tll_ptr String_t925;
  tll_ptr String_t926; tll_ptr String_t927; tll_ptr String_t928;
  tll_ptr String_t929; tll_ptr String_t930; tll_ptr String_t931;
  tll_ptr String_t932; tll_ptr String_t933; tll_ptr String_t934;
  tll_ptr String_t935; tll_ptr String_t936; tll_ptr String_t937;
  tll_ptr String_t938; tll_ptr String_t939; tll_ptr String_t940;
  tll_ptr String_t941; tll_ptr String_t942; tll_ptr String_t943;
  tll_ptr String_t944; tll_ptr String_t959; tll_ptr String_t960;
  tll_ptr String_t961; tll_ptr String_t962; tll_ptr String_t963;
  tll_ptr String_t964; tll_ptr String_t965; tll_ptr String_t966;
  tll_ptr String_t967; tll_ptr String_t978; tll_ptr String_t979;
  tll_ptr String_t980; tll_ptr String_t981; tll_ptr String_t982;
  tll_ptr String_t983; tll_ptr String_t984; tll_ptr String_t985;
  tll_ptr __v158118; tll_ptr __v158121; tll_ptr __v158122; tll_ptr __v158123;
  tll_ptr ans_v158116; tll_ptr app_ret_t876; tll_ptr app_ret_t945;
  tll_ptr app_ret_t986; tll_ptr app_ret_t988; tll_ptr c_v158117;
  tll_ptr c_v158120; tll_ptr call_ret_t850; tll_ptr call_ret_t877;
  tll_ptr call_ret_t946; tll_ptr call_ret_t947; tll_ptr call_ret_t948;
  tll_ptr call_ret_t968; tll_ptr call_ret_t987; tll_ptr pair_struct_t846;
  tll_ptr recv_msg_t848; tll_ptr repeat_v158119; tll_ptr switch_ret_t847;
  tll_ptr switch_ret_t849;
  instr_struct(&pair_struct_t846, 0, 2, 0, env[0]);
  switch(((tll_node)pair_struct_t846)->tag) {
    case 0:
      ans_v158116 = ((tll_node)pair_struct_t846)->data[0];
      c_v158117 = ((tll_node)pair_struct_t846)->data[1];
      instr_free_struct(pair_struct_t846);
      instr_recv(&recv_msg_t848, c_v158117);
      __v158118 = recv_msg_t848;
      switch(((tll_node)__v158118)->tag) {
        case 0:
          repeat_v158119 = ((tll_node)__v158118)->data[0];
          c_v158120 = ((tll_node)__v158118)->data[1];
          instr_free_struct(__v158118);
          instr_struct(&Char_t851, 5, 1, (tll_ptr)87);
          instr_struct(&Char_t852, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t853, 5, 1, (tll_ptr)114);
          instr_struct(&Char_t854, 5, 1, (tll_ptr)100);
          instr_struct(&Char_t855, 5, 1, (tll_ptr)108);
          instr_struct(&Char_t856, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t857, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t858, 5, 1, (tll_ptr)71);
          instr_struct(&Char_t859, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t860, 5, 1, (tll_ptr)109);
          instr_struct(&Char_t861, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t862, 5, 1, (tll_ptr)10);
          instr_struct(&EmptyString_t863, 6, 0);
          instr_struct(&String_t864, 7, 2, Char_t862, EmptyString_t863);
          instr_struct(&String_t865, 7, 2, Char_t861, String_t864);
          instr_struct(&String_t866, 7, 2, Char_t860, String_t865);
          instr_struct(&String_t867, 7, 2, Char_t859, String_t866);
          instr_struct(&String_t868, 7, 2, Char_t858, String_t867);
          instr_struct(&String_t869, 7, 2, Char_t857, String_t868);
          instr_struct(&String_t870, 7, 2, Char_t856, String_t869);
          instr_struct(&String_t871, 7, 2, Char_t855, String_t870);
          instr_struct(&String_t872, 7, 2, Char_t854, String_t871);
          instr_struct(&String_t873, 7, 2, Char_t853, String_t872);
          instr_struct(&String_t874, 7, 2, Char_t852, String_t873);
          instr_struct(&String_t875, 7, 2, Char_t851, String_t874);
          call_ret_t850 = print_i34(String_t875);
          instr_app(&app_ret_t876, call_ret_t850, 0);
          instr_free_clo(call_ret_t850);
          __v158121 = app_ret_t876;
          instr_struct(&Char_t878, 5, 1, (tll_ptr)80);
          instr_struct(&Char_t879, 5, 1, (tll_ptr)108);
          instr_struct(&Char_t880, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t881, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t882, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t883, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t884, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t885, 5, 1, (tll_ptr)103);
          instr_struct(&Char_t886, 5, 1, (tll_ptr)117);
          instr_struct(&Char_t887, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t888, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t889, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t890, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t891, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t892, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t893, 5, 1, (tll_ptr)119);
          instr_struct(&Char_t894, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t895, 5, 1, (tll_ptr)114);
          instr_struct(&Char_t896, 5, 1, (tll_ptr)100);
          instr_struct(&Char_t897, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t898, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t899, 5, 1, (tll_ptr)102);
          instr_struct(&Char_t900, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t901, 5, 1, (tll_ptr)108);
          instr_struct(&Char_t902, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t903, 5, 1, (tll_ptr)110);
          instr_struct(&Char_t904, 5, 1, (tll_ptr)103);
          instr_struct(&Char_t905, 5, 1, (tll_ptr)116);
          instr_struct(&Char_t906, 5, 1, (tll_ptr)104);
          instr_struct(&Char_t907, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t908, 5, 1, (tll_ptr)53);
          instr_struct(&Char_t909, 5, 1, (tll_ptr)46);
          instr_struct(&Char_t910, 5, 1, (tll_ptr)10);
          instr_struct(&EmptyString_t911, 6, 0);
          instr_struct(&String_t912, 7, 2, Char_t910, EmptyString_t911);
          instr_struct(&String_t913, 7, 2, Char_t909, String_t912);
          instr_struct(&String_t914, 7, 2, Char_t908, String_t913);
          instr_struct(&String_t915, 7, 2, Char_t907, String_t914);
          instr_struct(&String_t916, 7, 2, Char_t906, String_t915);
          instr_struct(&String_t917, 7, 2, Char_t905, String_t916);
          instr_struct(&String_t918, 7, 2, Char_t904, String_t917);
          instr_struct(&String_t919, 7, 2, Char_t903, String_t918);
          instr_struct(&String_t920, 7, 2, Char_t902, String_t919);
          instr_struct(&String_t921, 7, 2, Char_t901, String_t920);
          instr_struct(&String_t922, 7, 2, Char_t900, String_t921);
          instr_struct(&String_t923, 7, 2, Char_t899, String_t922);
          instr_struct(&String_t924, 7, 2, Char_t898, String_t923);
          instr_struct(&String_t925, 7, 2, Char_t897, String_t924);
          instr_struct(&String_t926, 7, 2, Char_t896, String_t925);
          instr_struct(&String_t927, 7, 2, Char_t895, String_t926);
          instr_struct(&String_t928, 7, 2, Char_t894, String_t927);
          instr_struct(&String_t929, 7, 2, Char_t893, String_t928);
          instr_struct(&String_t930, 7, 2, Char_t892, String_t929);
          instr_struct(&String_t931, 7, 2, Char_t891, String_t930);
          instr_struct(&String_t932, 7, 2, Char_t890, String_t931);
          instr_struct(&String_t933, 7, 2, Char_t889, String_t932);
          instr_struct(&String_t934, 7, 2, Char_t888, String_t933);
          instr_struct(&String_t935, 7, 2, Char_t887, String_t934);
          instr_struct(&String_t936, 7, 2, Char_t886, String_t935);
          instr_struct(&String_t937, 7, 2, Char_t885, String_t936);
          instr_struct(&String_t938, 7, 2, Char_t884, String_t937);
          instr_struct(&String_t939, 7, 2, Char_t883, String_t938);
          instr_struct(&String_t940, 7, 2, Char_t882, String_t939);
          instr_struct(&String_t941, 7, 2, Char_t881, String_t940);
          instr_struct(&String_t942, 7, 2, Char_t880, String_t941);
          instr_struct(&String_t943, 7, 2, Char_t879, String_t942);
          instr_struct(&String_t944, 7, 2, Char_t878, String_t943);
          call_ret_t877 = print_i34(String_t944);
          instr_app(&app_ret_t945, call_ret_t877, 0);
          instr_free_clo(call_ret_t877);
          __v158122 = app_ret_t945;
          instr_struct(&Char_t949, 5, 1, (tll_ptr)89);
          instr_struct(&Char_t950, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t951, 5, 1, (tll_ptr)117);
          instr_struct(&Char_t952, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t953, 5, 1, (tll_ptr)104);
          instr_struct(&Char_t954, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t955, 5, 1, (tll_ptr)118);
          instr_struct(&Char_t956, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t957, 5, 1, (tll_ptr)32);
          instr_struct(&EmptyString_t958, 6, 0);
          instr_struct(&String_t959, 7, 2, Char_t957, EmptyString_t958);
          instr_struct(&String_t960, 7, 2, Char_t956, String_t959);
          instr_struct(&String_t961, 7, 2, Char_t955, String_t960);
          instr_struct(&String_t962, 7, 2, Char_t954, String_t961);
          instr_struct(&String_t963, 7, 2, Char_t953, String_t962);
          instr_struct(&String_t964, 7, 2, Char_t952, String_t963);
          instr_struct(&String_t965, 7, 2, Char_t951, String_t964);
          instr_struct(&String_t966, 7, 2, Char_t950, String_t965);
          instr_struct(&String_t967, 7, 2, Char_t949, String_t966);
          call_ret_t968 = string_of_nat_i39(repeat_v158119);
          call_ret_t948 = cats_i20(String_t967, call_ret_t968);
          instr_struct(&Char_t969, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t970, 5, 1, (tll_ptr)116);
          instr_struct(&Char_t971, 5, 1, (tll_ptr)114);
          instr_struct(&Char_t972, 5, 1, (tll_ptr)105);
          instr_struct(&Char_t973, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t974, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t975, 5, 1, (tll_ptr)46);
          instr_struct(&Char_t976, 5, 1, (tll_ptr)10);
          instr_struct(&EmptyString_t977, 6, 0);
          instr_struct(&String_t978, 7, 2, Char_t976, EmptyString_t977);
          instr_struct(&String_t979, 7, 2, Char_t975, String_t978);
          instr_struct(&String_t980, 7, 2, Char_t974, String_t979);
          instr_struct(&String_t981, 7, 2, Char_t973, String_t980);
          instr_struct(&String_t982, 7, 2, Char_t972, String_t981);
          instr_struct(&String_t983, 7, 2, Char_t971, String_t982);
          instr_struct(&String_t984, 7, 2, Char_t970, String_t983);
          instr_struct(&String_t985, 7, 2, Char_t969, String_t984);
          call_ret_t947 = cats_i20(call_ret_t948, String_t985);
          call_ret_t946 = print_i34(call_ret_t947);
          instr_app(&app_ret_t986, call_ret_t946, 0);
          instr_free_clo(call_ret_t946);
          __v158123 = app_ret_t986;
          call_ret_t987 = player_loop_i61(0, repeat_v158119, c_v158120);
          instr_app(&app_ret_t988, call_ret_t987, 0);
          instr_free_clo(call_ret_t987);
          switch_ret_t849 = app_ret_t988;
          break;
      }
      switch_ret_t847 = switch_ret_t849;
      break;
  }
  return switch_ret_t847;
}

tll_ptr player_i62(tll_ptr c_v158106) {
  tll_ptr lam_clo_t990;
  instr_clo(&lam_clo_t990, &lam_fun_t989, 1, c_v158106);
  return lam_clo_t990;
}

tll_ptr lam_fun_t992(tll_ptr c_v158124, tll_env env) {
  tll_ptr call_ret_t991;
  call_ret_t991 = player_i62(c_v158124);
  return call_ret_t991;
}

tll_ptr lam_fun_t998(tll_ptr __v158160, tll_env env) {
  
  
  return 0;
}

tll_ptr lam_fun_t1000(tll_ptr c_v158158, tll_env env) {
  tll_ptr lam_clo_t999;
  instr_clo(&lam_clo_t999, &lam_fun_t998, 0);
  return lam_clo_t999;
}

tll_ptr lam_fun_t1007(tll_ptr __v158165, tll_env env) {
  tll_ptr add_ret_t1005; tll_ptr app_ret_t1006; tll_ptr c_v158168;
  tll_ptr call_ret_t1002; tll_ptr call_ret_t1004; tll_ptr send_ch_t1003;
  tll_ptr x_v158169;
  call_ret_t1002 = wordle_diff_i52(env[3], env[1]);
  x_v158169 = call_ret_t1002;
  instr_send(&send_ch_t1003, env[0], x_v158169);
  c_v158168 = send_ch_t1003;
  add_ret_t1005 = env[2] - 1;
  call_ret_t1004 = server_loop_i63(env[3], add_ret_t1005, c_v158168);
  instr_app(&app_ret_t1006, call_ret_t1004, 0);
  instr_free_clo(call_ret_t1004);
  return app_ret_t1006;
}

tll_ptr lam_fun_t1009(tll_ptr c_v158161, tll_env env) {
  tll_ptr lam_clo_t1008;
  instr_clo(&lam_clo_t1008, &lam_fun_t1007, 4,
            c_v158161, env[0], env[1], env[2]);
  return lam_clo_t1008;
}

tll_ptr lam_fun_t1014(tll_ptr __v158141, tll_env env) {
  tll_ptr __v158153; tll_ptr app_ret_t1012; tll_ptr app_ret_t1013;
  tll_ptr b_v158156; tll_ptr c_v158155; tll_ptr c_v158157;
  tll_ptr call_ret_t996; tll_ptr guess_v158154; tll_ptr ifte_ret_t1011;
  tll_ptr lam_clo_t1001; tll_ptr lam_clo_t1010; tll_ptr recv_msg_t994;
  tll_ptr send_ch_t997; tll_ptr switch_ret_t995;
  instr_recv(&recv_msg_t994, env[0]);
  __v158153 = recv_msg_t994;
  switch(((tll_node)__v158153)->tag) {
    case 0:
      guess_v158154 = ((tll_node)__v158153)->data[0];
      c_v158155 = ((tll_node)__v158153)->data[1];
      instr_free_struct(__v158153);
      call_ret_t996 = eqw_i53(env[2], guess_v158154);
      b_v158156 = call_ret_t996;
      instr_send(&send_ch_t997, c_v158155, b_v158156);
      c_v158157 = send_ch_t997;
      if (b_v158156) {
        instr_clo(&lam_clo_t1001, &lam_fun_t1000, 0);
        ifte_ret_t1011 = lam_clo_t1001;
      }
      else {
        instr_clo(&lam_clo_t1010, &lam_fun_t1009, 3,
                  guess_v158154, env[1], env[2]);
        ifte_ret_t1011 = lam_clo_t1010;
      }
      instr_app(&app_ret_t1012, ifte_ret_t1011, c_v158157);
      instr_free_clo(ifte_ret_t1011);
      instr_app(&app_ret_t1013, app_ret_t1012, 0);
      instr_free_clo(app_ret_t1012);
      switch_ret_t995 = app_ret_t1013;
      break;
  }
  return switch_ret_t995;
}

tll_ptr lam_fun_t1016(tll_ptr c_v158128, tll_env env) {
  tll_ptr lam_clo_t1015;
  instr_clo(&lam_clo_t1015, &lam_fun_t1014, 3, c_v158128, env[0], env[1]);
  return lam_clo_t1015;
}

tll_ptr lam_fun_t1019(tll_ptr __v158173, tll_env env) {
  tll_ptr c_v158175; tll_ptr send_ch_t1018;
  instr_send(&send_ch_t1018, env[0], env[1]);
  c_v158175 = send_ch_t1018;
  return 0;
}

tll_ptr lam_fun_t1021(tll_ptr c_v158170, tll_env env) {
  tll_ptr lam_clo_t1020;
  instr_clo(&lam_clo_t1020, &lam_fun_t1019, 2, c_v158170, env[0]);
  return lam_clo_t1020;
}

tll_ptr server_loop_i63(tll_ptr ans_v158125, tll_ptr repeat_v158126, tll_ptr c_v158127) {
  tll_ptr app_ret_t1024; tll_ptr ifte_ret_t1023; tll_ptr lam_clo_t1017;
  tll_ptr lam_clo_t1022;
  if (repeat_v158126) {
    instr_clo(&lam_clo_t1017, &lam_fun_t1016, 2, repeat_v158126, ans_v158125);
    ifte_ret_t1023 = lam_clo_t1017;
  }
  else {
    instr_clo(&lam_clo_t1022, &lam_fun_t1021, 1, ans_v158125);
    ifte_ret_t1023 = lam_clo_t1022;
  }
  instr_app(&app_ret_t1024, ifte_ret_t1023, c_v158127);
  return app_ret_t1024;
}

tll_ptr lam_fun_t1026(tll_ptr c_v158181, tll_env env) {
  tll_ptr call_ret_t1025;
  call_ret_t1025 = server_loop_i63(env[1], env[0], c_v158181);
  return call_ret_t1025;
}

tll_ptr lam_fun_t1028(tll_ptr repeat_v158179, tll_env env) {
  tll_ptr lam_clo_t1027;
  instr_clo(&lam_clo_t1027, &lam_fun_t1026, 2, repeat_v158179, env[0]);
  return lam_clo_t1027;
}

tll_ptr lam_fun_t1030(tll_ptr ans_v158176, tll_env env) {
  tll_ptr lam_clo_t1029;
  instr_clo(&lam_clo_t1029, &lam_fun_t1028, 1, ans_v158176);
  return lam_clo_t1029;
}

tll_ptr lam_fun_t1047(tll_ptr __v158183, tll_env env) {
  tll_ptr Char_t1034; tll_ptr Char_t1035; tll_ptr Char_t1036;
  tll_ptr Char_t1037; tll_ptr Char_t1038; tll_ptr EmptyString_t1039;
  tll_ptr String_t1040; tll_ptr String_t1041; tll_ptr String_t1042;
  tll_ptr String_t1043; tll_ptr String_t1044; tll_ptr Word_t1045;
  tll_ptr app_ret_t1046; tll_ptr c_v158185; tll_ptr call_ret_t1033;
  tll_ptr send_ch_t1032;
  instr_send(&send_ch_t1032, env[0], (tll_ptr)6);
  c_v158185 = send_ch_t1032;
  instr_struct(&Char_t1034, 5, 1, (tll_ptr)119);
  instr_struct(&Char_t1035, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t1036, 5, 1, (tll_ptr)114);
  instr_struct(&Char_t1037, 5, 1, (tll_ptr)108);
  instr_struct(&Char_t1038, 5, 1, (tll_ptr)100);
  instr_struct(&EmptyString_t1039, 6, 0);
  instr_struct(&String_t1040, 7, 2, Char_t1038, EmptyString_t1039);
  instr_struct(&String_t1041, 7, 2, Char_t1037, String_t1040);
  instr_struct(&String_t1042, 7, 2, Char_t1036, String_t1041);
  instr_struct(&String_t1043, 7, 2, Char_t1035, String_t1042);
  instr_struct(&String_t1044, 7, 2, Char_t1034, String_t1043);
  instr_struct(&Word_t1045, 12, 2, String_t1044, 0);
  call_ret_t1033 = server_loop_i63(Word_t1045, (tll_ptr)6, c_v158185);
  instr_app(&app_ret_t1046, call_ret_t1033, 0);
  instr_free_clo(call_ret_t1033);
  return app_ret_t1046;
}

tll_ptr server_i64(tll_ptr c_v158182) {
  tll_ptr lam_clo_t1048;
  instr_clo(&lam_clo_t1048, &lam_fun_t1047, 1, c_v158182);
  return lam_clo_t1048;
}

tll_ptr lam_fun_t1050(tll_ptr c_v158186, tll_env env) {
  tll_ptr call_ret_t1049;
  call_ret_t1049 = server_i64(c_v158186);
  return call_ret_t1049;
}

tll_ptr fork_fun_t1054(tll_env env) {
  tll_ptr app_ret_t1053; tll_ptr call_ret_t1052; tll_ptr fork_ret_t1056;
  call_ret_t1052 = server_i64(env[0]);
  instr_app(&app_ret_t1053, call_ret_t1052, 0);
  instr_free_clo(call_ret_t1052);
  fork_ret_t1056 = app_ret_t1053;
  instr_free_thread(env);
  return fork_ret_t1056;
}

tll_ptr fork_fun_t1062(tll_env env) {
  tll_ptr __v158196; tll_ptr __v158199; tll_ptr app_ret_t1060;
  tll_ptr c0_v158198; tll_ptr c0_v158200; tll_ptr c_v158197;
  tll_ptr call_ret_t1059; tll_ptr fork_ret_t1064; tll_ptr recv_msg_t1057;
  tll_ptr send_ch_t1061; tll_ptr switch_ret_t1058;
  instr_recv(&recv_msg_t1057, env[0]);
  __v158196 = recv_msg_t1057;
  switch(((tll_node)__v158196)->tag) {
    case 0:
      c_v158197 = ((tll_node)__v158196)->data[0];
      c0_v158198 = ((tll_node)__v158196)->data[1];
      instr_free_struct(__v158196);
      call_ret_t1059 = player_i62(c_v158197);
      instr_app(&app_ret_t1060, call_ret_t1059, 0);
      instr_free_clo(call_ret_t1059);
      __v158199 = app_ret_t1060;
      instr_send(&send_ch_t1061, c0_v158198, 0);
      c0_v158200 = send_ch_t1061;
      switch_ret_t1058 = 0;
      break;
  }
  fork_ret_t1064 = switch_ret_t1058;
  instr_free_thread(env);
  return fork_ret_t1064;
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
  tll_ptr String_t363; tll_ptr String_t366; tll_ptr __v158202;
  tll_ptr __v158203; tll_ptr c0_v158189; tll_ptr c0_v158201;
  tll_ptr c0_v158204; tll_ptr c_v158187; tll_ptr close_tmp_t1068;
  tll_ptr consUU_t368; tll_ptr consUU_t369; tll_ptr consUU_t370;
  tll_ptr consUU_t371; tll_ptr consUU_t372; tll_ptr consUU_t373;
  tll_ptr consUU_t374; tll_ptr consUU_t375; tll_ptr consUU_t376;
  tll_ptr consUU_t377; tll_ptr fork_ch_t1055; tll_ptr fork_ch_t1063;
  tll_ptr lam_clo_t1031; tll_ptr lam_clo_t104; tll_ptr lam_clo_t1051;
  tll_ptr lam_clo_t110; tll_ptr lam_clo_t118; tll_ptr lam_clo_t12;
  tll_ptr lam_clo_t126; tll_ptr lam_clo_t134; tll_ptr lam_clo_t140;
  tll_ptr lam_clo_t151; tll_ptr lam_clo_t16; tll_ptr lam_clo_t167;
  tll_ptr lam_clo_t179; tll_ptr lam_clo_t191; tll_ptr lam_clo_t203;
  tll_ptr lam_clo_t215; tll_ptr lam_clo_t227; tll_ptr lam_clo_t239;
  tll_ptr lam_clo_t252; tll_ptr lam_clo_t265; tll_ptr lam_clo_t278;
  tll_ptr lam_clo_t28; tll_ptr lam_clo_t288; tll_ptr lam_clo_t298;
  tll_ptr lam_clo_t308; tll_ptr lam_clo_t318; tll_ptr lam_clo_t327;
  tll_ptr lam_clo_t336; tll_ptr lam_clo_t34; tll_ptr lam_clo_t391;
  tll_ptr lam_clo_t396; tll_ptr lam_clo_t40; tll_ptr lam_clo_t406;
  tll_ptr lam_clo_t450; tll_ptr lam_clo_t46; tll_ptr lam_clo_t463;
  tll_ptr lam_clo_t467; tll_ptr lam_clo_t476; tll_ptr lam_clo_t506;
  tll_ptr lam_clo_t515; tll_ptr lam_clo_t52; tll_ptr lam_clo_t523;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t6; tll_ptr lam_clo_t623;
  tll_ptr lam_clo_t72; tll_ptr lam_clo_t77; tll_ptr lam_clo_t83;
  tll_ptr lam_clo_t845; tll_ptr lam_clo_t92; tll_ptr lam_clo_t98;
  tll_ptr lam_clo_t993; tll_ptr nilUU_t367; tll_ptr recv_msg_t1066;
  tll_ptr send_ch_t1065; tll_ptr switch_ret_t1067;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i90 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i91 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i92 = lam_clo_t16;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  comparebclo_i93 = lam_clo_t28;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 0);
  ltenclo_i94 = lam_clo_t34;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 0);
  gtenclo_i95 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  ltnclo_i96 = lam_clo_t46;
  instr_clo(&lam_clo_t52, &lam_fun_t51, 0);
  gtnclo_i97 = lam_clo_t52;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  eqnclo_i98 = lam_clo_t58;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  comparenclo_i99 = lam_clo_t72;
  instr_clo(&lam_clo_t77, &lam_fun_t76, 0);
  predclo_i100 = lam_clo_t77;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i101 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i102 = lam_clo_t92;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  mulnclo_i103 = lam_clo_t98;
  instr_clo(&lam_clo_t104, &lam_fun_t103, 0);
  divnclo_i104 = lam_clo_t104;
  instr_clo(&lam_clo_t110, &lam_fun_t109, 0);
  modnclo_i105 = lam_clo_t110;
  instr_clo(&lam_clo_t118, &lam_fun_t117, 0);
  eqcclo_i106 = lam_clo_t118;
  instr_clo(&lam_clo_t126, &lam_fun_t125, 0);
  comparecclo_i107 = lam_clo_t126;
  instr_clo(&lam_clo_t134, &lam_fun_t133, 0);
  catsclo_i108 = lam_clo_t134;
  instr_clo(&lam_clo_t140, &lam_fun_t139, 0);
  strlenclo_i109 = lam_clo_t140;
  instr_clo(&lam_clo_t151, &lam_fun_t150, 0);
  eqsclo_i110 = lam_clo_t151;
  instr_clo(&lam_clo_t167, &lam_fun_t166, 0);
  comparesclo_i111 = lam_clo_t167;
  instr_clo(&lam_clo_t179, &lam_fun_t178, 0);
  and_thenUUUclo_i112 = lam_clo_t179;
  instr_clo(&lam_clo_t191, &lam_fun_t190, 0);
  and_thenUULclo_i113 = lam_clo_t191;
  instr_clo(&lam_clo_t203, &lam_fun_t202, 0);
  and_thenULUclo_i114 = lam_clo_t203;
  instr_clo(&lam_clo_t215, &lam_fun_t214, 0);
  and_thenULLclo_i115 = lam_clo_t215;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 0);
  and_thenLULclo_i116 = lam_clo_t227;
  instr_clo(&lam_clo_t239, &lam_fun_t238, 0);
  and_thenLLLclo_i117 = lam_clo_t239;
  instr_clo(&lam_clo_t252, &lam_fun_t251, 0);
  lenUUclo_i118 = lam_clo_t252;
  instr_clo(&lam_clo_t265, &lam_fun_t264, 0);
  lenULclo_i119 = lam_clo_t265;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 0);
  lenLLclo_i120 = lam_clo_t278;
  instr_clo(&lam_clo_t288, &lam_fun_t287, 0);
  appendUUclo_i121 = lam_clo_t288;
  instr_clo(&lam_clo_t298, &lam_fun_t297, 0);
  appendULclo_i122 = lam_clo_t298;
  instr_clo(&lam_clo_t308, &lam_fun_t307, 0);
  appendLLclo_i123 = lam_clo_t308;
  instr_clo(&lam_clo_t318, &lam_fun_t317, 0);
  readlineclo_i124 = lam_clo_t318;
  instr_clo(&lam_clo_t327, &lam_fun_t326, 0);
  printclo_i125 = lam_clo_t327;
  instr_clo(&lam_clo_t336, &lam_fun_t335, 0);
  prerrclo_i126 = lam_clo_t336;
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
  get_atclo_i127 = lam_clo_t391;
  instr_clo(&lam_clo_t396, &lam_fun_t395, 0);
  string_of_digitclo_i128 = lam_clo_t396;
  instr_clo(&lam_clo_t406, &lam_fun_t405, 0);
  string_of_natclo_i129 = lam_clo_t406;
  instr_clo(&lam_clo_t450, &lam_fun_t449, 0);
  digit_of_charclo_i130 = lam_clo_t450;
  instr_clo(&lam_clo_t463, &lam_fun_t462, 0);
  nat_of_string_loopclo_i131 = lam_clo_t463;
  instr_clo(&lam_clo_t467, &lam_fun_t466, 0);
  nat_of_stringclo_i132 = lam_clo_t467;
  instr_clo(&lam_clo_t476, &lam_fun_t475, 0);
  containsclo_i133 = lam_clo_t476;
  instr_clo(&lam_clo_t506, &lam_fun_t505, 0);
  string_diffclo_i134 = lam_clo_t506;
  instr_clo(&lam_clo_t515, &lam_fun_t514, 0);
  wordle_diffclo_i135 = lam_clo_t515;
  instr_clo(&lam_clo_t523, &lam_fun_t522, 0);
  eqwclo_i136 = lam_clo_t523;
  instr_clo(&lam_clo_t623, &lam_fun_t622, 0);
  read_wordclo_i137 = lam_clo_t623;
  instr_clo(&lam_clo_t845, &lam_fun_t844, 0);
  player_loopclo_i138 = lam_clo_t845;
  instr_clo(&lam_clo_t993, &lam_fun_t992, 0);
  playerclo_i139 = lam_clo_t993;
  instr_clo(&lam_clo_t1031, &lam_fun_t1030, 0);
  server_loopclo_i140 = lam_clo_t1031;
  instr_clo(&lam_clo_t1051, &lam_fun_t1050, 0);
  serverclo_i141 = lam_clo_t1051;
  instr_fork(&fork_ch_t1055, &fork_fun_t1054, 0);
  c_v158187 = fork_ch_t1055;
  instr_fork(&fork_ch_t1063, &fork_fun_t1062, 0);
  c0_v158189 = fork_ch_t1063;
  instr_send(&send_ch_t1065, c0_v158189, c_v158187);
  c0_v158201 = send_ch_t1065;
  instr_recv(&recv_msg_t1066, c0_v158201);
  __v158202 = recv_msg_t1066;
  switch(((tll_node)__v158202)->tag) {
    case 0:
      __v158203 = ((tll_node)__v158202)->data[0];
      c0_v158204 = ((tll_node)__v158202)->data[1];
      instr_free_struct(__v158202);
      instr_close(&close_tmp_t1068, c0_v158204);
      switch_ret_t1067 = close_tmp_t1068;
      break;
  }
  return 0;
}

