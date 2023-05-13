#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v38542, tll_ptr b2_v38543);
tll_ptr orb_i2(tll_ptr b1_v38547, tll_ptr b2_v38548);
tll_ptr notb_i3(tll_ptr b_v38552);
tll_ptr compareb_i4(tll_ptr b1_v38554, tll_ptr b2_v38555);
tll_ptr lten_i5(tll_ptr x_v38559, tll_ptr y_v38560);
tll_ptr gten_i6(tll_ptr x_v38564, tll_ptr y_v38565);
tll_ptr ltn_i7(tll_ptr x_v38569, tll_ptr y_v38570);
tll_ptr gtn_i8(tll_ptr x_v38574, tll_ptr y_v38575);
tll_ptr eqn_i9(tll_ptr x_v38579, tll_ptr y_v38580);
tll_ptr comparen_i10(tll_ptr n1_v38584, tll_ptr n2_v38585);
tll_ptr pred_i11(tll_ptr x_v38589);
tll_ptr addn_i12(tll_ptr x_v38591, tll_ptr y_v38592);
tll_ptr subn_i13(tll_ptr x_v38596, tll_ptr y_v38597);
tll_ptr muln_i14(tll_ptr x_v38601, tll_ptr y_v38602);
tll_ptr divn_i15(tll_ptr x_v38606, tll_ptr y_v38607);
tll_ptr modn_i16(tll_ptr x_v38611, tll_ptr y_v38612);
tll_ptr eqc_i17(tll_ptr c1_v38616, tll_ptr c2_v38617);
tll_ptr comparec_i18(tll_ptr c1_v38623, tll_ptr c2_v38624);
tll_ptr cats_i19(tll_ptr s1_v38630, tll_ptr s2_v38631);
tll_ptr strlen_i20(tll_ptr s_v38637);
tll_ptr eqs_i21(tll_ptr s1_v38641, tll_ptr s2_v38642);
tll_ptr compares_i22(tll_ptr s1_v38652, tll_ptr s2_v38653);
tll_ptr and_thenUUU_i61(tll_ptr A_v38663, tll_ptr B_v38664, tll_ptr opt_v38665, tll_ptr f_v38666);
tll_ptr and_thenUUL_i60(tll_ptr A_v38678, tll_ptr B_v38679, tll_ptr opt_v38680, tll_ptr f_v38681);
tll_ptr and_thenULU_i59(tll_ptr A_v38693, tll_ptr B_v38694, tll_ptr opt_v38695, tll_ptr f_v38696);
tll_ptr and_thenULL_i58(tll_ptr A_v38708, tll_ptr B_v38709, tll_ptr opt_v38710, tll_ptr f_v38711);
tll_ptr and_thenLUL_i56(tll_ptr A_v38723, tll_ptr B_v38724, tll_ptr opt_v38725, tll_ptr f_v38726);
tll_ptr and_thenLLL_i54(tll_ptr A_v38738, tll_ptr B_v38739, tll_ptr opt_v38740, tll_ptr f_v38741);
tll_ptr lenUU_i65(tll_ptr A_v38753, tll_ptr xs_v38754);
tll_ptr lenUL_i64(tll_ptr A_v38762, tll_ptr xs_v38763);
tll_ptr lenLL_i62(tll_ptr A_v38771, tll_ptr xs_v38772);
tll_ptr appendUU_i69(tll_ptr A_v38780, tll_ptr xs_v38781, tll_ptr ys_v38782);
tll_ptr appendUL_i68(tll_ptr A_v38791, tll_ptr xs_v38792, tll_ptr ys_v38793);
tll_ptr appendLL_i66(tll_ptr A_v38802, tll_ptr xs_v38803, tll_ptr ys_v38804);
tll_ptr readline_i32(tll_ptr __v38813);
tll_ptr print_i33(tll_ptr s_v38828);
tll_ptr prerr_i34(tll_ptr s_v38839);
tll_ptr get_at_i36(tll_ptr A_v38850, tll_ptr n_v38851, tll_ptr xs_v38852, tll_ptr a_v38853);
tll_ptr string_of_digit_i37(tll_ptr n_v38868);
tll_ptr string_of_nat_i38(tll_ptr n_v38870);
tll_ptr digit_of_char_i39(tll_ptr c_v38874);
tll_ptr nat_of_string_loop_i40(tll_ptr s_v38876, tll_ptr acc_v38877);
tll_ptr nat_of_string_i41(tll_ptr s_v38884);
tll_ptr read_nat_i48(tll_ptr __v38886);
tll_ptr player_loop_i49(tll_ptr ans_v38895, tll_ptr repeat_v38896, tll_ptr c_v38897);
tll_ptr player_i50(tll_ptr c_v38958);
tll_ptr server_loop_i51(tll_ptr ans_v38995, tll_ptr repeat_v38996, tll_ptr c_v38997);
tll_ptr server_i52(tll_ptr c_v39028);

tll_ptr addnclo_i81;
tll_ptr and_thenLLLclo_i97;
tll_ptr and_thenLULclo_i96;
tll_ptr and_thenULLclo_i95;
tll_ptr and_thenULUclo_i94;
tll_ptr and_thenUULclo_i93;
tll_ptr and_thenUUUclo_i92;
tll_ptr andbclo_i70;
tll_ptr appendLLclo_i103;
tll_ptr appendULclo_i102;
tll_ptr appendUUclo_i101;
tll_ptr catsclo_i88;
tll_ptr comparebclo_i73;
tll_ptr comparecclo_i87;
tll_ptr comparenclo_i79;
tll_ptr comparesclo_i91;
tll_ptr digit_of_charclo_i110;
tll_ptr digits_i35;
tll_ptr divnclo_i84;
tll_ptr eqcclo_i86;
tll_ptr eqnclo_i78;
tll_ptr eqsclo_i90;
tll_ptr get_atclo_i107;
tll_ptr gtenclo_i75;
tll_ptr gtnclo_i77;
tll_ptr lenLLclo_i100;
tll_ptr lenULclo_i99;
tll_ptr lenUUclo_i98;
tll_ptr ltenclo_i74;
tll_ptr ltnclo_i76;
tll_ptr modnclo_i85;
tll_ptr mulnclo_i83;
tll_ptr nat_of_string_loopclo_i111;
tll_ptr nat_of_stringclo_i112;
tll_ptr notbclo_i72;
tll_ptr orbclo_i71;
tll_ptr player_loopclo_i114;
tll_ptr playerclo_i115;
tll_ptr predclo_i80;
tll_ptr prerrclo_i106;
tll_ptr printclo_i105;
tll_ptr read_natclo_i113;
tll_ptr readlineclo_i104;
tll_ptr server_loopclo_i116;
tll_ptr serverclo_i117;
tll_ptr string_of_digitclo_i108;
tll_ptr string_of_natclo_i109;
tll_ptr strlenclo_i89;
tll_ptr subnclo_i82;

tll_ptr andb_i1(tll_ptr b1_v38542, tll_ptr b2_v38543) {
  tll_ptr ifte_ret_t1;
  if (b1_v38542) {
    ifte_ret_t1 = b2_v38543;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v38546, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v38546);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v38544, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v38544);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v38547, tll_ptr b2_v38548) {
  tll_ptr ifte_ret_t7;
  if (b1_v38547) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v38548;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v38551, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v38551);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v38549, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v38549);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v38552) {
  tll_ptr ifte_ret_t13;
  if (b_v38552) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v38553, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v38553);
  return call_ret_t14;
}

tll_ptr compareb_i4(tll_ptr b1_v38554, tll_ptr b2_v38555) {
  tll_ptr EQ_t17; tll_ptr EQ_t21; tll_ptr GT_t18; tll_ptr LT_t20;
  tll_ptr ifte_ret_t19; tll_ptr ifte_ret_t22; tll_ptr ifte_ret_t23;
  if (b1_v38554) {
    if (b2_v38555) {
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
    if (b2_v38555) {
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

tll_ptr lam_fun_t25(tll_ptr b2_v38558, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = compareb_i4(env[0], b2_v38558);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr b1_v38556, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, b1_v38556);
  return lam_clo_t26;
}

tll_ptr lten_i5(tll_ptr x_v38559, tll_ptr y_v38560) {
  tll_ptr lten_ret_t29;
  instr_lten(&lten_ret_t29, x_v38559, y_v38560);
  return lten_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v38563, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = lten_i5(env[0], y_v38563);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v38561, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v38561);
  return lam_clo_t32;
}

tll_ptr gten_i6(tll_ptr x_v38564, tll_ptr y_v38565) {
  tll_ptr gten_ret_t35;
  instr_gten(&gten_ret_t35, x_v38564, y_v38565);
  return gten_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v38568, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = gten_i6(env[0], y_v38568);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v38566, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v38566);
  return lam_clo_t38;
}

tll_ptr ltn_i7(tll_ptr x_v38569, tll_ptr y_v38570) {
  tll_ptr ltn_ret_t41;
  instr_ltn(&ltn_ret_t41, x_v38569, y_v38570);
  return ltn_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v38573, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = ltn_i7(env[0], y_v38573);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v38571, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v38571);
  return lam_clo_t44;
}

tll_ptr gtn_i8(tll_ptr x_v38574, tll_ptr y_v38575) {
  tll_ptr gtn_ret_t47;
  instr_gtn(&gtn_ret_t47, x_v38574, y_v38575);
  return gtn_ret_t47;
}

tll_ptr lam_fun_t49(tll_ptr y_v38578, tll_env env) {
  tll_ptr call_ret_t48;
  call_ret_t48 = gtn_i8(env[0], y_v38578);
  return call_ret_t48;
}

tll_ptr lam_fun_t51(tll_ptr x_v38576, tll_env env) {
  tll_ptr lam_clo_t50;
  instr_clo(&lam_clo_t50, &lam_fun_t49, 1, x_v38576);
  return lam_clo_t50;
}

tll_ptr eqn_i9(tll_ptr x_v38579, tll_ptr y_v38580) {
  tll_ptr eqn_ret_t53;
  instr_eqn(&eqn_ret_t53, x_v38579, y_v38580);
  return eqn_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v38583, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = eqn_i9(env[0], y_v38583);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v38581, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v38581);
  return lam_clo_t56;
}

tll_ptr comparen_i10(tll_ptr n1_v38584, tll_ptr n2_v38585) {
  tll_ptr EQ_t65; tll_ptr GT_t62; tll_ptr LT_t64; tll_ptr add_ret_t60;
  tll_ptr add_ret_t61; tll_ptr call_ret_t59; tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t66; tll_ptr ifte_ret_t67;
  if (n1_v38584) {
    if (n2_v38585) {
      add_ret_t60 = n1_v38584 - 1;
      add_ret_t61 = n2_v38585 - 1;
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
    if (n2_v38585) {
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

tll_ptr lam_fun_t69(tll_ptr n2_v38588, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = comparen_i10(env[0], n2_v38588);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr n1_v38586, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, n1_v38586);
  return lam_clo_t70;
}

tll_ptr pred_i11(tll_ptr x_v38589) {
  tll_ptr add_ret_t73; tll_ptr ifte_ret_t74;
  if (x_v38589) {
    add_ret_t73 = x_v38589 - 1;
    ifte_ret_t74 = add_ret_t73;
  }
  else {
    ifte_ret_t74 = (tll_ptr)0;
  }
  return ifte_ret_t74;
}

tll_ptr lam_fun_t76(tll_ptr x_v38590, tll_env env) {
  tll_ptr call_ret_t75;
  call_ret_t75 = pred_i11(x_v38590);
  return call_ret_t75;
}

tll_ptr addn_i12(tll_ptr x_v38591, tll_ptr y_v38592) {
  tll_ptr addn_ret_t78;
  instr_addn(&addn_ret_t78, x_v38591, y_v38592);
  return addn_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v38595, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i12(env[0], y_v38595);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v38593, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v38593);
  return lam_clo_t81;
}

tll_ptr subn_i13(tll_ptr x_v38596, tll_ptr y_v38597) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v38597) {
    call_ret_t85 = pred_i11(x_v38596);
    add_ret_t86 = y_v38597 - 1;
    call_ret_t84 = subn_i13(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v38596;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v38600, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i13(env[0], y_v38600);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v38598, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v38598);
  return lam_clo_t90;
}

tll_ptr muln_i14(tll_ptr x_v38601, tll_ptr y_v38602) {
  tll_ptr muln_ret_t93;
  instr_muln(&muln_ret_t93, x_v38601, y_v38602);
  return muln_ret_t93;
}

tll_ptr lam_fun_t95(tll_ptr y_v38605, tll_env env) {
  tll_ptr call_ret_t94;
  call_ret_t94 = muln_i14(env[0], y_v38605);
  return call_ret_t94;
}

tll_ptr lam_fun_t97(tll_ptr x_v38603, tll_env env) {
  tll_ptr lam_clo_t96;
  instr_clo(&lam_clo_t96, &lam_fun_t95, 1, x_v38603);
  return lam_clo_t96;
}

tll_ptr divn_i15(tll_ptr x_v38606, tll_ptr y_v38607) {
  tll_ptr divn_ret_t99;
  instr_divn(&divn_ret_t99, x_v38606, y_v38607);
  return divn_ret_t99;
}

tll_ptr lam_fun_t101(tll_ptr y_v38610, tll_env env) {
  tll_ptr call_ret_t100;
  call_ret_t100 = divn_i15(env[0], y_v38610);
  return call_ret_t100;
}

tll_ptr lam_fun_t103(tll_ptr x_v38608, tll_env env) {
  tll_ptr lam_clo_t102;
  instr_clo(&lam_clo_t102, &lam_fun_t101, 1, x_v38608);
  return lam_clo_t102;
}

tll_ptr modn_i16(tll_ptr x_v38611, tll_ptr y_v38612) {
  tll_ptr modn_ret_t105;
  instr_modn(&modn_ret_t105, x_v38611, y_v38612);
  return modn_ret_t105;
}

tll_ptr lam_fun_t107(tll_ptr y_v38615, tll_env env) {
  tll_ptr call_ret_t106;
  call_ret_t106 = modn_i16(env[0], y_v38615);
  return call_ret_t106;
}

tll_ptr lam_fun_t109(tll_ptr x_v38613, tll_env env) {
  tll_ptr lam_clo_t108;
  instr_clo(&lam_clo_t108, &lam_fun_t107, 1, x_v38613);
  return lam_clo_t108;
}

tll_ptr eqc_i17(tll_ptr c1_v38616, tll_ptr c2_v38617) {
  tll_ptr call_ret_t113; tll_ptr n1_v38618; tll_ptr n2_v38619;
  tll_ptr switch_ret_t111; tll_ptr switch_ret_t112;
  switch(((tll_node)c1_v38616)->tag) {
    case 5:
      n1_v38618 = ((tll_node)c1_v38616)->data[0];
      switch(((tll_node)c2_v38617)->tag) {
        case 5:
          n2_v38619 = ((tll_node)c2_v38617)->data[0];
          call_ret_t113 = eqn_i9(n1_v38618, n2_v38619);
          switch_ret_t112 = call_ret_t113;
          break;
      }
      switch_ret_t111 = switch_ret_t112;
      break;
  }
  return switch_ret_t111;
}

tll_ptr lam_fun_t115(tll_ptr c2_v38622, tll_env env) {
  tll_ptr call_ret_t114;
  call_ret_t114 = eqc_i17(env[0], c2_v38622);
  return call_ret_t114;
}

tll_ptr lam_fun_t117(tll_ptr c1_v38620, tll_env env) {
  tll_ptr lam_clo_t116;
  instr_clo(&lam_clo_t116, &lam_fun_t115, 1, c1_v38620);
  return lam_clo_t116;
}

tll_ptr comparec_i18(tll_ptr c1_v38623, tll_ptr c2_v38624) {
  tll_ptr call_ret_t121; tll_ptr n1_v38625; tll_ptr n2_v38626;
  tll_ptr switch_ret_t119; tll_ptr switch_ret_t120;
  switch(((tll_node)c1_v38623)->tag) {
    case 5:
      n1_v38625 = ((tll_node)c1_v38623)->data[0];
      switch(((tll_node)c2_v38624)->tag) {
        case 5:
          n2_v38626 = ((tll_node)c2_v38624)->data[0];
          call_ret_t121 = comparen_i10(n1_v38625, n2_v38626);
          switch_ret_t120 = call_ret_t121;
          break;
      }
      switch_ret_t119 = switch_ret_t120;
      break;
  }
  return switch_ret_t119;
}

tll_ptr lam_fun_t123(tll_ptr c2_v38629, tll_env env) {
  tll_ptr call_ret_t122;
  call_ret_t122 = comparec_i18(env[0], c2_v38629);
  return call_ret_t122;
}

tll_ptr lam_fun_t125(tll_ptr c1_v38627, tll_env env) {
  tll_ptr lam_clo_t124;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 1, c1_v38627);
  return lam_clo_t124;
}

tll_ptr cats_i19(tll_ptr s1_v38630, tll_ptr s2_v38631) {
  tll_ptr String_t129; tll_ptr c_v38632; tll_ptr call_ret_t128;
  tll_ptr s1_v38633; tll_ptr switch_ret_t127;
  switch(((tll_node)s1_v38630)->tag) {
    case 6:
      switch_ret_t127 = s2_v38631;
      break;
    case 7:
      c_v38632 = ((tll_node)s1_v38630)->data[0];
      s1_v38633 = ((tll_node)s1_v38630)->data[1];
      call_ret_t128 = cats_i19(s1_v38633, s2_v38631);
      instr_struct(&String_t129, 7, 2, c_v38632, call_ret_t128);
      switch_ret_t127 = String_t129;
      break;
  }
  return switch_ret_t127;
}

tll_ptr lam_fun_t131(tll_ptr s2_v38636, tll_env env) {
  tll_ptr call_ret_t130;
  call_ret_t130 = cats_i19(env[0], s2_v38636);
  return call_ret_t130;
}

tll_ptr lam_fun_t133(tll_ptr s1_v38634, tll_env env) {
  tll_ptr lam_clo_t132;
  instr_clo(&lam_clo_t132, &lam_fun_t131, 1, s1_v38634);
  return lam_clo_t132;
}

tll_ptr strlen_i20(tll_ptr s_v38637) {
  tll_ptr __v38638; tll_ptr add_ret_t137; tll_ptr call_ret_t136;
  tll_ptr s_v38639; tll_ptr switch_ret_t135;
  switch(((tll_node)s_v38637)->tag) {
    case 6:
      switch_ret_t135 = (tll_ptr)0;
      break;
    case 7:
      __v38638 = ((tll_node)s_v38637)->data[0];
      s_v38639 = ((tll_node)s_v38637)->data[1];
      call_ret_t136 = strlen_i20(s_v38639);
      add_ret_t137 = call_ret_t136 + 1;
      switch_ret_t135 = add_ret_t137;
      break;
  }
  return switch_ret_t135;
}

tll_ptr lam_fun_t139(tll_ptr s_v38640, tll_env env) {
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i20(s_v38640);
  return call_ret_t138;
}

tll_ptr eqs_i21(tll_ptr s1_v38641, tll_ptr s2_v38642) {
  tll_ptr __v38643; tll_ptr __v38644; tll_ptr c1_v38645; tll_ptr c2_v38647;
  tll_ptr call_ret_t144; tll_ptr call_ret_t145; tll_ptr call_ret_t146;
  tll_ptr s1_v38646; tll_ptr s2_v38648; tll_ptr switch_ret_t141;
  tll_ptr switch_ret_t142; tll_ptr switch_ret_t143;
  switch(((tll_node)s1_v38641)->tag) {
    case 6:
      switch(((tll_node)s2_v38642)->tag) {
        case 6:
          switch_ret_t142 = (tll_ptr)1;
          break;
        case 7:
          __v38643 = ((tll_node)s2_v38642)->data[0];
          __v38644 = ((tll_node)s2_v38642)->data[1];
          switch_ret_t142 = (tll_ptr)0;
          break;
      }
      switch_ret_t141 = switch_ret_t142;
      break;
    case 7:
      c1_v38645 = ((tll_node)s1_v38641)->data[0];
      s1_v38646 = ((tll_node)s1_v38641)->data[1];
      switch(((tll_node)s2_v38642)->tag) {
        case 6:
          switch_ret_t143 = (tll_ptr)0;
          break;
        case 7:
          c2_v38647 = ((tll_node)s2_v38642)->data[0];
          s2_v38648 = ((tll_node)s2_v38642)->data[1];
          call_ret_t145 = eqc_i17(c1_v38645, c2_v38647);
          call_ret_t146 = eqs_i21(s1_v38646, s2_v38648);
          call_ret_t144 = andb_i1(call_ret_t145, call_ret_t146);
          switch_ret_t143 = call_ret_t144;
          break;
      }
      switch_ret_t141 = switch_ret_t143;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t148(tll_ptr s2_v38651, tll_env env) {
  tll_ptr call_ret_t147;
  call_ret_t147 = eqs_i21(env[0], s2_v38651);
  return call_ret_t147;
}

tll_ptr lam_fun_t150(tll_ptr s1_v38649, tll_env env) {
  tll_ptr lam_clo_t149;
  instr_clo(&lam_clo_t149, &lam_fun_t148, 1, s1_v38649);
  return lam_clo_t149;
}

tll_ptr compares_i22(tll_ptr s1_v38652, tll_ptr s2_v38653) {
  tll_ptr EQ_t154; tll_ptr GT_t157; tll_ptr GT_t162; tll_ptr LT_t155;
  tll_ptr LT_t161; tll_ptr __v38654; tll_ptr __v38655; tll_ptr c1_v38656;
  tll_ptr c2_v38658; tll_ptr call_ret_t158; tll_ptr call_ret_t160;
  tll_ptr s1_v38657; tll_ptr s2_v38659; tll_ptr switch_ret_t152;
  tll_ptr switch_ret_t153; tll_ptr switch_ret_t156; tll_ptr switch_ret_t159;
  switch(((tll_node)s1_v38652)->tag) {
    case 6:
      switch(((tll_node)s2_v38653)->tag) {
        case 6:
          instr_struct(&EQ_t154, 3, 0);
          switch_ret_t153 = EQ_t154;
          break;
        case 7:
          __v38654 = ((tll_node)s2_v38653)->data[0];
          __v38655 = ((tll_node)s2_v38653)->data[1];
          instr_struct(&LT_t155, 1, 0);
          switch_ret_t153 = LT_t155;
          break;
      }
      switch_ret_t152 = switch_ret_t153;
      break;
    case 7:
      c1_v38656 = ((tll_node)s1_v38652)->data[0];
      s1_v38657 = ((tll_node)s1_v38652)->data[1];
      switch(((tll_node)s2_v38653)->tag) {
        case 6:
          instr_struct(&GT_t157, 2, 0);
          switch_ret_t156 = GT_t157;
          break;
        case 7:
          c2_v38658 = ((tll_node)s2_v38653)->data[0];
          s2_v38659 = ((tll_node)s2_v38653)->data[1];
          call_ret_t158 = comparec_i18(c1_v38656, c2_v38658);
          switch(((tll_node)call_ret_t158)->tag) {
            case 3:
              call_ret_t160 = compares_i22(s1_v38657, s2_v38659);
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

tll_ptr lam_fun_t164(tll_ptr s2_v38662, tll_env env) {
  tll_ptr call_ret_t163;
  call_ret_t163 = compares_i22(env[0], s2_v38662);
  return call_ret_t163;
}

tll_ptr lam_fun_t166(tll_ptr s1_v38660, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, s1_v38660);
  return lam_clo_t165;
}

tll_ptr and_thenUUU_i61(tll_ptr A_v38663, tll_ptr B_v38664, tll_ptr opt_v38665, tll_ptr f_v38666) {
  tll_ptr NoneUU_t169; tll_ptr app_ret_t170; tll_ptr switch_ret_t168;
  tll_ptr x_v38667;
  switch(((tll_node)opt_v38665)->tag) {
    case 18:
      instr_struct(&NoneUU_t169, 18, 0);
      switch_ret_t168 = NoneUU_t169;
      break;
    case 19:
      x_v38667 = ((tll_node)opt_v38665)->data[0];
      instr_app(&app_ret_t170, f_v38666, x_v38667);
      switch_ret_t168 = app_ret_t170;
      break;
  }
  return switch_ret_t168;
}

tll_ptr lam_fun_t172(tll_ptr f_v38677, tll_env env) {
  tll_ptr call_ret_t171;
  call_ret_t171 = and_thenUUU_i61(env[2], env[1], env[0], f_v38677);
  return call_ret_t171;
}

tll_ptr lam_fun_t174(tll_ptr opt_v38675, tll_env env) {
  tll_ptr lam_clo_t173;
  instr_clo(&lam_clo_t173, &lam_fun_t172, 3, opt_v38675, env[0], env[1]);
  return lam_clo_t173;
}

tll_ptr lam_fun_t176(tll_ptr B_v38672, tll_env env) {
  tll_ptr lam_clo_t175;
  instr_clo(&lam_clo_t175, &lam_fun_t174, 2, B_v38672, env[0]);
  return lam_clo_t175;
}

tll_ptr lam_fun_t178(tll_ptr A_v38668, tll_env env) {
  tll_ptr lam_clo_t177;
  instr_clo(&lam_clo_t177, &lam_fun_t176, 1, A_v38668);
  return lam_clo_t177;
}

tll_ptr and_thenUUL_i60(tll_ptr A_v38678, tll_ptr B_v38679, tll_ptr opt_v38680, tll_ptr f_v38681) {
  tll_ptr NoneUL_t181; tll_ptr app_ret_t182; tll_ptr switch_ret_t180;
  tll_ptr x_v38682;
  switch(((tll_node)opt_v38680)->tag) {
    case 16:
      instr_free_struct(opt_v38680);
      instr_struct(&NoneUL_t181, 16, 0);
      switch_ret_t180 = NoneUL_t181;
      break;
    case 17:
      x_v38682 = ((tll_node)opt_v38680)->data[0];
      instr_free_struct(opt_v38680);
      instr_app(&app_ret_t182, f_v38681, x_v38682);
      switch_ret_t180 = app_ret_t182;
      break;
  }
  return switch_ret_t180;
}

tll_ptr lam_fun_t184(tll_ptr f_v38692, tll_env env) {
  tll_ptr call_ret_t183;
  call_ret_t183 = and_thenUUL_i60(env[2], env[1], env[0], f_v38692);
  return call_ret_t183;
}

tll_ptr lam_fun_t186(tll_ptr opt_v38690, tll_env env) {
  tll_ptr lam_clo_t185;
  instr_clo(&lam_clo_t185, &lam_fun_t184, 3, opt_v38690, env[0], env[1]);
  return lam_clo_t185;
}

tll_ptr lam_fun_t188(tll_ptr B_v38687, tll_env env) {
  tll_ptr lam_clo_t187;
  instr_clo(&lam_clo_t187, &lam_fun_t186, 2, B_v38687, env[0]);
  return lam_clo_t187;
}

tll_ptr lam_fun_t190(tll_ptr A_v38683, tll_env env) {
  tll_ptr lam_clo_t189;
  instr_clo(&lam_clo_t189, &lam_fun_t188, 1, A_v38683);
  return lam_clo_t189;
}

tll_ptr and_thenULU_i59(tll_ptr A_v38693, tll_ptr B_v38694, tll_ptr opt_v38695, tll_ptr f_v38696) {
  tll_ptr NoneLU_t193; tll_ptr app_ret_t194; tll_ptr switch_ret_t192;
  tll_ptr x_v38697;
  switch(((tll_node)opt_v38695)->tag) {
    case 18:
      instr_struct(&NoneLU_t193, 14, 0);
      switch_ret_t192 = NoneLU_t193;
      break;
    case 19:
      x_v38697 = ((tll_node)opt_v38695)->data[0];
      instr_app(&app_ret_t194, f_v38696, x_v38697);
      switch_ret_t192 = app_ret_t194;
      break;
  }
  return switch_ret_t192;
}

tll_ptr lam_fun_t196(tll_ptr f_v38707, tll_env env) {
  tll_ptr call_ret_t195;
  call_ret_t195 = and_thenULU_i59(env[2], env[1], env[0], f_v38707);
  return call_ret_t195;
}

tll_ptr lam_fun_t198(tll_ptr opt_v38705, tll_env env) {
  tll_ptr lam_clo_t197;
  instr_clo(&lam_clo_t197, &lam_fun_t196, 3, opt_v38705, env[0], env[1]);
  return lam_clo_t197;
}

tll_ptr lam_fun_t200(tll_ptr B_v38702, tll_env env) {
  tll_ptr lam_clo_t199;
  instr_clo(&lam_clo_t199, &lam_fun_t198, 2, B_v38702, env[0]);
  return lam_clo_t199;
}

tll_ptr lam_fun_t202(tll_ptr A_v38698, tll_env env) {
  tll_ptr lam_clo_t201;
  instr_clo(&lam_clo_t201, &lam_fun_t200, 1, A_v38698);
  return lam_clo_t201;
}

tll_ptr and_thenULL_i58(tll_ptr A_v38708, tll_ptr B_v38709, tll_ptr opt_v38710, tll_ptr f_v38711) {
  tll_ptr NoneLL_t205; tll_ptr app_ret_t206; tll_ptr switch_ret_t204;
  tll_ptr x_v38712;
  switch(((tll_node)opt_v38710)->tag) {
    case 16:
      instr_free_struct(opt_v38710);
      instr_struct(&NoneLL_t205, 12, 0);
      switch_ret_t204 = NoneLL_t205;
      break;
    case 17:
      x_v38712 = ((tll_node)opt_v38710)->data[0];
      instr_free_struct(opt_v38710);
      instr_app(&app_ret_t206, f_v38711, x_v38712);
      switch_ret_t204 = app_ret_t206;
      break;
  }
  return switch_ret_t204;
}

tll_ptr lam_fun_t208(tll_ptr f_v38722, tll_env env) {
  tll_ptr call_ret_t207;
  call_ret_t207 = and_thenULL_i58(env[2], env[1], env[0], f_v38722);
  return call_ret_t207;
}

tll_ptr lam_fun_t210(tll_ptr opt_v38720, tll_env env) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 3, opt_v38720, env[0], env[1]);
  return lam_clo_t209;
}

tll_ptr lam_fun_t212(tll_ptr B_v38717, tll_env env) {
  tll_ptr lam_clo_t211;
  instr_clo(&lam_clo_t211, &lam_fun_t210, 2, B_v38717, env[0]);
  return lam_clo_t211;
}

tll_ptr lam_fun_t214(tll_ptr A_v38713, tll_env env) {
  tll_ptr lam_clo_t213;
  instr_clo(&lam_clo_t213, &lam_fun_t212, 1, A_v38713);
  return lam_clo_t213;
}

tll_ptr and_thenLUL_i56(tll_ptr A_v38723, tll_ptr B_v38724, tll_ptr opt_v38725, tll_ptr f_v38726) {
  tll_ptr NoneUL_t217; tll_ptr app_ret_t218; tll_ptr switch_ret_t216;
  tll_ptr x_v38727;
  switch(((tll_node)opt_v38725)->tag) {
    case 12:
      instr_free_struct(opt_v38725);
      instr_struct(&NoneUL_t217, 16, 0);
      switch_ret_t216 = NoneUL_t217;
      break;
    case 13:
      x_v38727 = ((tll_node)opt_v38725)->data[0];
      instr_free_struct(opt_v38725);
      instr_app(&app_ret_t218, f_v38726, x_v38727);
      switch_ret_t216 = app_ret_t218;
      break;
  }
  return switch_ret_t216;
}

tll_ptr lam_fun_t220(tll_ptr f_v38737, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = and_thenLUL_i56(env[2], env[1], env[0], f_v38737);
  return call_ret_t219;
}

tll_ptr lam_fun_t222(tll_ptr opt_v38735, tll_env env) {
  tll_ptr lam_clo_t221;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 3, opt_v38735, env[0], env[1]);
  return lam_clo_t221;
}

tll_ptr lam_fun_t224(tll_ptr B_v38732, tll_env env) {
  tll_ptr lam_clo_t223;
  instr_clo(&lam_clo_t223, &lam_fun_t222, 2, B_v38732, env[0]);
  return lam_clo_t223;
}

tll_ptr lam_fun_t226(tll_ptr A_v38728, tll_env env) {
  tll_ptr lam_clo_t225;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 1, A_v38728);
  return lam_clo_t225;
}

tll_ptr and_thenLLL_i54(tll_ptr A_v38738, tll_ptr B_v38739, tll_ptr opt_v38740, tll_ptr f_v38741) {
  tll_ptr NoneLL_t229; tll_ptr app_ret_t230; tll_ptr switch_ret_t228;
  tll_ptr x_v38742;
  switch(((tll_node)opt_v38740)->tag) {
    case 12:
      instr_free_struct(opt_v38740);
      instr_struct(&NoneLL_t229, 12, 0);
      switch_ret_t228 = NoneLL_t229;
      break;
    case 13:
      x_v38742 = ((tll_node)opt_v38740)->data[0];
      instr_free_struct(opt_v38740);
      instr_app(&app_ret_t230, f_v38741, x_v38742);
      switch_ret_t228 = app_ret_t230;
      break;
  }
  return switch_ret_t228;
}

tll_ptr lam_fun_t232(tll_ptr f_v38752, tll_env env) {
  tll_ptr call_ret_t231;
  call_ret_t231 = and_thenLLL_i54(env[2], env[1], env[0], f_v38752);
  return call_ret_t231;
}

tll_ptr lam_fun_t234(tll_ptr opt_v38750, tll_env env) {
  tll_ptr lam_clo_t233;
  instr_clo(&lam_clo_t233, &lam_fun_t232, 3, opt_v38750, env[0], env[1]);
  return lam_clo_t233;
}

tll_ptr lam_fun_t236(tll_ptr B_v38747, tll_env env) {
  tll_ptr lam_clo_t235;
  instr_clo(&lam_clo_t235, &lam_fun_t234, 2, B_v38747, env[0]);
  return lam_clo_t235;
}

tll_ptr lam_fun_t238(tll_ptr A_v38743, tll_env env) {
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, A_v38743);
  return lam_clo_t237;
}

tll_ptr lenUU_i65(tll_ptr A_v38753, tll_ptr xs_v38754) {
  tll_ptr add_ret_t245; tll_ptr call_ret_t243; tll_ptr consUU_t246;
  tll_ptr n_v38757; tll_ptr nilUU_t241; tll_ptr pair_struct_t242;
  tll_ptr pair_struct_t247; tll_ptr switch_ret_t240; tll_ptr switch_ret_t244;
  tll_ptr x_v38755; tll_ptr xs_v38756; tll_ptr xs_v38758;
  switch(((tll_node)xs_v38754)->tag) {
    case 26:
      instr_struct(&nilUU_t241, 26, 0);
      instr_struct(&pair_struct_t242, 0, 2, (tll_ptr)0, nilUU_t241);
      switch_ret_t240 = pair_struct_t242;
      break;
    case 27:
      x_v38755 = ((tll_node)xs_v38754)->data[0];
      xs_v38756 = ((tll_node)xs_v38754)->data[1];
      call_ret_t243 = lenUU_i65(0, xs_v38756);
      switch(((tll_node)call_ret_t243)->tag) {
        case 0:
          n_v38757 = ((tll_node)call_ret_t243)->data[0];
          xs_v38758 = ((tll_node)call_ret_t243)->data[1];
          instr_free_struct(call_ret_t243);
          add_ret_t245 = n_v38757 + 1;
          instr_struct(&consUU_t246, 27, 2, x_v38755, xs_v38758);
          instr_struct(&pair_struct_t247, 0, 2, add_ret_t245, consUU_t246);
          switch_ret_t244 = pair_struct_t247;
          break;
      }
      switch_ret_t240 = switch_ret_t244;
      break;
  }
  return switch_ret_t240;
}

tll_ptr lam_fun_t249(tll_ptr xs_v38761, tll_env env) {
  tll_ptr call_ret_t248;
  call_ret_t248 = lenUU_i65(env[0], xs_v38761);
  return call_ret_t248;
}

tll_ptr lam_fun_t251(tll_ptr A_v38759, tll_env env) {
  tll_ptr lam_clo_t250;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 1, A_v38759);
  return lam_clo_t250;
}

tll_ptr lenUL_i64(tll_ptr A_v38762, tll_ptr xs_v38763) {
  tll_ptr add_ret_t258; tll_ptr call_ret_t256; tll_ptr consUL_t259;
  tll_ptr n_v38766; tll_ptr nilUL_t254; tll_ptr pair_struct_t255;
  tll_ptr pair_struct_t260; tll_ptr switch_ret_t253; tll_ptr switch_ret_t257;
  tll_ptr x_v38764; tll_ptr xs_v38765; tll_ptr xs_v38767;
  switch(((tll_node)xs_v38763)->tag) {
    case 24:
      instr_free_struct(xs_v38763);
      instr_struct(&nilUL_t254, 24, 0);
      instr_struct(&pair_struct_t255, 0, 2, (tll_ptr)0, nilUL_t254);
      switch_ret_t253 = pair_struct_t255;
      break;
    case 25:
      x_v38764 = ((tll_node)xs_v38763)->data[0];
      xs_v38765 = ((tll_node)xs_v38763)->data[1];
      instr_free_struct(xs_v38763);
      call_ret_t256 = lenUL_i64(0, xs_v38765);
      switch(((tll_node)call_ret_t256)->tag) {
        case 0:
          n_v38766 = ((tll_node)call_ret_t256)->data[0];
          xs_v38767 = ((tll_node)call_ret_t256)->data[1];
          instr_free_struct(call_ret_t256);
          add_ret_t258 = n_v38766 + 1;
          instr_struct(&consUL_t259, 25, 2, x_v38764, xs_v38767);
          instr_struct(&pair_struct_t260, 0, 2, add_ret_t258, consUL_t259);
          switch_ret_t257 = pair_struct_t260;
          break;
      }
      switch_ret_t253 = switch_ret_t257;
      break;
  }
  return switch_ret_t253;
}

tll_ptr lam_fun_t262(tll_ptr xs_v38770, tll_env env) {
  tll_ptr call_ret_t261;
  call_ret_t261 = lenUL_i64(env[0], xs_v38770);
  return call_ret_t261;
}

tll_ptr lam_fun_t264(tll_ptr A_v38768, tll_env env) {
  tll_ptr lam_clo_t263;
  instr_clo(&lam_clo_t263, &lam_fun_t262, 1, A_v38768);
  return lam_clo_t263;
}

tll_ptr lenLL_i62(tll_ptr A_v38771, tll_ptr xs_v38772) {
  tll_ptr add_ret_t271; tll_ptr call_ret_t269; tll_ptr consLL_t272;
  tll_ptr n_v38775; tll_ptr nilLL_t267; tll_ptr pair_struct_t268;
  tll_ptr pair_struct_t273; tll_ptr switch_ret_t266; tll_ptr switch_ret_t270;
  tll_ptr x_v38773; tll_ptr xs_v38774; tll_ptr xs_v38776;
  switch(((tll_node)xs_v38772)->tag) {
    case 20:
      instr_free_struct(xs_v38772);
      instr_struct(&nilLL_t267, 20, 0);
      instr_struct(&pair_struct_t268, 0, 2, (tll_ptr)0, nilLL_t267);
      switch_ret_t266 = pair_struct_t268;
      break;
    case 21:
      x_v38773 = ((tll_node)xs_v38772)->data[0];
      xs_v38774 = ((tll_node)xs_v38772)->data[1];
      instr_free_struct(xs_v38772);
      call_ret_t269 = lenLL_i62(0, xs_v38774);
      switch(((tll_node)call_ret_t269)->tag) {
        case 0:
          n_v38775 = ((tll_node)call_ret_t269)->data[0];
          xs_v38776 = ((tll_node)call_ret_t269)->data[1];
          instr_free_struct(call_ret_t269);
          add_ret_t271 = n_v38775 + 1;
          instr_struct(&consLL_t272, 21, 2, x_v38773, xs_v38776);
          instr_struct(&pair_struct_t273, 0, 2, add_ret_t271, consLL_t272);
          switch_ret_t270 = pair_struct_t273;
          break;
      }
      switch_ret_t266 = switch_ret_t270;
      break;
  }
  return switch_ret_t266;
}

tll_ptr lam_fun_t275(tll_ptr xs_v38779, tll_env env) {
  tll_ptr call_ret_t274;
  call_ret_t274 = lenLL_i62(env[0], xs_v38779);
  return call_ret_t274;
}

tll_ptr lam_fun_t277(tll_ptr A_v38777, tll_env env) {
  tll_ptr lam_clo_t276;
  instr_clo(&lam_clo_t276, &lam_fun_t275, 1, A_v38777);
  return lam_clo_t276;
}

tll_ptr appendUU_i69(tll_ptr A_v38780, tll_ptr xs_v38781, tll_ptr ys_v38782) {
  tll_ptr call_ret_t280; tll_ptr consUU_t281; tll_ptr switch_ret_t279;
  tll_ptr x_v38783; tll_ptr xs_v38784;
  switch(((tll_node)xs_v38781)->tag) {
    case 26:
      switch_ret_t279 = ys_v38782;
      break;
    case 27:
      x_v38783 = ((tll_node)xs_v38781)->data[0];
      xs_v38784 = ((tll_node)xs_v38781)->data[1];
      call_ret_t280 = appendUU_i69(0, xs_v38784, ys_v38782);
      instr_struct(&consUU_t281, 27, 2, x_v38783, call_ret_t280);
      switch_ret_t279 = consUU_t281;
      break;
  }
  return switch_ret_t279;
}

tll_ptr lam_fun_t283(tll_ptr ys_v38790, tll_env env) {
  tll_ptr call_ret_t282;
  call_ret_t282 = appendUU_i69(env[1], env[0], ys_v38790);
  return call_ret_t282;
}

tll_ptr lam_fun_t285(tll_ptr xs_v38788, tll_env env) {
  tll_ptr lam_clo_t284;
  instr_clo(&lam_clo_t284, &lam_fun_t283, 2, xs_v38788, env[0]);
  return lam_clo_t284;
}

tll_ptr lam_fun_t287(tll_ptr A_v38785, tll_env env) {
  tll_ptr lam_clo_t286;
  instr_clo(&lam_clo_t286, &lam_fun_t285, 1, A_v38785);
  return lam_clo_t286;
}

tll_ptr appendUL_i68(tll_ptr A_v38791, tll_ptr xs_v38792, tll_ptr ys_v38793) {
  tll_ptr call_ret_t290; tll_ptr consUL_t291; tll_ptr switch_ret_t289;
  tll_ptr x_v38794; tll_ptr xs_v38795;
  switch(((tll_node)xs_v38792)->tag) {
    case 24:
      instr_free_struct(xs_v38792);
      switch_ret_t289 = ys_v38793;
      break;
    case 25:
      x_v38794 = ((tll_node)xs_v38792)->data[0];
      xs_v38795 = ((tll_node)xs_v38792)->data[1];
      instr_free_struct(xs_v38792);
      call_ret_t290 = appendUL_i68(0, xs_v38795, ys_v38793);
      instr_struct(&consUL_t291, 25, 2, x_v38794, call_ret_t290);
      switch_ret_t289 = consUL_t291;
      break;
  }
  return switch_ret_t289;
}

tll_ptr lam_fun_t293(tll_ptr ys_v38801, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = appendUL_i68(env[1], env[0], ys_v38801);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v38799, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 2, xs_v38799, env[0]);
  return lam_clo_t294;
}

tll_ptr lam_fun_t297(tll_ptr A_v38796, tll_env env) {
  tll_ptr lam_clo_t296;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 1, A_v38796);
  return lam_clo_t296;
}

tll_ptr appendLL_i66(tll_ptr A_v38802, tll_ptr xs_v38803, tll_ptr ys_v38804) {
  tll_ptr call_ret_t300; tll_ptr consLL_t301; tll_ptr switch_ret_t299;
  tll_ptr x_v38805; tll_ptr xs_v38806;
  switch(((tll_node)xs_v38803)->tag) {
    case 20:
      instr_free_struct(xs_v38803);
      switch_ret_t299 = ys_v38804;
      break;
    case 21:
      x_v38805 = ((tll_node)xs_v38803)->data[0];
      xs_v38806 = ((tll_node)xs_v38803)->data[1];
      instr_free_struct(xs_v38803);
      call_ret_t300 = appendLL_i66(0, xs_v38806, ys_v38804);
      instr_struct(&consLL_t301, 21, 2, x_v38805, call_ret_t300);
      switch_ret_t299 = consLL_t301;
      break;
  }
  return switch_ret_t299;
}

tll_ptr lam_fun_t303(tll_ptr ys_v38812, tll_env env) {
  tll_ptr call_ret_t302;
  call_ret_t302 = appendLL_i66(env[1], env[0], ys_v38812);
  return call_ret_t302;
}

tll_ptr lam_fun_t305(tll_ptr xs_v38810, tll_env env) {
  tll_ptr lam_clo_t304;
  instr_clo(&lam_clo_t304, &lam_fun_t303, 2, xs_v38810, env[0]);
  return lam_clo_t304;
}

tll_ptr lam_fun_t307(tll_ptr A_v38807, tll_env env) {
  tll_ptr lam_clo_t306;
  instr_clo(&lam_clo_t306, &lam_fun_t305, 1, A_v38807);
  return lam_clo_t306;
}

tll_ptr lam_fun_t314(tll_ptr __v38814, tll_env env) {
  tll_ptr __v38823; tll_ptr ch_v38821; tll_ptr ch_v38822; tll_ptr ch_v38825;
  tll_ptr ch_v38826; tll_ptr prim_ch_t309; tll_ptr recv_msg_t311;
  tll_ptr s_v38824; tll_ptr send_ch_t310; tll_ptr send_ch_t313;
  tll_ptr switch_ret_t312;
  instr_open(&prim_ch_t309, &proc_stdin);
  ch_v38821 = prim_ch_t309;
  instr_send(&send_ch_t310, ch_v38821, (tll_ptr)1);
  ch_v38822 = send_ch_t310;
  instr_recv(&recv_msg_t311, ch_v38822);
  __v38823 = recv_msg_t311;
  switch(((tll_node)__v38823)->tag) {
    case 0:
      s_v38824 = ((tll_node)__v38823)->data[0];
      ch_v38825 = ((tll_node)__v38823)->data[1];
      instr_free_struct(__v38823);
      instr_send(&send_ch_t313, ch_v38825, (tll_ptr)0);
      ch_v38826 = send_ch_t313;
      switch_ret_t312 = s_v38824;
      break;
  }
  return switch_ret_t312;
}

tll_ptr readline_i32(tll_ptr __v38813) {
  tll_ptr lam_clo_t315;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 0);
  return lam_clo_t315;
}

tll_ptr lam_fun_t317(tll_ptr __v38827, tll_env env) {
  tll_ptr call_ret_t316;
  call_ret_t316 = readline_i32(__v38827);
  return call_ret_t316;
}

tll_ptr lam_fun_t323(tll_ptr __v38829, tll_env env) {
  tll_ptr ch_v38834; tll_ptr ch_v38835; tll_ptr ch_v38836; tll_ptr ch_v38837;
  tll_ptr prim_ch_t319; tll_ptr send_ch_t320; tll_ptr send_ch_t321;
  tll_ptr send_ch_t322;
  instr_open(&prim_ch_t319, &proc_stdout);
  ch_v38834 = prim_ch_t319;
  instr_send(&send_ch_t320, ch_v38834, (tll_ptr)1);
  ch_v38835 = send_ch_t320;
  instr_send(&send_ch_t321, ch_v38835, env[0]);
  ch_v38836 = send_ch_t321;
  instr_send(&send_ch_t322, ch_v38836, (tll_ptr)0);
  ch_v38837 = send_ch_t322;
  return 0;
}

tll_ptr print_i33(tll_ptr s_v38828) {
  tll_ptr lam_clo_t324;
  instr_clo(&lam_clo_t324, &lam_fun_t323, 1, s_v38828);
  return lam_clo_t324;
}

tll_ptr lam_fun_t326(tll_ptr s_v38838, tll_env env) {
  tll_ptr call_ret_t325;
  call_ret_t325 = print_i33(s_v38838);
  return call_ret_t325;
}

tll_ptr lam_fun_t332(tll_ptr __v38840, tll_env env) {
  tll_ptr ch_v38845; tll_ptr ch_v38846; tll_ptr ch_v38847; tll_ptr ch_v38848;
  tll_ptr prim_ch_t328; tll_ptr send_ch_t329; tll_ptr send_ch_t330;
  tll_ptr send_ch_t331;
  instr_open(&prim_ch_t328, &proc_stderr);
  ch_v38845 = prim_ch_t328;
  instr_send(&send_ch_t329, ch_v38845, (tll_ptr)1);
  ch_v38846 = send_ch_t329;
  instr_send(&send_ch_t330, ch_v38846, env[0]);
  ch_v38847 = send_ch_t330;
  instr_send(&send_ch_t331, ch_v38847, (tll_ptr)0);
  ch_v38848 = send_ch_t331;
  return 0;
}

tll_ptr prerr_i34(tll_ptr s_v38839) {
  tll_ptr lam_clo_t333;
  instr_clo(&lam_clo_t333, &lam_fun_t332, 1, s_v38839);
  return lam_clo_t333;
}

tll_ptr lam_fun_t335(tll_ptr s_v38849, tll_env env) {
  tll_ptr call_ret_t334;
  call_ret_t334 = prerr_i34(s_v38849);
  return call_ret_t334;
}

tll_ptr get_at_i36(tll_ptr A_v38850, tll_ptr n_v38851, tll_ptr xs_v38852, tll_ptr a_v38853) {
  tll_ptr __v38854; tll_ptr __v38857; tll_ptr add_ret_t380;
  tll_ptr call_ret_t379; tll_ptr ifte_ret_t382; tll_ptr switch_ret_t378;
  tll_ptr switch_ret_t381; tll_ptr x_v38856; tll_ptr xs_v38855;
  if (n_v38851) {
    switch(((tll_node)xs_v38852)->tag) {
      case 26:
        switch_ret_t378 = a_v38853;
        break;
      case 27:
        __v38854 = ((tll_node)xs_v38852)->data[0];
        xs_v38855 = ((tll_node)xs_v38852)->data[1];
        add_ret_t380 = n_v38851 - 1;
        call_ret_t379 = get_at_i36(0, add_ret_t380, xs_v38855, a_v38853);
        switch_ret_t378 = call_ret_t379;
        break;
    }
    ifte_ret_t382 = switch_ret_t378;
  }
  else {
    switch(((tll_node)xs_v38852)->tag) {
      case 26:
        switch_ret_t381 = a_v38853;
        break;
      case 27:
        x_v38856 = ((tll_node)xs_v38852)->data[0];
        __v38857 = ((tll_node)xs_v38852)->data[1];
        switch_ret_t381 = x_v38856;
        break;
    }
    ifte_ret_t382 = switch_ret_t381;
  }
  return ifte_ret_t382;
}

tll_ptr lam_fun_t384(tll_ptr a_v38867, tll_env env) {
  tll_ptr call_ret_t383;
  call_ret_t383 = get_at_i36(env[2], env[1], env[0], a_v38867);
  return call_ret_t383;
}

tll_ptr lam_fun_t386(tll_ptr xs_v38865, tll_env env) {
  tll_ptr lam_clo_t385;
  instr_clo(&lam_clo_t385, &lam_fun_t384, 3, xs_v38865, env[0], env[1]);
  return lam_clo_t385;
}

tll_ptr lam_fun_t388(tll_ptr n_v38862, tll_env env) {
  tll_ptr lam_clo_t387;
  instr_clo(&lam_clo_t387, &lam_fun_t386, 2, n_v38862, env[0]);
  return lam_clo_t387;
}

tll_ptr lam_fun_t390(tll_ptr A_v38858, tll_env env) {
  tll_ptr lam_clo_t389;
  instr_clo(&lam_clo_t389, &lam_fun_t388, 1, A_v38858);
  return lam_clo_t389;
}

tll_ptr string_of_digit_i37(tll_ptr n_v38868) {
  tll_ptr EmptyString_t393; tll_ptr call_ret_t392;
  instr_struct(&EmptyString_t393, 6, 0);
  call_ret_t392 = get_at_i36(0, n_v38868, digits_i35, EmptyString_t393);
  return call_ret_t392;
}

tll_ptr lam_fun_t395(tll_ptr n_v38869, tll_env env) {
  tll_ptr call_ret_t394;
  call_ret_t394 = string_of_digit_i37(n_v38869);
  return call_ret_t394;
}

tll_ptr string_of_nat_i38(tll_ptr n_v38870) {
  tll_ptr call_ret_t397; tll_ptr call_ret_t398; tll_ptr call_ret_t399;
  tll_ptr call_ret_t400; tll_ptr call_ret_t401; tll_ptr call_ret_t402;
  tll_ptr ifte_ret_t403; tll_ptr n_v38872; tll_ptr s_v38871;
  call_ret_t398 = modn_i16(n_v38870, (tll_ptr)10);
  call_ret_t397 = string_of_digit_i37(call_ret_t398);
  s_v38871 = call_ret_t397;
  call_ret_t399 = divn_i15(n_v38870, (tll_ptr)10);
  n_v38872 = call_ret_t399;
  call_ret_t400 = ltn_i7((tll_ptr)0, n_v38872);
  if (call_ret_t400) {
    call_ret_t402 = string_of_nat_i38(n_v38872);
    call_ret_t401 = cats_i19(call_ret_t402, s_v38871);
    ifte_ret_t403 = call_ret_t401;
  }
  else {
    ifte_ret_t403 = s_v38871;
  }
  return ifte_ret_t403;
}

tll_ptr lam_fun_t405(tll_ptr n_v38873, tll_env env) {
  tll_ptr call_ret_t404;
  call_ret_t404 = string_of_nat_i38(n_v38873);
  return call_ret_t404;
}

tll_ptr digit_of_char_i39(tll_ptr c_v38874) {
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
  call_ret_t407 = eqc_i17(c_v38874, Char_t408);
  if (call_ret_t407) {
    instr_struct(&SomeUL_t409, 17, 1, (tll_ptr)0);
    ifte_ret_t447 = SomeUL_t409;
  }
  else {
    instr_struct(&Char_t411, 5, 1, (tll_ptr)49);
    call_ret_t410 = eqc_i17(c_v38874, Char_t411);
    if (call_ret_t410) {
      instr_struct(&SomeUL_t412, 17, 1, (tll_ptr)1);
      ifte_ret_t446 = SomeUL_t412;
    }
    else {
      instr_struct(&Char_t414, 5, 1, (tll_ptr)50);
      call_ret_t413 = eqc_i17(c_v38874, Char_t414);
      if (call_ret_t413) {
        instr_struct(&SomeUL_t415, 17, 1, (tll_ptr)2);
        ifte_ret_t445 = SomeUL_t415;
      }
      else {
        instr_struct(&Char_t417, 5, 1, (tll_ptr)51);
        call_ret_t416 = eqc_i17(c_v38874, Char_t417);
        if (call_ret_t416) {
          instr_struct(&SomeUL_t418, 17, 1, (tll_ptr)3);
          ifte_ret_t444 = SomeUL_t418;
        }
        else {
          instr_struct(&Char_t420, 5, 1, (tll_ptr)52);
          call_ret_t419 = eqc_i17(c_v38874, Char_t420);
          if (call_ret_t419) {
            instr_struct(&SomeUL_t421, 17, 1, (tll_ptr)4);
            ifte_ret_t443 = SomeUL_t421;
          }
          else {
            instr_struct(&Char_t423, 5, 1, (tll_ptr)53);
            call_ret_t422 = eqc_i17(c_v38874, Char_t423);
            if (call_ret_t422) {
              instr_struct(&SomeUL_t424, 17, 1, (tll_ptr)5);
              ifte_ret_t442 = SomeUL_t424;
            }
            else {
              instr_struct(&Char_t426, 5, 1, (tll_ptr)54);
              call_ret_t425 = eqc_i17(c_v38874, Char_t426);
              if (call_ret_t425) {
                instr_struct(&SomeUL_t427, 17, 1, (tll_ptr)6);
                ifte_ret_t441 = SomeUL_t427;
              }
              else {
                instr_struct(&Char_t429, 5, 1, (tll_ptr)55);
                call_ret_t428 = eqc_i17(c_v38874, Char_t429);
                if (call_ret_t428) {
                  instr_struct(&SomeUL_t430, 17, 1, (tll_ptr)7);
                  ifte_ret_t440 = SomeUL_t430;
                }
                else {
                  instr_struct(&Char_t432, 5, 1, (tll_ptr)56);
                  call_ret_t431 = eqc_i17(c_v38874, Char_t432);
                  if (call_ret_t431) {
                    instr_struct(&SomeUL_t433, 17, 1, (tll_ptr)8);
                    ifte_ret_t439 = SomeUL_t433;
                  }
                  else {
                    instr_struct(&Char_t435, 5, 1, (tll_ptr)57);
                    call_ret_t434 = eqc_i17(c_v38874, Char_t435);
                    if (call_ret_t434) {
                      instr_struct(&SomeUL_t436, 17, 1, (tll_ptr)9);
                      ifte_ret_t438 = SomeUL_t436;
                    }
                    else {
                      instr_struct(&NoneUL_t437, 16, 0);
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

tll_ptr lam_fun_t449(tll_ptr c_v38875, tll_env env) {
  tll_ptr call_ret_t448;
  call_ret_t448 = digit_of_char_i39(c_v38875);
  return call_ret_t448;
}

tll_ptr nat_of_string_loop_i40(tll_ptr s_v38876, tll_ptr acc_v38877) {
  tll_ptr NoneUL_t455; tll_ptr SomeUL_t452; tll_ptr c_v38878;
  tll_ptr call_ret_t453; tll_ptr call_ret_t456; tll_ptr call_ret_t457;
  tll_ptr call_ret_t458; tll_ptr n_v38880; tll_ptr s_v38879;
  tll_ptr switch_ret_t451; tll_ptr switch_ret_t454;
  switch(((tll_node)s_v38876)->tag) {
    case 6:
      instr_struct(&SomeUL_t452, 17, 1, acc_v38877);
      switch_ret_t451 = SomeUL_t452;
      break;
    case 7:
      c_v38878 = ((tll_node)s_v38876)->data[0];
      s_v38879 = ((tll_node)s_v38876)->data[1];
      call_ret_t453 = digit_of_char_i39(c_v38878);
      switch(((tll_node)call_ret_t453)->tag) {
        case 16:
          instr_free_struct(call_ret_t453);
          instr_struct(&NoneUL_t455, 16, 0);
          switch_ret_t454 = NoneUL_t455;
          break;
        case 17:
          n_v38880 = ((tll_node)call_ret_t453)->data[0];
          instr_free_struct(call_ret_t453);
          call_ret_t458 = muln_i14(acc_v38877, (tll_ptr)10);
          call_ret_t457 = addn_i12(call_ret_t458, n_v38880);
          call_ret_t456 = nat_of_string_loop_i40(s_v38879, call_ret_t457);
          switch_ret_t454 = call_ret_t456;
          break;
      }
      switch_ret_t451 = switch_ret_t454;
      break;
  }
  return switch_ret_t451;
}

tll_ptr lam_fun_t460(tll_ptr acc_v38883, tll_env env) {
  tll_ptr call_ret_t459;
  call_ret_t459 = nat_of_string_loop_i40(env[0], acc_v38883);
  return call_ret_t459;
}

tll_ptr lam_fun_t462(tll_ptr s_v38881, tll_env env) {
  tll_ptr lam_clo_t461;
  instr_clo(&lam_clo_t461, &lam_fun_t460, 1, s_v38881);
  return lam_clo_t461;
}

tll_ptr nat_of_string_i41(tll_ptr s_v38884) {
  tll_ptr call_ret_t464;
  call_ret_t464 = nat_of_string_loop_i40(s_v38884, (tll_ptr)0);
  return call_ret_t464;
}

tll_ptr lam_fun_t466(tll_ptr s_v38885, tll_env env) {
  tll_ptr call_ret_t465;
  call_ret_t465 = nat_of_string_i41(s_v38885);
  return call_ret_t465;
}

tll_ptr lam_fun_t537(tll_ptr __v38887, tll_env env) {
  tll_ptr Char_t473; tll_ptr Char_t474; tll_ptr Char_t475; tll_ptr Char_t476;
  tll_ptr Char_t477; tll_ptr Char_t478; tll_ptr Char_t479; tll_ptr Char_t480;
  tll_ptr Char_t481; tll_ptr Char_t482; tll_ptr Char_t483; tll_ptr Char_t484;
  tll_ptr Char_t485; tll_ptr Char_t486; tll_ptr Char_t487; tll_ptr Char_t488;
  tll_ptr Char_t489; tll_ptr Char_t490; tll_ptr Char_t491; tll_ptr Char_t492;
  tll_ptr Char_t493; tll_ptr Char_t494; tll_ptr Char_t495; tll_ptr Char_t496;
  tll_ptr Char_t497; tll_ptr Char_t498; tll_ptr Char_t499; tll_ptr Char_t500;
  tll_ptr Char_t501; tll_ptr Char_t502; tll_ptr EmptyString_t503;
  tll_ptr String_t504; tll_ptr String_t505; tll_ptr String_t506;
  tll_ptr String_t507; tll_ptr String_t508; tll_ptr String_t509;
  tll_ptr String_t510; tll_ptr String_t511; tll_ptr String_t512;
  tll_ptr String_t513; tll_ptr String_t514; tll_ptr String_t515;
  tll_ptr String_t516; tll_ptr String_t517; tll_ptr String_t518;
  tll_ptr String_t519; tll_ptr String_t520; tll_ptr String_t521;
  tll_ptr String_t522; tll_ptr String_t523; tll_ptr String_t524;
  tll_ptr String_t525; tll_ptr String_t526; tll_ptr String_t527;
  tll_ptr String_t528; tll_ptr String_t529; tll_ptr String_t530;
  tll_ptr String_t531; tll_ptr String_t532; tll_ptr String_t533;
  tll_ptr __v38893; tll_ptr app_ret_t469; tll_ptr app_ret_t534;
  tll_ptr app_ret_t536; tll_ptr call_ret_t468; tll_ptr call_ret_t470;
  tll_ptr call_ret_t472; tll_ptr call_ret_t535; tll_ptr n_v38892;
  tll_ptr s_v38891; tll_ptr switch_ret_t471;
  call_ret_t468 = readline_i32(0);
  instr_app(&app_ret_t469, call_ret_t468, 0);
  instr_free_clo(call_ret_t468);
  s_v38891 = app_ret_t469;
  call_ret_t470 = nat_of_string_i41(s_v38891);
  switch(((tll_node)call_ret_t470)->tag) {
    case 17:
      n_v38892 = ((tll_node)call_ret_t470)->data[0];
      instr_free_struct(call_ret_t470);
      switch_ret_t471 = n_v38892;
      break;
    case 16:
      instr_free_struct(call_ret_t470);
      instr_struct(&Char_t473, 5, 1, (tll_ptr)112);
      instr_struct(&Char_t474, 5, 1, (tll_ptr)108);
      instr_struct(&Char_t475, 5, 1, (tll_ptr)101);
      instr_struct(&Char_t476, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t477, 5, 1, (tll_ptr)115);
      instr_struct(&Char_t478, 5, 1, (tll_ptr)101);
      instr_struct(&Char_t479, 5, 1, (tll_ptr)32);
      instr_struct(&Char_t480, 5, 1, (tll_ptr)105);
      instr_struct(&Char_t481, 5, 1, (tll_ptr)110);
      instr_struct(&Char_t482, 5, 1, (tll_ptr)112);
      instr_struct(&Char_t483, 5, 1, (tll_ptr)117);
      instr_struct(&Char_t484, 5, 1, (tll_ptr)116);
      instr_struct(&Char_t485, 5, 1, (tll_ptr)32);
      instr_struct(&Char_t486, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t487, 5, 1, (tll_ptr)32);
      instr_struct(&Char_t488, 5, 1, (tll_ptr)110);
      instr_struct(&Char_t489, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t490, 5, 1, (tll_ptr)116);
      instr_struct(&Char_t491, 5, 1, (tll_ptr)117);
      instr_struct(&Char_t492, 5, 1, (tll_ptr)114);
      instr_struct(&Char_t493, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t494, 5, 1, (tll_ptr)108);
      instr_struct(&Char_t495, 5, 1, (tll_ptr)32);
      instr_struct(&Char_t496, 5, 1, (tll_ptr)110);
      instr_struct(&Char_t497, 5, 1, (tll_ptr)117);
      instr_struct(&Char_t498, 5, 1, (tll_ptr)109);
      instr_struct(&Char_t499, 5, 1, (tll_ptr)98);
      instr_struct(&Char_t500, 5, 1, (tll_ptr)101);
      instr_struct(&Char_t501, 5, 1, (tll_ptr)114);
      instr_struct(&Char_t502, 5, 1, (tll_ptr)10);
      instr_struct(&EmptyString_t503, 6, 0);
      instr_struct(&String_t504, 7, 2, Char_t502, EmptyString_t503);
      instr_struct(&String_t505, 7, 2, Char_t501, String_t504);
      instr_struct(&String_t506, 7, 2, Char_t500, String_t505);
      instr_struct(&String_t507, 7, 2, Char_t499, String_t506);
      instr_struct(&String_t508, 7, 2, Char_t498, String_t507);
      instr_struct(&String_t509, 7, 2, Char_t497, String_t508);
      instr_struct(&String_t510, 7, 2, Char_t496, String_t509);
      instr_struct(&String_t511, 7, 2, Char_t495, String_t510);
      instr_struct(&String_t512, 7, 2, Char_t494, String_t511);
      instr_struct(&String_t513, 7, 2, Char_t493, String_t512);
      instr_struct(&String_t514, 7, 2, Char_t492, String_t513);
      instr_struct(&String_t515, 7, 2, Char_t491, String_t514);
      instr_struct(&String_t516, 7, 2, Char_t490, String_t515);
      instr_struct(&String_t517, 7, 2, Char_t489, String_t516);
      instr_struct(&String_t518, 7, 2, Char_t488, String_t517);
      instr_struct(&String_t519, 7, 2, Char_t487, String_t518);
      instr_struct(&String_t520, 7, 2, Char_t486, String_t519);
      instr_struct(&String_t521, 7, 2, Char_t485, String_t520);
      instr_struct(&String_t522, 7, 2, Char_t484, String_t521);
      instr_struct(&String_t523, 7, 2, Char_t483, String_t522);
      instr_struct(&String_t524, 7, 2, Char_t482, String_t523);
      instr_struct(&String_t525, 7, 2, Char_t481, String_t524);
      instr_struct(&String_t526, 7, 2, Char_t480, String_t525);
      instr_struct(&String_t527, 7, 2, Char_t479, String_t526);
      instr_struct(&String_t528, 7, 2, Char_t478, String_t527);
      instr_struct(&String_t529, 7, 2, Char_t477, String_t528);
      instr_struct(&String_t530, 7, 2, Char_t476, String_t529);
      instr_struct(&String_t531, 7, 2, Char_t475, String_t530);
      instr_struct(&String_t532, 7, 2, Char_t474, String_t531);
      instr_struct(&String_t533, 7, 2, Char_t473, String_t532);
      call_ret_t472 = print_i33(String_t533);
      instr_app(&app_ret_t534, call_ret_t472, 0);
      instr_free_clo(call_ret_t472);
      __v38893 = app_ret_t534;
      call_ret_t535 = read_nat_i48(0);
      instr_app(&app_ret_t536, call_ret_t535, 0);
      instr_free_clo(call_ret_t535);
      switch_ret_t471 = app_ret_t536;
      break;
  }
  return switch_ret_t471;
}

tll_ptr read_nat_i48(tll_ptr __v38886) {
  tll_ptr lam_clo_t538;
  instr_clo(&lam_clo_t538, &lam_fun_t537, 0);
  return lam_clo_t538;
}

tll_ptr lam_fun_t540(tll_ptr __v38894, tll_env env) {
  tll_ptr call_ret_t539;
  call_ret_t539 = read_nat_i48(__v38894);
  return call_ret_t539;
}

tll_ptr lam_fun_t772(tll_ptr __v38910, tll_env env) {
  tll_ptr Char_t551; tll_ptr Char_t552; tll_ptr Char_t553; tll_ptr Char_t554;
  tll_ptr Char_t555; tll_ptr Char_t556; tll_ptr Char_t557; tll_ptr Char_t558;
  tll_ptr Char_t559; tll_ptr Char_t575; tll_ptr Char_t576; tll_ptr Char_t577;
  tll_ptr Char_t578; tll_ptr Char_t579; tll_ptr Char_t580; tll_ptr Char_t581;
  tll_ptr Char_t582; tll_ptr Char_t583; tll_ptr Char_t584; tll_ptr Char_t585;
  tll_ptr Char_t586; tll_ptr Char_t587; tll_ptr Char_t588; tll_ptr Char_t589;
  tll_ptr Char_t590; tll_ptr Char_t591; tll_ptr Char_t592; tll_ptr Char_t593;
  tll_ptr Char_t594; tll_ptr Char_t595; tll_ptr Char_t596; tll_ptr Char_t597;
  tll_ptr Char_t598; tll_ptr Char_t599; tll_ptr Char_t600; tll_ptr Char_t601;
  tll_ptr Char_t602; tll_ptr Char_t603; tll_ptr Char_t604; tll_ptr Char_t605;
  tll_ptr Char_t640; tll_ptr Char_t641; tll_ptr Char_t642; tll_ptr Char_t643;
  tll_ptr Char_t644; tll_ptr Char_t645; tll_ptr Char_t646; tll_ptr Char_t647;
  tll_ptr Char_t648; tll_ptr Char_t649; tll_ptr Char_t650; tll_ptr Char_t651;
  tll_ptr Char_t652; tll_ptr Char_t674; tll_ptr Char_t675; tll_ptr Char_t676;
  tll_ptr Char_t677; tll_ptr Char_t678; tll_ptr Char_t679; tll_ptr Char_t680;
  tll_ptr Char_t681; tll_ptr Char_t682; tll_ptr Char_t683; tll_ptr Char_t684;
  tll_ptr Char_t685; tll_ptr Char_t686; tll_ptr Char_t687; tll_ptr Char_t688;
  tll_ptr Char_t689; tll_ptr Char_t690; tll_ptr Char_t691; tll_ptr Char_t692;
  tll_ptr Char_t693; tll_ptr Char_t694; tll_ptr Char_t695; tll_ptr Char_t696;
  tll_ptr Char_t697; tll_ptr Char_t698; tll_ptr Char_t699; tll_ptr Char_t700;
  tll_ptr Char_t701; tll_ptr Char_t702; tll_ptr Char_t703; tll_ptr Char_t704;
  tll_ptr Char_t705; tll_ptr Char_t741; tll_ptr Char_t742; tll_ptr Char_t743;
  tll_ptr Char_t744; tll_ptr Char_t745; tll_ptr Char_t746; tll_ptr Char_t747;
  tll_ptr Char_t748; tll_ptr Char_t749; tll_ptr Char_t750; tll_ptr Char_t751;
  tll_ptr Char_t752; tll_ptr Char_t753; tll_ptr EmptyString_t560;
  tll_ptr EmptyString_t606; tll_ptr EmptyString_t653;
  tll_ptr EmptyString_t706; tll_ptr EmptyString_t754; tll_ptr String_t561;
  tll_ptr String_t562; tll_ptr String_t563; tll_ptr String_t564;
  tll_ptr String_t565; tll_ptr String_t566; tll_ptr String_t567;
  tll_ptr String_t568; tll_ptr String_t569; tll_ptr String_t607;
  tll_ptr String_t608; tll_ptr String_t609; tll_ptr String_t610;
  tll_ptr String_t611; tll_ptr String_t612; tll_ptr String_t613;
  tll_ptr String_t614; tll_ptr String_t615; tll_ptr String_t616;
  tll_ptr String_t617; tll_ptr String_t618; tll_ptr String_t619;
  tll_ptr String_t620; tll_ptr String_t621; tll_ptr String_t622;
  tll_ptr String_t623; tll_ptr String_t624; tll_ptr String_t625;
  tll_ptr String_t626; tll_ptr String_t627; tll_ptr String_t628;
  tll_ptr String_t629; tll_ptr String_t630; tll_ptr String_t631;
  tll_ptr String_t632; tll_ptr String_t633; tll_ptr String_t634;
  tll_ptr String_t635; tll_ptr String_t636; tll_ptr String_t637;
  tll_ptr String_t654; tll_ptr String_t655; tll_ptr String_t656;
  tll_ptr String_t657; tll_ptr String_t658; tll_ptr String_t659;
  tll_ptr String_t660; tll_ptr String_t661; tll_ptr String_t662;
  tll_ptr String_t663; tll_ptr String_t664; tll_ptr String_t665;
  tll_ptr String_t666; tll_ptr String_t707; tll_ptr String_t708;
  tll_ptr String_t709; tll_ptr String_t710; tll_ptr String_t711;
  tll_ptr String_t712; tll_ptr String_t713; tll_ptr String_t714;
  tll_ptr String_t715; tll_ptr String_t716; tll_ptr String_t717;
  tll_ptr String_t718; tll_ptr String_t719; tll_ptr String_t720;
  tll_ptr String_t721; tll_ptr String_t722; tll_ptr String_t723;
  tll_ptr String_t724; tll_ptr String_t725; tll_ptr String_t726;
  tll_ptr String_t727; tll_ptr String_t728; tll_ptr String_t729;
  tll_ptr String_t730; tll_ptr String_t731; tll_ptr String_t732;
  tll_ptr String_t733; tll_ptr String_t734; tll_ptr String_t735;
  tll_ptr String_t736; tll_ptr String_t737; tll_ptr String_t738;
  tll_ptr String_t755; tll_ptr String_t756; tll_ptr String_t757;
  tll_ptr String_t758; tll_ptr String_t759; tll_ptr String_t760;
  tll_ptr String_t761; tll_ptr String_t762; tll_ptr String_t763;
  tll_ptr String_t764; tll_ptr String_t765; tll_ptr String_t766;
  tll_ptr String_t767; tll_ptr __v38923; tll_ptr __v38928; tll_ptr __v38929;
  tll_ptr __v38930; tll_ptr add_ret_t639; tll_ptr add_ret_t669;
  tll_ptr add_ret_t740; tll_ptr add_ret_t770; tll_ptr app_ret_t543;
  tll_ptr app_ret_t570; tll_ptr app_ret_t667; tll_ptr app_ret_t670;
  tll_ptr app_ret_t768; tll_ptr app_ret_t771; tll_ptr c_v38922;
  tll_ptr c_v38925; tll_ptr c_v38927; tll_ptr call_ret_t542;
  tll_ptr call_ret_t550; tll_ptr call_ret_t572; tll_ptr call_ret_t573;
  tll_ptr call_ret_t574; tll_ptr call_ret_t638; tll_ptr call_ret_t668;
  tll_ptr call_ret_t671; tll_ptr call_ret_t672; tll_ptr call_ret_t673;
  tll_ptr call_ret_t739; tll_ptr call_ret_t769; tll_ptr close_tmp_t571;
  tll_ptr guess_v38921; tll_ptr ord_v38924; tll_ptr pair_struct_t547;
  tll_ptr pf_v38926; tll_ptr recv_msg_t545; tll_ptr send_ch_t544;
  tll_ptr switch_ret_t546; tll_ptr switch_ret_t548; tll_ptr switch_ret_t549;
  call_ret_t542 = read_nat_i48(0);
  instr_app(&app_ret_t543, call_ret_t542, 0);
  instr_free_clo(call_ret_t542);
  guess_v38921 = app_ret_t543;
  instr_send(&send_ch_t544, env[0], guess_v38921);
  c_v38922 = send_ch_t544;
  instr_recv(&recv_msg_t545, c_v38922);
  __v38923 = recv_msg_t545;
  switch(((tll_node)__v38923)->tag) {
    case 0:
      ord_v38924 = ((tll_node)__v38923)->data[0];
      c_v38925 = ((tll_node)__v38923)->data[1];
      instr_free_struct(__v38923);
      instr_struct(&pair_struct_t547, 0, 2, 0, c_v38925);
      switch(((tll_node)pair_struct_t547)->tag) {
        case 0:
          pf_v38926 = ((tll_node)pair_struct_t547)->data[0];
          c_v38927 = ((tll_node)pair_struct_t547)->data[1];
          instr_free_struct(pair_struct_t547);
          switch(((tll_node)ord_v38924)->tag) {
            case 3:
              instr_struct(&Char_t551, 5, 1, (tll_ptr)89);
              instr_struct(&Char_t552, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t553, 5, 1, (tll_ptr)117);
              instr_struct(&Char_t554, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t555, 5, 1, (tll_ptr)87);
              instr_struct(&Char_t556, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t557, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t558, 5, 1, (tll_ptr)33);
              instr_struct(&Char_t559, 5, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t560, 6, 0);
              instr_struct(&String_t561, 7, 2, Char_t559, EmptyString_t560);
              instr_struct(&String_t562, 7, 2, Char_t558, String_t561);
              instr_struct(&String_t563, 7, 2, Char_t557, String_t562);
              instr_struct(&String_t564, 7, 2, Char_t556, String_t563);
              instr_struct(&String_t565, 7, 2, Char_t555, String_t564);
              instr_struct(&String_t566, 7, 2, Char_t554, String_t565);
              instr_struct(&String_t567, 7, 2, Char_t553, String_t566);
              instr_struct(&String_t568, 7, 2, Char_t552, String_t567);
              instr_struct(&String_t569, 7, 2, Char_t551, String_t568);
              call_ret_t550 = print_i33(String_t569);
              instr_app(&app_ret_t570, call_ret_t550, 0);
              instr_free_clo(call_ret_t550);
              __v38928 = app_ret_t570;
              instr_close(&close_tmp_t571, c_v38927);
              switch_ret_t549 = close_tmp_t571;
              break;
            case 1:
              instr_struct(&Char_t575, 5, 1, (tll_ptr)84);
              instr_struct(&Char_t576, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t577, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t578, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t579, 5, 1, (tll_ptr)97);
              instr_struct(&Char_t580, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t581, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t582, 5, 1, (tll_ptr)119);
              instr_struct(&Char_t583, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t584, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t585, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t586, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t587, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t588, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t589, 5, 1, (tll_ptr)108);
              instr_struct(&Char_t590, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t591, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t592, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t593, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t594, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t595, 5, 1, (tll_ptr)44);
              instr_struct(&Char_t596, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t597, 5, 1, (tll_ptr)121);
              instr_struct(&Char_t598, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t599, 5, 1, (tll_ptr)117);
              instr_struct(&Char_t600, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t601, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t602, 5, 1, (tll_ptr)97);
              instr_struct(&Char_t603, 5, 1, (tll_ptr)118);
              instr_struct(&Char_t604, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t605, 5, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t606, 6, 0);
              instr_struct(&String_t607, 7, 2, Char_t605, EmptyString_t606);
              instr_struct(&String_t608, 7, 2, Char_t604, String_t607);
              instr_struct(&String_t609, 7, 2, Char_t603, String_t608);
              instr_struct(&String_t610, 7, 2, Char_t602, String_t609);
              instr_struct(&String_t611, 7, 2, Char_t601, String_t610);
              instr_struct(&String_t612, 7, 2, Char_t600, String_t611);
              instr_struct(&String_t613, 7, 2, Char_t599, String_t612);
              instr_struct(&String_t614, 7, 2, Char_t598, String_t613);
              instr_struct(&String_t615, 7, 2, Char_t597, String_t614);
              instr_struct(&String_t616, 7, 2, Char_t596, String_t615);
              instr_struct(&String_t617, 7, 2, Char_t595, String_t616);
              instr_struct(&String_t618, 7, 2, Char_t594, String_t617);
              instr_struct(&String_t619, 7, 2, Char_t593, String_t618);
              instr_struct(&String_t620, 7, 2, Char_t592, String_t619);
              instr_struct(&String_t621, 7, 2, Char_t591, String_t620);
              instr_struct(&String_t622, 7, 2, Char_t590, String_t621);
              instr_struct(&String_t623, 7, 2, Char_t589, String_t622);
              instr_struct(&String_t624, 7, 2, Char_t588, String_t623);
              instr_struct(&String_t625, 7, 2, Char_t587, String_t624);
              instr_struct(&String_t626, 7, 2, Char_t586, String_t625);
              instr_struct(&String_t627, 7, 2, Char_t585, String_t626);
              instr_struct(&String_t628, 7, 2, Char_t584, String_t627);
              instr_struct(&String_t629, 7, 2, Char_t583, String_t628);
              instr_struct(&String_t630, 7, 2, Char_t582, String_t629);
              instr_struct(&String_t631, 7, 2, Char_t581, String_t630);
              instr_struct(&String_t632, 7, 2, Char_t580, String_t631);
              instr_struct(&String_t633, 7, 2, Char_t579, String_t632);
              instr_struct(&String_t634, 7, 2, Char_t578, String_t633);
              instr_struct(&String_t635, 7, 2, Char_t577, String_t634);
              instr_struct(&String_t636, 7, 2, Char_t576, String_t635);
              instr_struct(&String_t637, 7, 2, Char_t575, String_t636);
              add_ret_t639 = env[1] - 1;
              call_ret_t638 = string_of_nat_i38(add_ret_t639);
              call_ret_t574 = cats_i19(String_t637, call_ret_t638);
              instr_struct(&Char_t640, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t641, 5, 1, (tll_ptr)109);
              instr_struct(&Char_t642, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t643, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t644, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t645, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t646, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t647, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t648, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t649, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t650, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t651, 5, 1, (tll_ptr)46);
              instr_struct(&Char_t652, 5, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t653, 6, 0);
              instr_struct(&String_t654, 7, 2, Char_t652, EmptyString_t653);
              instr_struct(&String_t655, 7, 2, Char_t651, String_t654);
              instr_struct(&String_t656, 7, 2, Char_t650, String_t655);
              instr_struct(&String_t657, 7, 2, Char_t649, String_t656);
              instr_struct(&String_t658, 7, 2, Char_t648, String_t657);
              instr_struct(&String_t659, 7, 2, Char_t647, String_t658);
              instr_struct(&String_t660, 7, 2, Char_t646, String_t659);
              instr_struct(&String_t661, 7, 2, Char_t645, String_t660);
              instr_struct(&String_t662, 7, 2, Char_t644, String_t661);
              instr_struct(&String_t663, 7, 2, Char_t643, String_t662);
              instr_struct(&String_t664, 7, 2, Char_t642, String_t663);
              instr_struct(&String_t665, 7, 2, Char_t641, String_t664);
              instr_struct(&String_t666, 7, 2, Char_t640, String_t665);
              call_ret_t573 = cats_i19(call_ret_t574, String_t666);
              call_ret_t572 = print_i33(call_ret_t573);
              instr_app(&app_ret_t667, call_ret_t572, 0);
              instr_free_clo(call_ret_t572);
              __v38929 = app_ret_t667;
              add_ret_t669 = env[1] - 1;
              call_ret_t668 = player_loop_i49(0, add_ret_t669, c_v38927);
              instr_app(&app_ret_t670, call_ret_t668, 0);
              instr_free_clo(call_ret_t668);
              switch_ret_t549 = app_ret_t670;
              break;
            case 2:
              instr_struct(&Char_t674, 5, 1, (tll_ptr)84);
              instr_struct(&Char_t675, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t676, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t677, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t678, 5, 1, (tll_ptr)97);
              instr_struct(&Char_t679, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t680, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t681, 5, 1, (tll_ptr)119);
              instr_struct(&Char_t682, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t683, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t684, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t685, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t686, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t687, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t688, 5, 1, (tll_ptr)103);
              instr_struct(&Char_t689, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t690, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t691, 5, 1, (tll_ptr)97);
              instr_struct(&Char_t692, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t693, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t694, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t695, 5, 1, (tll_ptr)44);
              instr_struct(&Char_t696, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t697, 5, 1, (tll_ptr)121);
              instr_struct(&Char_t698, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t699, 5, 1, (tll_ptr)117);
              instr_struct(&Char_t700, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t701, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t702, 5, 1, (tll_ptr)97);
              instr_struct(&Char_t703, 5, 1, (tll_ptr)118);
              instr_struct(&Char_t704, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t705, 5, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t706, 6, 0);
              instr_struct(&String_t707, 7, 2, Char_t705, EmptyString_t706);
              instr_struct(&String_t708, 7, 2, Char_t704, String_t707);
              instr_struct(&String_t709, 7, 2, Char_t703, String_t708);
              instr_struct(&String_t710, 7, 2, Char_t702, String_t709);
              instr_struct(&String_t711, 7, 2, Char_t701, String_t710);
              instr_struct(&String_t712, 7, 2, Char_t700, String_t711);
              instr_struct(&String_t713, 7, 2, Char_t699, String_t712);
              instr_struct(&String_t714, 7, 2, Char_t698, String_t713);
              instr_struct(&String_t715, 7, 2, Char_t697, String_t714);
              instr_struct(&String_t716, 7, 2, Char_t696, String_t715);
              instr_struct(&String_t717, 7, 2, Char_t695, String_t716);
              instr_struct(&String_t718, 7, 2, Char_t694, String_t717);
              instr_struct(&String_t719, 7, 2, Char_t693, String_t718);
              instr_struct(&String_t720, 7, 2, Char_t692, String_t719);
              instr_struct(&String_t721, 7, 2, Char_t691, String_t720);
              instr_struct(&String_t722, 7, 2, Char_t690, String_t721);
              instr_struct(&String_t723, 7, 2, Char_t689, String_t722);
              instr_struct(&String_t724, 7, 2, Char_t688, String_t723);
              instr_struct(&String_t725, 7, 2, Char_t687, String_t724);
              instr_struct(&String_t726, 7, 2, Char_t686, String_t725);
              instr_struct(&String_t727, 7, 2, Char_t685, String_t726);
              instr_struct(&String_t728, 7, 2, Char_t684, String_t727);
              instr_struct(&String_t729, 7, 2, Char_t683, String_t728);
              instr_struct(&String_t730, 7, 2, Char_t682, String_t729);
              instr_struct(&String_t731, 7, 2, Char_t681, String_t730);
              instr_struct(&String_t732, 7, 2, Char_t680, String_t731);
              instr_struct(&String_t733, 7, 2, Char_t679, String_t732);
              instr_struct(&String_t734, 7, 2, Char_t678, String_t733);
              instr_struct(&String_t735, 7, 2, Char_t677, String_t734);
              instr_struct(&String_t736, 7, 2, Char_t676, String_t735);
              instr_struct(&String_t737, 7, 2, Char_t675, String_t736);
              instr_struct(&String_t738, 7, 2, Char_t674, String_t737);
              add_ret_t740 = env[1] - 1;
              call_ret_t739 = string_of_nat_i38(add_ret_t740);
              call_ret_t673 = cats_i19(String_t738, call_ret_t739);
              instr_struct(&Char_t741, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t742, 5, 1, (tll_ptr)109);
              instr_struct(&Char_t743, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t744, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t745, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t746, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t747, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t748, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t749, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t750, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t751, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t752, 5, 1, (tll_ptr)46);
              instr_struct(&Char_t753, 5, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t754, 6, 0);
              instr_struct(&String_t755, 7, 2, Char_t753, EmptyString_t754);
              instr_struct(&String_t756, 7, 2, Char_t752, String_t755);
              instr_struct(&String_t757, 7, 2, Char_t751, String_t756);
              instr_struct(&String_t758, 7, 2, Char_t750, String_t757);
              instr_struct(&String_t759, 7, 2, Char_t749, String_t758);
              instr_struct(&String_t760, 7, 2, Char_t748, String_t759);
              instr_struct(&String_t761, 7, 2, Char_t747, String_t760);
              instr_struct(&String_t762, 7, 2, Char_t746, String_t761);
              instr_struct(&String_t763, 7, 2, Char_t745, String_t762);
              instr_struct(&String_t764, 7, 2, Char_t744, String_t763);
              instr_struct(&String_t765, 7, 2, Char_t743, String_t764);
              instr_struct(&String_t766, 7, 2, Char_t742, String_t765);
              instr_struct(&String_t767, 7, 2, Char_t741, String_t766);
              call_ret_t672 = cats_i19(call_ret_t673, String_t767);
              call_ret_t671 = print_i33(call_ret_t672);
              instr_app(&app_ret_t768, call_ret_t671, 0);
              instr_free_clo(call_ret_t671);
              __v38930 = app_ret_t768;
              add_ret_t770 = env[1] - 1;
              call_ret_t769 = player_loop_i49(0, add_ret_t770, c_v38927);
              instr_app(&app_ret_t771, call_ret_t769, 0);
              instr_free_clo(call_ret_t769);
              switch_ret_t549 = app_ret_t771;
              break;
          }
          switch_ret_t548 = switch_ret_t549;
          break;
      }
      switch_ret_t546 = switch_ret_t548;
      break;
  }
  return switch_ret_t546;
}

tll_ptr lam_fun_t774(tll_ptr c_v38898, tll_env env) {
  tll_ptr lam_clo_t773;
  instr_clo(&lam_clo_t773, &lam_fun_t772, 2, c_v38898, env[0]);
  return lam_clo_t773;
}

tll_ptr lam_fun_t840(tll_ptr __v38939, tll_env env) {
  tll_ptr Char_t783; tll_ptr Char_t784; tll_ptr Char_t785; tll_ptr Char_t786;
  tll_ptr Char_t787; tll_ptr Char_t788; tll_ptr Char_t789; tll_ptr Char_t790;
  tll_ptr Char_t791; tll_ptr Char_t792; tll_ptr Char_t793; tll_ptr Char_t794;
  tll_ptr Char_t795; tll_ptr Char_t796; tll_ptr Char_t797; tll_ptr Char_t798;
  tll_ptr Char_t799; tll_ptr Char_t800; tll_ptr Char_t801; tll_ptr Char_t802;
  tll_ptr Char_t803; tll_ptr Char_t804; tll_ptr Char_t805; tll_ptr Char_t806;
  tll_ptr Char_t833; tll_ptr Char_t834; tll_ptr EmptyString_t807;
  tll_ptr EmptyString_t835; tll_ptr String_t808; tll_ptr String_t809;
  tll_ptr String_t810; tll_ptr String_t811; tll_ptr String_t812;
  tll_ptr String_t813; tll_ptr String_t814; tll_ptr String_t815;
  tll_ptr String_t816; tll_ptr String_t817; tll_ptr String_t818;
  tll_ptr String_t819; tll_ptr String_t820; tll_ptr String_t821;
  tll_ptr String_t822; tll_ptr String_t823; tll_ptr String_t824;
  tll_ptr String_t825; tll_ptr String_t826; tll_ptr String_t827;
  tll_ptr String_t828; tll_ptr String_t829; tll_ptr String_t830;
  tll_ptr String_t831; tll_ptr String_t836; tll_ptr String_t837;
  tll_ptr __v38946; tll_ptr __v38951; tll_ptr ans_v38947;
  tll_ptr app_ret_t838; tll_ptr c_v38948; tll_ptr c_v38950;
  tll_ptr call_ret_t780; tll_ptr call_ret_t781; tll_ptr call_ret_t782;
  tll_ptr call_ret_t832; tll_ptr close_tmp_t839; tll_ptr pair_struct_t778;
  tll_ptr pf_v38949; tll_ptr recv_msg_t776; tll_ptr switch_ret_t777;
  tll_ptr switch_ret_t779;
  instr_recv(&recv_msg_t776, env[0]);
  __v38946 = recv_msg_t776;
  switch(((tll_node)__v38946)->tag) {
    case 0:
      ans_v38947 = ((tll_node)__v38946)->data[0];
      c_v38948 = ((tll_node)__v38946)->data[1];
      instr_free_struct(__v38946);
      instr_struct(&pair_struct_t778, 0, 2, 0, c_v38948);
      switch(((tll_node)pair_struct_t778)->tag) {
        case 0:
          pf_v38949 = ((tll_node)pair_struct_t778)->data[0];
          c_v38950 = ((tll_node)pair_struct_t778)->data[1];
          instr_free_struct(pair_struct_t778);
          instr_struct(&Char_t783, 5, 1, (tll_ptr)89);
          instr_struct(&Char_t784, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t785, 5, 1, (tll_ptr)117);
          instr_struct(&Char_t786, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t787, 5, 1, (tll_ptr)76);
          instr_struct(&Char_t788, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t789, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t790, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t791, 5, 1, (tll_ptr)33);
          instr_struct(&Char_t792, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t793, 5, 1, (tll_ptr)84);
          instr_struct(&Char_t794, 5, 1, (tll_ptr)104);
          instr_struct(&Char_t795, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t796, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t797, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t798, 5, 1, (tll_ptr)110);
          instr_struct(&Char_t799, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t800, 5, 1, (tll_ptr)119);
          instr_struct(&Char_t801, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t802, 5, 1, (tll_ptr)114);
          instr_struct(&Char_t803, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t804, 5, 1, (tll_ptr)105);
          instr_struct(&Char_t805, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t806, 5, 1, (tll_ptr)32);
          instr_struct(&EmptyString_t807, 6, 0);
          instr_struct(&String_t808, 7, 2, Char_t806, EmptyString_t807);
          instr_struct(&String_t809, 7, 2, Char_t805, String_t808);
          instr_struct(&String_t810, 7, 2, Char_t804, String_t809);
          instr_struct(&String_t811, 7, 2, Char_t803, String_t810);
          instr_struct(&String_t812, 7, 2, Char_t802, String_t811);
          instr_struct(&String_t813, 7, 2, Char_t801, String_t812);
          instr_struct(&String_t814, 7, 2, Char_t800, String_t813);
          instr_struct(&String_t815, 7, 2, Char_t799, String_t814);
          instr_struct(&String_t816, 7, 2, Char_t798, String_t815);
          instr_struct(&String_t817, 7, 2, Char_t797, String_t816);
          instr_struct(&String_t818, 7, 2, Char_t796, String_t817);
          instr_struct(&String_t819, 7, 2, Char_t795, String_t818);
          instr_struct(&String_t820, 7, 2, Char_t794, String_t819);
          instr_struct(&String_t821, 7, 2, Char_t793, String_t820);
          instr_struct(&String_t822, 7, 2, Char_t792, String_t821);
          instr_struct(&String_t823, 7, 2, Char_t791, String_t822);
          instr_struct(&String_t824, 7, 2, Char_t790, String_t823);
          instr_struct(&String_t825, 7, 2, Char_t789, String_t824);
          instr_struct(&String_t826, 7, 2, Char_t788, String_t825);
          instr_struct(&String_t827, 7, 2, Char_t787, String_t826);
          instr_struct(&String_t828, 7, 2, Char_t786, String_t827);
          instr_struct(&String_t829, 7, 2, Char_t785, String_t828);
          instr_struct(&String_t830, 7, 2, Char_t784, String_t829);
          instr_struct(&String_t831, 7, 2, Char_t783, String_t830);
          call_ret_t832 = string_of_nat_i38(ans_v38947);
          call_ret_t782 = cats_i19(String_t831, call_ret_t832);
          instr_struct(&Char_t833, 5, 1, (tll_ptr)46);
          instr_struct(&Char_t834, 5, 1, (tll_ptr)10);
          instr_struct(&EmptyString_t835, 6, 0);
          instr_struct(&String_t836, 7, 2, Char_t834, EmptyString_t835);
          instr_struct(&String_t837, 7, 2, Char_t833, String_t836);
          call_ret_t781 = cats_i19(call_ret_t782, String_t837);
          call_ret_t780 = print_i33(call_ret_t781);
          instr_app(&app_ret_t838, call_ret_t780, 0);
          instr_free_clo(call_ret_t780);
          __v38951 = app_ret_t838;
          instr_close(&close_tmp_t839, c_v38950);
          switch_ret_t779 = close_tmp_t839;
          break;
      }
      switch_ret_t777 = switch_ret_t779;
      break;
  }
  return switch_ret_t777;
}

tll_ptr lam_fun_t842(tll_ptr c_v38931, tll_env env) {
  tll_ptr lam_clo_t841;
  instr_clo(&lam_clo_t841, &lam_fun_t840, 1, c_v38931);
  return lam_clo_t841;
}

tll_ptr player_loop_i49(tll_ptr ans_v38895, tll_ptr repeat_v38896, tll_ptr c_v38897) {
  tll_ptr app_ret_t845; tll_ptr ifte_ret_t844; tll_ptr lam_clo_t775;
  tll_ptr lam_clo_t843;
  if (repeat_v38896) {
    instr_clo(&lam_clo_t775, &lam_fun_t774, 1, repeat_v38896);
    ifte_ret_t844 = lam_clo_t775;
  }
  else {
    instr_clo(&lam_clo_t843, &lam_fun_t842, 0);
    ifte_ret_t844 = lam_clo_t843;
  }
  instr_app(&app_ret_t845, ifte_ret_t844, c_v38897);
  return app_ret_t845;
}

tll_ptr lam_fun_t847(tll_ptr c_v38957, tll_env env) {
  tll_ptr call_ret_t846;
  call_ret_t846 = player_loop_i49(env[1], env[0], c_v38957);
  return call_ret_t846;
}

tll_ptr lam_fun_t849(tll_ptr repeat_v38955, tll_env env) {
  tll_ptr lam_clo_t848;
  instr_clo(&lam_clo_t848, &lam_fun_t847, 2, repeat_v38955, env[0]);
  return lam_clo_t848;
}

tll_ptr lam_fun_t851(tll_ptr ans_v38952, tll_env env) {
  tll_ptr lam_clo_t850;
  instr_clo(&lam_clo_t850, &lam_fun_t849, 1, ans_v38952);
  return lam_clo_t850;
}

tll_ptr lam_fun_t989(tll_ptr __v38959, tll_env env) {
  tll_ptr Char_t870; tll_ptr Char_t871; tll_ptr Char_t872; tll_ptr Char_t873;
  tll_ptr Char_t874; tll_ptr Char_t875; tll_ptr Char_t876; tll_ptr Char_t877;
  tll_ptr Char_t878; tll_ptr Char_t879; tll_ptr Char_t880; tll_ptr Char_t881;
  tll_ptr Char_t882; tll_ptr Char_t883; tll_ptr Char_t884; tll_ptr Char_t885;
  tll_ptr Char_t886; tll_ptr Char_t887; tll_ptr Char_t888; tll_ptr Char_t889;
  tll_ptr Char_t890; tll_ptr Char_t891; tll_ptr Char_t892; tll_ptr Char_t893;
  tll_ptr Char_t894; tll_ptr Char_t895; tll_ptr Char_t896; tll_ptr Char_t897;
  tll_ptr Char_t928; tll_ptr Char_t929; tll_ptr Char_t930; tll_ptr Char_t931;
  tll_ptr Char_t932; tll_ptr Char_t940; tll_ptr Char_t941; tll_ptr Char_t949;
  tll_ptr Char_t950; tll_ptr Char_t951; tll_ptr Char_t952; tll_ptr Char_t953;
  tll_ptr Char_t954; tll_ptr Char_t955; tll_ptr Char_t956; tll_ptr Char_t957;
  tll_ptr Char_t969; tll_ptr Char_t970; tll_ptr Char_t971; tll_ptr Char_t972;
  tll_ptr Char_t973; tll_ptr Char_t974; tll_ptr Char_t975; tll_ptr Char_t976;
  tll_ptr EmptyString_t898; tll_ptr EmptyString_t933;
  tll_ptr EmptyString_t942; tll_ptr EmptyString_t958;
  tll_ptr EmptyString_t977; tll_ptr String_t899; tll_ptr String_t900;
  tll_ptr String_t901; tll_ptr String_t902; tll_ptr String_t903;
  tll_ptr String_t904; tll_ptr String_t905; tll_ptr String_t906;
  tll_ptr String_t907; tll_ptr String_t908; tll_ptr String_t909;
  tll_ptr String_t910; tll_ptr String_t911; tll_ptr String_t912;
  tll_ptr String_t913; tll_ptr String_t914; tll_ptr String_t915;
  tll_ptr String_t916; tll_ptr String_t917; tll_ptr String_t918;
  tll_ptr String_t919; tll_ptr String_t920; tll_ptr String_t921;
  tll_ptr String_t922; tll_ptr String_t923; tll_ptr String_t924;
  tll_ptr String_t925; tll_ptr String_t926; tll_ptr String_t934;
  tll_ptr String_t935; tll_ptr String_t936; tll_ptr String_t937;
  tll_ptr String_t938; tll_ptr String_t943; tll_ptr String_t944;
  tll_ptr String_t959; tll_ptr String_t960; tll_ptr String_t961;
  tll_ptr String_t962; tll_ptr String_t963; tll_ptr String_t964;
  tll_ptr String_t965; tll_ptr String_t966; tll_ptr String_t967;
  tll_ptr String_t978; tll_ptr String_t979; tll_ptr String_t980;
  tll_ptr String_t981; tll_ptr String_t982; tll_ptr String_t983;
  tll_ptr String_t984; tll_ptr String_t985; tll_ptr __v38977;
  tll_ptr __v38980; tll_ptr __v38989; tll_ptr __v38992; tll_ptr __v38993;
  tll_ptr ans_v38983; tll_ptr app_ret_t945; tll_ptr app_ret_t986;
  tll_ptr app_ret_t988; tll_ptr c_v38979; tll_ptr c_v38982; tll_ptr c_v38984;
  tll_ptr c_v38986; tll_ptr c_v38988; tll_ptr c_v38991;
  tll_ptr call_ret_t865; tll_ptr call_ret_t866; tll_ptr call_ret_t867;
  tll_ptr call_ret_t868; tll_ptr call_ret_t869; tll_ptr call_ret_t927;
  tll_ptr call_ret_t939; tll_ptr call_ret_t946; tll_ptr call_ret_t947;
  tll_ptr call_ret_t948; tll_ptr call_ret_t968; tll_ptr call_ret_t987;
  tll_ptr lower_v38978; tll_ptr pair_struct_t857; tll_ptr pair_struct_t859;
  tll_ptr pair_struct_t861; tll_ptr pf1_v38985; tll_ptr pf2_v38987;
  tll_ptr recv_msg_t853; tll_ptr recv_msg_t855; tll_ptr recv_msg_t863;
  tll_ptr repeat_v38990; tll_ptr switch_ret_t854; tll_ptr switch_ret_t856;
  tll_ptr switch_ret_t858; tll_ptr switch_ret_t860; tll_ptr switch_ret_t862;
  tll_ptr switch_ret_t864; tll_ptr upper_v38981;
  instr_recv(&recv_msg_t853, env[0]);
  __v38977 = recv_msg_t853;
  switch(((tll_node)__v38977)->tag) {
    case 0:
      lower_v38978 = ((tll_node)__v38977)->data[0];
      c_v38979 = ((tll_node)__v38977)->data[1];
      instr_free_struct(__v38977);
      instr_recv(&recv_msg_t855, c_v38979);
      __v38980 = recv_msg_t855;
      switch(((tll_node)__v38980)->tag) {
        case 0:
          upper_v38981 = ((tll_node)__v38980)->data[0];
          c_v38982 = ((tll_node)__v38980)->data[1];
          instr_free_struct(__v38980);
          instr_struct(&pair_struct_t857, 0, 2, 0, c_v38982);
          switch(((tll_node)pair_struct_t857)->tag) {
            case 0:
              ans_v38983 = ((tll_node)pair_struct_t857)->data[0];
              c_v38984 = ((tll_node)pair_struct_t857)->data[1];
              instr_free_struct(pair_struct_t857);
              instr_struct(&pair_struct_t859, 0, 2, 0, c_v38984);
              switch(((tll_node)pair_struct_t859)->tag) {
                case 0:
                  pf1_v38985 = ((tll_node)pair_struct_t859)->data[0];
                  c_v38986 = ((tll_node)pair_struct_t859)->data[1];
                  instr_free_struct(pair_struct_t859);
                  instr_struct(&pair_struct_t861, 0, 2, 0, c_v38986);
                  switch(((tll_node)pair_struct_t861)->tag) {
                    case 0:
                      pf2_v38987 = ((tll_node)pair_struct_t861)->data[0];
                      c_v38988 = ((tll_node)pair_struct_t861)->data[1];
                      instr_free_struct(pair_struct_t861);
                      instr_recv(&recv_msg_t863, c_v38988);
                      __v38989 = recv_msg_t863;
                      switch(((tll_node)__v38989)->tag) {
                        case 0:
                          repeat_v38990 = ((tll_node)__v38989)->data[0];
                          c_v38991 = ((tll_node)__v38989)->data[1];
                          instr_free_struct(__v38989);
                          instr_struct(&Char_t870, 5, 1, (tll_ptr)80);
                          instr_struct(&Char_t871, 5, 1, (tll_ptr)108);
                          instr_struct(&Char_t872, 5, 1, (tll_ptr)101);
                          instr_struct(&Char_t873, 5, 1, (tll_ptr)97);
                          instr_struct(&Char_t874, 5, 1, (tll_ptr)115);
                          instr_struct(&Char_t875, 5, 1, (tll_ptr)101);
                          instr_struct(&Char_t876, 5, 1, (tll_ptr)32);
                          instr_struct(&Char_t877, 5, 1, (tll_ptr)109);
                          instr_struct(&Char_t878, 5, 1, (tll_ptr)97);
                          instr_struct(&Char_t879, 5, 1, (tll_ptr)107);
                          instr_struct(&Char_t880, 5, 1, (tll_ptr)101);
                          instr_struct(&Char_t881, 5, 1, (tll_ptr)32);
                          instr_struct(&Char_t882, 5, 1, (tll_ptr)97);
                          instr_struct(&Char_t883, 5, 1, (tll_ptr)32);
                          instr_struct(&Char_t884, 5, 1, (tll_ptr)103);
                          instr_struct(&Char_t885, 5, 1, (tll_ptr)117);
                          instr_struct(&Char_t886, 5, 1, (tll_ptr)101);
                          instr_struct(&Char_t887, 5, 1, (tll_ptr)115);
                          instr_struct(&Char_t888, 5, 1, (tll_ptr)115);
                          instr_struct(&Char_t889, 5, 1, (tll_ptr)32);
                          instr_struct(&Char_t890, 5, 1, (tll_ptr)98);
                          instr_struct(&Char_t891, 5, 1, (tll_ptr)101);
                          instr_struct(&Char_t892, 5, 1, (tll_ptr)116);
                          instr_struct(&Char_t893, 5, 1, (tll_ptr)119);
                          instr_struct(&Char_t894, 5, 1, (tll_ptr)101);
                          instr_struct(&Char_t895, 5, 1, (tll_ptr)101);
                          instr_struct(&Char_t896, 5, 1, (tll_ptr)110);
                          instr_struct(&Char_t897, 5, 1, (tll_ptr)32);
                          instr_struct(&EmptyString_t898, 6, 0);
                          instr_struct(&String_t899, 7, 2,
                                       Char_t897, EmptyString_t898);
                          instr_struct(&String_t900, 7, 2,
                                       Char_t896, String_t899);
                          instr_struct(&String_t901, 7, 2,
                                       Char_t895, String_t900);
                          instr_struct(&String_t902, 7, 2,
                                       Char_t894, String_t901);
                          instr_struct(&String_t903, 7, 2,
                                       Char_t893, String_t902);
                          instr_struct(&String_t904, 7, 2,
                                       Char_t892, String_t903);
                          instr_struct(&String_t905, 7, 2,
                                       Char_t891, String_t904);
                          instr_struct(&String_t906, 7, 2,
                                       Char_t890, String_t905);
                          instr_struct(&String_t907, 7, 2,
                                       Char_t889, String_t906);
                          instr_struct(&String_t908, 7, 2,
                                       Char_t888, String_t907);
                          instr_struct(&String_t909, 7, 2,
                                       Char_t887, String_t908);
                          instr_struct(&String_t910, 7, 2,
                                       Char_t886, String_t909);
                          instr_struct(&String_t911, 7, 2,
                                       Char_t885, String_t910);
                          instr_struct(&String_t912, 7, 2,
                                       Char_t884, String_t911);
                          instr_struct(&String_t913, 7, 2,
                                       Char_t883, String_t912);
                          instr_struct(&String_t914, 7, 2,
                                       Char_t882, String_t913);
                          instr_struct(&String_t915, 7, 2,
                                       Char_t881, String_t914);
                          instr_struct(&String_t916, 7, 2,
                                       Char_t880, String_t915);
                          instr_struct(&String_t917, 7, 2,
                                       Char_t879, String_t916);
                          instr_struct(&String_t918, 7, 2,
                                       Char_t878, String_t917);
                          instr_struct(&String_t919, 7, 2,
                                       Char_t877, String_t918);
                          instr_struct(&String_t920, 7, 2,
                                       Char_t876, String_t919);
                          instr_struct(&String_t921, 7, 2,
                                       Char_t875, String_t920);
                          instr_struct(&String_t922, 7, 2,
                                       Char_t874, String_t921);
                          instr_struct(&String_t923, 7, 2,
                                       Char_t873, String_t922);
                          instr_struct(&String_t924, 7, 2,
                                       Char_t872, String_t923);
                          instr_struct(&String_t925, 7, 2,
                                       Char_t871, String_t924);
                          instr_struct(&String_t926, 7, 2,
                                       Char_t870, String_t925);
                          call_ret_t927 = string_of_nat_i38(lower_v38978);
                          call_ret_t869 = cats_i19(String_t926, call_ret_t927);
                          instr_struct(&Char_t928, 5, 1, (tll_ptr)32);
                          instr_struct(&Char_t929, 5, 1, (tll_ptr)97);
                          instr_struct(&Char_t930, 5, 1, (tll_ptr)110);
                          instr_struct(&Char_t931, 5, 1, (tll_ptr)100);
                          instr_struct(&Char_t932, 5, 1, (tll_ptr)32);
                          instr_struct(&EmptyString_t933, 6, 0);
                          instr_struct(&String_t934, 7, 2,
                                       Char_t932, EmptyString_t933);
                          instr_struct(&String_t935, 7, 2,
                                       Char_t931, String_t934);
                          instr_struct(&String_t936, 7, 2,
                                       Char_t930, String_t935);
                          instr_struct(&String_t937, 7, 2,
                                       Char_t929, String_t936);
                          instr_struct(&String_t938, 7, 2,
                                       Char_t928, String_t937);
                          call_ret_t868 = cats_i19(call_ret_t869, String_t938);
                          call_ret_t939 = string_of_nat_i38(upper_v38981);
                          call_ret_t867 = cats_i19(call_ret_t868,
                                                   call_ret_t939);
                          instr_struct(&Char_t940, 5, 1, (tll_ptr)46);
                          instr_struct(&Char_t941, 5, 1, (tll_ptr)10);
                          instr_struct(&EmptyString_t942, 6, 0);
                          instr_struct(&String_t943, 7, 2,
                                       Char_t941, EmptyString_t942);
                          instr_struct(&String_t944, 7, 2,
                                       Char_t940, String_t943);
                          call_ret_t866 = cats_i19(call_ret_t867, String_t944);
                          call_ret_t865 = print_i33(call_ret_t866);
                          instr_app(&app_ret_t945, call_ret_t865, 0);
                          instr_free_clo(call_ret_t865);
                          __v38992 = app_ret_t945;
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
                          instr_struct(&String_t959, 7, 2,
                                       Char_t957, EmptyString_t958);
                          instr_struct(&String_t960, 7, 2,
                                       Char_t956, String_t959);
                          instr_struct(&String_t961, 7, 2,
                                       Char_t955, String_t960);
                          instr_struct(&String_t962, 7, 2,
                                       Char_t954, String_t961);
                          instr_struct(&String_t963, 7, 2,
                                       Char_t953, String_t962);
                          instr_struct(&String_t964, 7, 2,
                                       Char_t952, String_t963);
                          instr_struct(&String_t965, 7, 2,
                                       Char_t951, String_t964);
                          instr_struct(&String_t966, 7, 2,
                                       Char_t950, String_t965);
                          instr_struct(&String_t967, 7, 2,
                                       Char_t949, String_t966);
                          call_ret_t968 = string_of_nat_i38(repeat_v38990);
                          call_ret_t948 = cats_i19(String_t967, call_ret_t968);
                          instr_struct(&Char_t969, 5, 1, (tll_ptr)32);
                          instr_struct(&Char_t970, 5, 1, (tll_ptr)116);
                          instr_struct(&Char_t971, 5, 1, (tll_ptr)114);
                          instr_struct(&Char_t972, 5, 1, (tll_ptr)105);
                          instr_struct(&Char_t973, 5, 1, (tll_ptr)101);
                          instr_struct(&Char_t974, 5, 1, (tll_ptr)115);
                          instr_struct(&Char_t975, 5, 1, (tll_ptr)46);
                          instr_struct(&Char_t976, 5, 1, (tll_ptr)10);
                          instr_struct(&EmptyString_t977, 6, 0);
                          instr_struct(&String_t978, 7, 2,
                                       Char_t976, EmptyString_t977);
                          instr_struct(&String_t979, 7, 2,
                                       Char_t975, String_t978);
                          instr_struct(&String_t980, 7, 2,
                                       Char_t974, String_t979);
                          instr_struct(&String_t981, 7, 2,
                                       Char_t973, String_t980);
                          instr_struct(&String_t982, 7, 2,
                                       Char_t972, String_t981);
                          instr_struct(&String_t983, 7, 2,
                                       Char_t971, String_t982);
                          instr_struct(&String_t984, 7, 2,
                                       Char_t970, String_t983);
                          instr_struct(&String_t985, 7, 2,
                                       Char_t969, String_t984);
                          call_ret_t947 = cats_i19(call_ret_t948, String_t985);
                          call_ret_t946 = print_i33(call_ret_t947);
                          instr_app(&app_ret_t986, call_ret_t946, 0);
                          instr_free_clo(call_ret_t946);
                          __v38993 = app_ret_t986;
                          call_ret_t987 = player_loop_i49(0, repeat_v38990,
                                                          c_v38991);
                          instr_app(&app_ret_t988, call_ret_t987, 0);
                          instr_free_clo(call_ret_t987);
                          switch_ret_t864 = app_ret_t988;
                          break;
                      }
                      switch_ret_t862 = switch_ret_t864;
                      break;
                  }
                  switch_ret_t860 = switch_ret_t862;
                  break;
              }
              switch_ret_t858 = switch_ret_t860;
              break;
          }
          switch_ret_t856 = switch_ret_t858;
          break;
      }
      switch_ret_t854 = switch_ret_t856;
      break;
  }
  return switch_ret_t854;
}

tll_ptr player_i50(tll_ptr c_v38958) {
  tll_ptr lam_clo_t990;
  instr_clo(&lam_clo_t990, &lam_fun_t989, 1, c_v38958);
  return lam_clo_t990;
}

tll_ptr lam_fun_t992(tll_ptr c_v38994, tll_env env) {
  tll_ptr call_ret_t991;
  call_ret_t991 = player_i50(c_v38994);
  return call_ret_t991;
}

tll_ptr lam_fun_t1005(tll_ptr __v39005, tll_env env) {
  tll_ptr __v39011; tll_ptr add_ret_t1000; tll_ptr add_ret_t1003;
  tll_ptr app_ret_t1001; tll_ptr app_ret_t1004; tll_ptr c_v39013;
  tll_ptr c_v39015; tll_ptr call_ret_t1002; tll_ptr call_ret_t996;
  tll_ptr call_ret_t999; tll_ptr n_v39012; tll_ptr ord_v39014;
  tll_ptr recv_msg_t994; tll_ptr send_ch_t997; tll_ptr switch_ret_t995;
  tll_ptr switch_ret_t998;
  instr_recv(&recv_msg_t994, env[0]);
  __v39011 = recv_msg_t994;
  switch(((tll_node)__v39011)->tag) {
    case 0:
      n_v39012 = ((tll_node)__v39011)->data[0];
      c_v39013 = ((tll_node)__v39011)->data[1];
      instr_free_struct(__v39011);
      call_ret_t996 = comparen_i10(env[2], n_v39012);
      ord_v39014 = call_ret_t996;
      instr_send(&send_ch_t997, c_v39013, ord_v39014);
      c_v39015 = send_ch_t997;
      switch(((tll_node)ord_v39014)->tag) {
        case 3:
          switch_ret_t998 = 0;
          break;
        case 1:
          add_ret_t1000 = env[1] - 1;
          call_ret_t999 = server_loop_i51(env[2], add_ret_t1000, c_v39015);
          instr_app(&app_ret_t1001, call_ret_t999, 0);
          switch_ret_t998 = app_ret_t1001;
          break;
        case 2:
          add_ret_t1003 = env[1] - 1;
          call_ret_t1002 = server_loop_i51(env[2], add_ret_t1003, c_v39015);
          instr_app(&app_ret_t1004, call_ret_t1002, 0);
          switch_ret_t998 = app_ret_t1004;
          break;
      }
      switch_ret_t995 = switch_ret_t998;
      break;
  }
  return switch_ret_t995;
}

tll_ptr lam_fun_t1007(tll_ptr c_v38998, tll_env env) {
  tll_ptr lam_clo_t1006;
  instr_clo(&lam_clo_t1006, &lam_fun_t1005, 3, c_v38998, env[0], env[1]);
  return lam_clo_t1006;
}

tll_ptr lam_fun_t1010(tll_ptr __v39019, tll_env env) {
  tll_ptr c_v39021; tll_ptr send_ch_t1009;
  instr_send(&send_ch_t1009, env[0], env[1]);
  c_v39021 = send_ch_t1009;
  return 0;
}

tll_ptr lam_fun_t1012(tll_ptr c_v39016, tll_env env) {
  tll_ptr lam_clo_t1011;
  instr_clo(&lam_clo_t1011, &lam_fun_t1010, 2, c_v39016, env[0]);
  return lam_clo_t1011;
}

tll_ptr server_loop_i51(tll_ptr ans_v38995, tll_ptr repeat_v38996, tll_ptr c_v38997) {
  tll_ptr app_ret_t1015; tll_ptr ifte_ret_t1014; tll_ptr lam_clo_t1008;
  tll_ptr lam_clo_t1013;
  if (repeat_v38996) {
    instr_clo(&lam_clo_t1008, &lam_fun_t1007, 2, repeat_v38996, ans_v38995);
    ifte_ret_t1014 = lam_clo_t1008;
  }
  else {
    instr_clo(&lam_clo_t1013, &lam_fun_t1012, 1, ans_v38995);
    ifte_ret_t1014 = lam_clo_t1013;
  }
  instr_app(&app_ret_t1015, ifte_ret_t1014, c_v38997);
  return app_ret_t1015;
}

tll_ptr lam_fun_t1017(tll_ptr c_v39027, tll_env env) {
  tll_ptr call_ret_t1016;
  call_ret_t1016 = server_loop_i51(env[1], env[0], c_v39027);
  return call_ret_t1016;
}

tll_ptr lam_fun_t1019(tll_ptr repeat_v39025, tll_env env) {
  tll_ptr lam_clo_t1018;
  instr_clo(&lam_clo_t1018, &lam_fun_t1017, 2, repeat_v39025, env[0]);
  return lam_clo_t1018;
}

tll_ptr lam_fun_t1021(tll_ptr ans_v39022, tll_env env) {
  tll_ptr lam_clo_t1020;
  instr_clo(&lam_clo_t1020, &lam_fun_t1019, 1, ans_v39022);
  return lam_clo_t1020;
}

tll_ptr lam_fun_t1030(tll_ptr __v39029, tll_env env) {
  tll_ptr ans_v39038; tll_ptr app_ret_t1029; tll_ptr c_v39041;
  tll_ptr c_v39042; tll_ptr c_v39043; tll_ptr call_ret_t1028;
  tll_ptr pf1_v39039; tll_ptr pf2_v39040; tll_ptr rand_tmp_t1023;
  tll_ptr res_v39037; tll_ptr send_ch_t1025; tll_ptr send_ch_t1026;
  tll_ptr send_ch_t1027; tll_ptr switch_ret_t1024;
  instr_rand(&rand_tmp_t1023, (tll_ptr)1, (tll_ptr)128);
  res_v39037 = rand_tmp_t1023;
  switch(((tll_node)res_v39037)->tag) {
    case 4:
      ans_v39038 = ((tll_node)res_v39037)->data[0];
      pf1_v39039 = ((tll_node)res_v39037)->data[1];
      pf2_v39040 = ((tll_node)res_v39037)->data[2];
      instr_send(&send_ch_t1025, env[0], (tll_ptr)1);
      c_v39041 = send_ch_t1025;
      instr_send(&send_ch_t1026, c_v39041, (tll_ptr)128);
      c_v39042 = send_ch_t1026;
      instr_send(&send_ch_t1027, c_v39042, (tll_ptr)7);
      c_v39043 = send_ch_t1027;
      call_ret_t1028 = server_loop_i51(ans_v39038, (tll_ptr)7, c_v39043);
      instr_app(&app_ret_t1029, call_ret_t1028, 0);
      instr_free_clo(call_ret_t1028);
      switch_ret_t1024 = app_ret_t1029;
      break;
  }
  return switch_ret_t1024;
}

tll_ptr server_i52(tll_ptr c_v39028) {
  tll_ptr lam_clo_t1031;
  instr_clo(&lam_clo_t1031, &lam_fun_t1030, 1, c_v39028);
  return lam_clo_t1031;
}

tll_ptr lam_fun_t1033(tll_ptr c_v39044, tll_env env) {
  tll_ptr call_ret_t1032;
  call_ret_t1032 = server_i52(c_v39044);
  return call_ret_t1032;
}

tll_ptr fork_fun_t1037(tll_env env) {
  tll_ptr app_ret_t1036; tll_ptr call_ret_t1035; tll_ptr fork_ret_t1039;
  call_ret_t1035 = server_i52(env[0]);
  instr_app(&app_ret_t1036, call_ret_t1035, 0);
  instr_free_clo(call_ret_t1035);
  fork_ret_t1039 = app_ret_t1036;
  instr_free_thread(env);
  return fork_ret_t1039;
}

tll_ptr fork_fun_t1045(tll_env env) {
  tll_ptr __v39054; tll_ptr __v39057; tll_ptr app_ret_t1043;
  tll_ptr c0_v39056; tll_ptr c0_v39058; tll_ptr c_v39055;
  tll_ptr call_ret_t1042; tll_ptr fork_ret_t1047; tll_ptr recv_msg_t1040;
  tll_ptr send_ch_t1044; tll_ptr switch_ret_t1041;
  instr_recv(&recv_msg_t1040, env[0]);
  __v39054 = recv_msg_t1040;
  switch(((tll_node)__v39054)->tag) {
    case 0:
      c_v39055 = ((tll_node)__v39054)->data[0];
      c0_v39056 = ((tll_node)__v39054)->data[1];
      instr_free_struct(__v39054);
      call_ret_t1042 = player_i50(c_v39055);
      instr_app(&app_ret_t1043, call_ret_t1042, 0);
      instr_free_clo(call_ret_t1042);
      __v39057 = app_ret_t1043;
      instr_send(&send_ch_t1044, c0_v39056, 0);
      c0_v39058 = send_ch_t1044;
      switch_ret_t1041 = 0;
      break;
  }
  fork_ret_t1047 = switch_ret_t1041;
  instr_free_thread(env);
  return fork_ret_t1047;
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
  tll_ptr String_t363; tll_ptr String_t366; tll_ptr __v39060;
  tll_ptr __v39061; tll_ptr c0_v39047; tll_ptr c0_v39059; tll_ptr c0_v39062;
  tll_ptr c_v39045; tll_ptr close_tmp_t1051; tll_ptr consUU_t368;
  tll_ptr consUU_t369; tll_ptr consUU_t370; tll_ptr consUU_t371;
  tll_ptr consUU_t372; tll_ptr consUU_t373; tll_ptr consUU_t374;
  tll_ptr consUU_t375; tll_ptr consUU_t376; tll_ptr consUU_t377;
  tll_ptr fork_ch_t1038; tll_ptr fork_ch_t1046; tll_ptr lam_clo_t1022;
  tll_ptr lam_clo_t1034; tll_ptr lam_clo_t104; tll_ptr lam_clo_t110;
  tll_ptr lam_clo_t118; tll_ptr lam_clo_t12; tll_ptr lam_clo_t126;
  tll_ptr lam_clo_t134; tll_ptr lam_clo_t140; tll_ptr lam_clo_t151;
  tll_ptr lam_clo_t16; tll_ptr lam_clo_t167; tll_ptr lam_clo_t179;
  tll_ptr lam_clo_t191; tll_ptr lam_clo_t203; tll_ptr lam_clo_t215;
  tll_ptr lam_clo_t227; tll_ptr lam_clo_t239; tll_ptr lam_clo_t252;
  tll_ptr lam_clo_t265; tll_ptr lam_clo_t278; tll_ptr lam_clo_t28;
  tll_ptr lam_clo_t288; tll_ptr lam_clo_t298; tll_ptr lam_clo_t308;
  tll_ptr lam_clo_t318; tll_ptr lam_clo_t327; tll_ptr lam_clo_t336;
  tll_ptr lam_clo_t34; tll_ptr lam_clo_t391; tll_ptr lam_clo_t396;
  tll_ptr lam_clo_t40; tll_ptr lam_clo_t406; tll_ptr lam_clo_t450;
  tll_ptr lam_clo_t46; tll_ptr lam_clo_t463; tll_ptr lam_clo_t467;
  tll_ptr lam_clo_t52; tll_ptr lam_clo_t541; tll_ptr lam_clo_t58;
  tll_ptr lam_clo_t6; tll_ptr lam_clo_t72; tll_ptr lam_clo_t77;
  tll_ptr lam_clo_t83; tll_ptr lam_clo_t852; tll_ptr lam_clo_t92;
  tll_ptr lam_clo_t98; tll_ptr lam_clo_t993; tll_ptr nilUU_t367;
  tll_ptr recv_msg_t1049; tll_ptr send_ch_t1048; tll_ptr switch_ret_t1050;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i70 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i71 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i72 = lam_clo_t16;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  comparebclo_i73 = lam_clo_t28;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 0);
  ltenclo_i74 = lam_clo_t34;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 0);
  gtenclo_i75 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  ltnclo_i76 = lam_clo_t46;
  instr_clo(&lam_clo_t52, &lam_fun_t51, 0);
  gtnclo_i77 = lam_clo_t52;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  eqnclo_i78 = lam_clo_t58;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  comparenclo_i79 = lam_clo_t72;
  instr_clo(&lam_clo_t77, &lam_fun_t76, 0);
  predclo_i80 = lam_clo_t77;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i81 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i82 = lam_clo_t92;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  mulnclo_i83 = lam_clo_t98;
  instr_clo(&lam_clo_t104, &lam_fun_t103, 0);
  divnclo_i84 = lam_clo_t104;
  instr_clo(&lam_clo_t110, &lam_fun_t109, 0);
  modnclo_i85 = lam_clo_t110;
  instr_clo(&lam_clo_t118, &lam_fun_t117, 0);
  eqcclo_i86 = lam_clo_t118;
  instr_clo(&lam_clo_t126, &lam_fun_t125, 0);
  comparecclo_i87 = lam_clo_t126;
  instr_clo(&lam_clo_t134, &lam_fun_t133, 0);
  catsclo_i88 = lam_clo_t134;
  instr_clo(&lam_clo_t140, &lam_fun_t139, 0);
  strlenclo_i89 = lam_clo_t140;
  instr_clo(&lam_clo_t151, &lam_fun_t150, 0);
  eqsclo_i90 = lam_clo_t151;
  instr_clo(&lam_clo_t167, &lam_fun_t166, 0);
  comparesclo_i91 = lam_clo_t167;
  instr_clo(&lam_clo_t179, &lam_fun_t178, 0);
  and_thenUUUclo_i92 = lam_clo_t179;
  instr_clo(&lam_clo_t191, &lam_fun_t190, 0);
  and_thenUULclo_i93 = lam_clo_t191;
  instr_clo(&lam_clo_t203, &lam_fun_t202, 0);
  and_thenULUclo_i94 = lam_clo_t203;
  instr_clo(&lam_clo_t215, &lam_fun_t214, 0);
  and_thenULLclo_i95 = lam_clo_t215;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 0);
  and_thenLULclo_i96 = lam_clo_t227;
  instr_clo(&lam_clo_t239, &lam_fun_t238, 0);
  and_thenLLLclo_i97 = lam_clo_t239;
  instr_clo(&lam_clo_t252, &lam_fun_t251, 0);
  lenUUclo_i98 = lam_clo_t252;
  instr_clo(&lam_clo_t265, &lam_fun_t264, 0);
  lenULclo_i99 = lam_clo_t265;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 0);
  lenLLclo_i100 = lam_clo_t278;
  instr_clo(&lam_clo_t288, &lam_fun_t287, 0);
  appendUUclo_i101 = lam_clo_t288;
  instr_clo(&lam_clo_t298, &lam_fun_t297, 0);
  appendULclo_i102 = lam_clo_t298;
  instr_clo(&lam_clo_t308, &lam_fun_t307, 0);
  appendLLclo_i103 = lam_clo_t308;
  instr_clo(&lam_clo_t318, &lam_fun_t317, 0);
  readlineclo_i104 = lam_clo_t318;
  instr_clo(&lam_clo_t327, &lam_fun_t326, 0);
  printclo_i105 = lam_clo_t327;
  instr_clo(&lam_clo_t336, &lam_fun_t335, 0);
  prerrclo_i106 = lam_clo_t336;
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
  instr_struct(&nilUU_t367, 26, 0);
  instr_struct(&consUU_t368, 27, 2, String_t366, nilUU_t367);
  instr_struct(&consUU_t369, 27, 2, String_t363, consUU_t368);
  instr_struct(&consUU_t370, 27, 2, String_t360, consUU_t369);
  instr_struct(&consUU_t371, 27, 2, String_t357, consUU_t370);
  instr_struct(&consUU_t372, 27, 2, String_t354, consUU_t371);
  instr_struct(&consUU_t373, 27, 2, String_t351, consUU_t372);
  instr_struct(&consUU_t374, 27, 2, String_t348, consUU_t373);
  instr_struct(&consUU_t375, 27, 2, String_t345, consUU_t374);
  instr_struct(&consUU_t376, 27, 2, String_t342, consUU_t375);
  instr_struct(&consUU_t377, 27, 2, String_t339, consUU_t376);
  digits_i35 = consUU_t377;
  instr_clo(&lam_clo_t391, &lam_fun_t390, 0);
  get_atclo_i107 = lam_clo_t391;
  instr_clo(&lam_clo_t396, &lam_fun_t395, 0);
  string_of_digitclo_i108 = lam_clo_t396;
  instr_clo(&lam_clo_t406, &lam_fun_t405, 0);
  string_of_natclo_i109 = lam_clo_t406;
  instr_clo(&lam_clo_t450, &lam_fun_t449, 0);
  digit_of_charclo_i110 = lam_clo_t450;
  instr_clo(&lam_clo_t463, &lam_fun_t462, 0);
  nat_of_string_loopclo_i111 = lam_clo_t463;
  instr_clo(&lam_clo_t467, &lam_fun_t466, 0);
  nat_of_stringclo_i112 = lam_clo_t467;
  instr_clo(&lam_clo_t541, &lam_fun_t540, 0);
  read_natclo_i113 = lam_clo_t541;
  instr_clo(&lam_clo_t852, &lam_fun_t851, 0);
  player_loopclo_i114 = lam_clo_t852;
  instr_clo(&lam_clo_t993, &lam_fun_t992, 0);
  playerclo_i115 = lam_clo_t993;
  instr_clo(&lam_clo_t1022, &lam_fun_t1021, 0);
  server_loopclo_i116 = lam_clo_t1022;
  instr_clo(&lam_clo_t1034, &lam_fun_t1033, 0);
  serverclo_i117 = lam_clo_t1034;
  instr_fork(&fork_ch_t1038, &fork_fun_t1037, 0);
  c_v39045 = fork_ch_t1038;
  instr_fork(&fork_ch_t1046, &fork_fun_t1045, 0);
  c0_v39047 = fork_ch_t1046;
  instr_send(&send_ch_t1048, c0_v39047, c_v39045);
  c0_v39059 = send_ch_t1048;
  instr_recv(&recv_msg_t1049, c0_v39059);
  __v39060 = recv_msg_t1049;
  switch(((tll_node)__v39060)->tag) {
    case 0:
      __v39061 = ((tll_node)__v39060)->data[0];
      c0_v39062 = ((tll_node)__v39060)->data[1];
      instr_free_struct(__v39060);
      instr_close(&close_tmp_t1051, c0_v39062);
      switch_ret_t1050 = close_tmp_t1051;
      break;
  }
  return 0;
}

