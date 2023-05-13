#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v36490, tll_ptr b2_v36491);
tll_ptr orb_i2(tll_ptr b1_v36495, tll_ptr b2_v36496);
tll_ptr notb_i3(tll_ptr b_v36500);
tll_ptr compareb_i4(tll_ptr b1_v36502, tll_ptr b2_v36503);
tll_ptr lten_i5(tll_ptr x_v36507, tll_ptr y_v36508);
tll_ptr gten_i6(tll_ptr x_v36512, tll_ptr y_v36513);
tll_ptr ltn_i7(tll_ptr x_v36517, tll_ptr y_v36518);
tll_ptr gtn_i8(tll_ptr x_v36522, tll_ptr y_v36523);
tll_ptr eqn_i9(tll_ptr x_v36527, tll_ptr y_v36528);
tll_ptr comparen_i10(tll_ptr n1_v36532, tll_ptr n2_v36533);
tll_ptr pred_i11(tll_ptr x_v36537);
tll_ptr addn_i12(tll_ptr x_v36539, tll_ptr y_v36540);
tll_ptr subn_i13(tll_ptr x_v36544, tll_ptr y_v36545);
tll_ptr muln_i14(tll_ptr x_v36549, tll_ptr y_v36550);
tll_ptr divn_i15(tll_ptr x_v36554, tll_ptr y_v36555);
tll_ptr modn_i16(tll_ptr x_v36559, tll_ptr y_v36560);
tll_ptr eqc_i17(tll_ptr c1_v36564, tll_ptr c2_v36565);
tll_ptr comparec_i18(tll_ptr c1_v36571, tll_ptr c2_v36572);
tll_ptr cats_i19(tll_ptr s1_v36578, tll_ptr s2_v36579);
tll_ptr strlen_i20(tll_ptr s_v36585);
tll_ptr eqs_i21(tll_ptr s1_v36589, tll_ptr s2_v36590);
tll_ptr compares_i22(tll_ptr s1_v36600, tll_ptr s2_v36601);
tll_ptr and_thenUUU_i61(tll_ptr A_v36611, tll_ptr B_v36612, tll_ptr opt_v36613, tll_ptr f_v36614);
tll_ptr and_thenUUL_i60(tll_ptr A_v36626, tll_ptr B_v36627, tll_ptr opt_v36628, tll_ptr f_v36629);
tll_ptr and_thenULU_i59(tll_ptr A_v36641, tll_ptr B_v36642, tll_ptr opt_v36643, tll_ptr f_v36644);
tll_ptr and_thenULL_i58(tll_ptr A_v36656, tll_ptr B_v36657, tll_ptr opt_v36658, tll_ptr f_v36659);
tll_ptr and_thenLUL_i56(tll_ptr A_v36671, tll_ptr B_v36672, tll_ptr opt_v36673, tll_ptr f_v36674);
tll_ptr and_thenLLL_i54(tll_ptr A_v36686, tll_ptr B_v36687, tll_ptr opt_v36688, tll_ptr f_v36689);
tll_ptr lenUU_i65(tll_ptr A_v36701, tll_ptr xs_v36702);
tll_ptr lenUL_i64(tll_ptr A_v36710, tll_ptr xs_v36711);
tll_ptr lenLL_i62(tll_ptr A_v36719, tll_ptr xs_v36720);
tll_ptr appendUU_i69(tll_ptr A_v36728, tll_ptr xs_v36729, tll_ptr ys_v36730);
tll_ptr appendUL_i68(tll_ptr A_v36739, tll_ptr xs_v36740, tll_ptr ys_v36741);
tll_ptr appendLL_i66(tll_ptr A_v36750, tll_ptr xs_v36751, tll_ptr ys_v36752);
tll_ptr readline_i32(tll_ptr __v36761);
tll_ptr print_i33(tll_ptr s_v36776);
tll_ptr prerr_i34(tll_ptr s_v36787);
tll_ptr get_at_i36(tll_ptr A_v36798, tll_ptr n_v36799, tll_ptr xs_v36800, tll_ptr a_v36801);
tll_ptr string_of_digit_i37(tll_ptr n_v36816);
tll_ptr string_of_nat_i38(tll_ptr n_v36818);
tll_ptr digit_of_char_i39(tll_ptr c_v36822);
tll_ptr nat_of_string_loop_i40(tll_ptr s_v36824, tll_ptr acc_v36825);
tll_ptr nat_of_string_i41(tll_ptr s_v36832);
tll_ptr read_nat_i48(tll_ptr __v36834);
tll_ptr player_loop_i49(tll_ptr ans_v36843, tll_ptr repeat_v36844, tll_ptr c_v36845);
tll_ptr player_i50(tll_ptr c_v36891);
tll_ptr server_loop_i51(tll_ptr ans_v36928, tll_ptr repeat_v36929, tll_ptr c_v36930);
tll_ptr server_i52(tll_ptr c_v36958);

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

tll_ptr andb_i1(tll_ptr b1_v36490, tll_ptr b2_v36491) {
  tll_ptr ifte_ret_t1;
  if (b1_v36490) {
    ifte_ret_t1 = b2_v36491;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v36494, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v36494);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v36492, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v36492);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v36495, tll_ptr b2_v36496) {
  tll_ptr ifte_ret_t7;
  if (b1_v36495) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v36496;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v36499, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v36499);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v36497, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v36497);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v36500) {
  tll_ptr ifte_ret_t13;
  if (b_v36500) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v36501, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v36501);
  return call_ret_t14;
}

tll_ptr compareb_i4(tll_ptr b1_v36502, tll_ptr b2_v36503) {
  tll_ptr EQ_t17; tll_ptr EQ_t21; tll_ptr GT_t18; tll_ptr LT_t20;
  tll_ptr ifte_ret_t19; tll_ptr ifte_ret_t22; tll_ptr ifte_ret_t23;
  if (b1_v36502) {
    if (b2_v36503) {
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
    if (b2_v36503) {
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

tll_ptr lam_fun_t25(tll_ptr b2_v36506, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = compareb_i4(env[0], b2_v36506);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr b1_v36504, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, b1_v36504);
  return lam_clo_t26;
}

tll_ptr lten_i5(tll_ptr x_v36507, tll_ptr y_v36508) {
  tll_ptr lten_ret_t29;
  instr_lten(&lten_ret_t29, x_v36507, y_v36508);
  return lten_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v36511, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = lten_i5(env[0], y_v36511);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v36509, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v36509);
  return lam_clo_t32;
}

tll_ptr gten_i6(tll_ptr x_v36512, tll_ptr y_v36513) {
  tll_ptr gten_ret_t35;
  instr_gten(&gten_ret_t35, x_v36512, y_v36513);
  return gten_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v36516, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = gten_i6(env[0], y_v36516);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v36514, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v36514);
  return lam_clo_t38;
}

tll_ptr ltn_i7(tll_ptr x_v36517, tll_ptr y_v36518) {
  tll_ptr ltn_ret_t41;
  instr_ltn(&ltn_ret_t41, x_v36517, y_v36518);
  return ltn_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v36521, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = ltn_i7(env[0], y_v36521);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v36519, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v36519);
  return lam_clo_t44;
}

tll_ptr gtn_i8(tll_ptr x_v36522, tll_ptr y_v36523) {
  tll_ptr gtn_ret_t47;
  instr_gtn(&gtn_ret_t47, x_v36522, y_v36523);
  return gtn_ret_t47;
}

tll_ptr lam_fun_t49(tll_ptr y_v36526, tll_env env) {
  tll_ptr call_ret_t48;
  call_ret_t48 = gtn_i8(env[0], y_v36526);
  return call_ret_t48;
}

tll_ptr lam_fun_t51(tll_ptr x_v36524, tll_env env) {
  tll_ptr lam_clo_t50;
  instr_clo(&lam_clo_t50, &lam_fun_t49, 1, x_v36524);
  return lam_clo_t50;
}

tll_ptr eqn_i9(tll_ptr x_v36527, tll_ptr y_v36528) {
  tll_ptr eqn_ret_t53;
  instr_eqn(&eqn_ret_t53, x_v36527, y_v36528);
  return eqn_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v36531, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = eqn_i9(env[0], y_v36531);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v36529, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v36529);
  return lam_clo_t56;
}

tll_ptr comparen_i10(tll_ptr n1_v36532, tll_ptr n2_v36533) {
  tll_ptr EQ_t65; tll_ptr GT_t62; tll_ptr LT_t64; tll_ptr add_ret_t60;
  tll_ptr add_ret_t61; tll_ptr call_ret_t59; tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t66; tll_ptr ifte_ret_t67;
  if (n1_v36532) {
    if (n2_v36533) {
      add_ret_t60 = n1_v36532 - 1;
      add_ret_t61 = n2_v36533 - 1;
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
    if (n2_v36533) {
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

tll_ptr lam_fun_t69(tll_ptr n2_v36536, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = comparen_i10(env[0], n2_v36536);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr n1_v36534, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, n1_v36534);
  return lam_clo_t70;
}

tll_ptr pred_i11(tll_ptr x_v36537) {
  tll_ptr add_ret_t73; tll_ptr ifte_ret_t74;
  if (x_v36537) {
    add_ret_t73 = x_v36537 - 1;
    ifte_ret_t74 = add_ret_t73;
  }
  else {
    ifte_ret_t74 = (tll_ptr)0;
  }
  return ifte_ret_t74;
}

tll_ptr lam_fun_t76(tll_ptr x_v36538, tll_env env) {
  tll_ptr call_ret_t75;
  call_ret_t75 = pred_i11(x_v36538);
  return call_ret_t75;
}

tll_ptr addn_i12(tll_ptr x_v36539, tll_ptr y_v36540) {
  tll_ptr addn_ret_t78;
  instr_addn(&addn_ret_t78, x_v36539, y_v36540);
  return addn_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v36543, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i12(env[0], y_v36543);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v36541, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v36541);
  return lam_clo_t81;
}

tll_ptr subn_i13(tll_ptr x_v36544, tll_ptr y_v36545) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v36545) {
    call_ret_t85 = pred_i11(x_v36544);
    add_ret_t86 = y_v36545 - 1;
    call_ret_t84 = subn_i13(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v36544;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v36548, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i13(env[0], y_v36548);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v36546, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v36546);
  return lam_clo_t90;
}

tll_ptr muln_i14(tll_ptr x_v36549, tll_ptr y_v36550) {
  tll_ptr muln_ret_t93;
  instr_muln(&muln_ret_t93, x_v36549, y_v36550);
  return muln_ret_t93;
}

tll_ptr lam_fun_t95(tll_ptr y_v36553, tll_env env) {
  tll_ptr call_ret_t94;
  call_ret_t94 = muln_i14(env[0], y_v36553);
  return call_ret_t94;
}

tll_ptr lam_fun_t97(tll_ptr x_v36551, tll_env env) {
  tll_ptr lam_clo_t96;
  instr_clo(&lam_clo_t96, &lam_fun_t95, 1, x_v36551);
  return lam_clo_t96;
}

tll_ptr divn_i15(tll_ptr x_v36554, tll_ptr y_v36555) {
  tll_ptr divn_ret_t99;
  instr_divn(&divn_ret_t99, x_v36554, y_v36555);
  return divn_ret_t99;
}

tll_ptr lam_fun_t101(tll_ptr y_v36558, tll_env env) {
  tll_ptr call_ret_t100;
  call_ret_t100 = divn_i15(env[0], y_v36558);
  return call_ret_t100;
}

tll_ptr lam_fun_t103(tll_ptr x_v36556, tll_env env) {
  tll_ptr lam_clo_t102;
  instr_clo(&lam_clo_t102, &lam_fun_t101, 1, x_v36556);
  return lam_clo_t102;
}

tll_ptr modn_i16(tll_ptr x_v36559, tll_ptr y_v36560) {
  tll_ptr modn_ret_t105;
  instr_modn(&modn_ret_t105, x_v36559, y_v36560);
  return modn_ret_t105;
}

tll_ptr lam_fun_t107(tll_ptr y_v36563, tll_env env) {
  tll_ptr call_ret_t106;
  call_ret_t106 = modn_i16(env[0], y_v36563);
  return call_ret_t106;
}

tll_ptr lam_fun_t109(tll_ptr x_v36561, tll_env env) {
  tll_ptr lam_clo_t108;
  instr_clo(&lam_clo_t108, &lam_fun_t107, 1, x_v36561);
  return lam_clo_t108;
}

tll_ptr eqc_i17(tll_ptr c1_v36564, tll_ptr c2_v36565) {
  tll_ptr call_ret_t113; tll_ptr n1_v36566; tll_ptr n2_v36567;
  tll_ptr switch_ret_t111; tll_ptr switch_ret_t112;
  switch(((tll_node)c1_v36564)->tag) {
    case 4:
      n1_v36566 = ((tll_node)c1_v36564)->data[0];
      switch(((tll_node)c2_v36565)->tag) {
        case 4:
          n2_v36567 = ((tll_node)c2_v36565)->data[0];
          call_ret_t113 = eqn_i9(n1_v36566, n2_v36567);
          switch_ret_t112 = call_ret_t113;
          break;
      }
      switch_ret_t111 = switch_ret_t112;
      break;
  }
  return switch_ret_t111;
}

tll_ptr lam_fun_t115(tll_ptr c2_v36570, tll_env env) {
  tll_ptr call_ret_t114;
  call_ret_t114 = eqc_i17(env[0], c2_v36570);
  return call_ret_t114;
}

tll_ptr lam_fun_t117(tll_ptr c1_v36568, tll_env env) {
  tll_ptr lam_clo_t116;
  instr_clo(&lam_clo_t116, &lam_fun_t115, 1, c1_v36568);
  return lam_clo_t116;
}

tll_ptr comparec_i18(tll_ptr c1_v36571, tll_ptr c2_v36572) {
  tll_ptr call_ret_t121; tll_ptr n1_v36573; tll_ptr n2_v36574;
  tll_ptr switch_ret_t119; tll_ptr switch_ret_t120;
  switch(((tll_node)c1_v36571)->tag) {
    case 4:
      n1_v36573 = ((tll_node)c1_v36571)->data[0];
      switch(((tll_node)c2_v36572)->tag) {
        case 4:
          n2_v36574 = ((tll_node)c2_v36572)->data[0];
          call_ret_t121 = comparen_i10(n1_v36573, n2_v36574);
          switch_ret_t120 = call_ret_t121;
          break;
      }
      switch_ret_t119 = switch_ret_t120;
      break;
  }
  return switch_ret_t119;
}

tll_ptr lam_fun_t123(tll_ptr c2_v36577, tll_env env) {
  tll_ptr call_ret_t122;
  call_ret_t122 = comparec_i18(env[0], c2_v36577);
  return call_ret_t122;
}

tll_ptr lam_fun_t125(tll_ptr c1_v36575, tll_env env) {
  tll_ptr lam_clo_t124;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 1, c1_v36575);
  return lam_clo_t124;
}

tll_ptr cats_i19(tll_ptr s1_v36578, tll_ptr s2_v36579) {
  tll_ptr String_t129; tll_ptr c_v36580; tll_ptr call_ret_t128;
  tll_ptr s1_v36581; tll_ptr switch_ret_t127;
  switch(((tll_node)s1_v36578)->tag) {
    case 5:
      switch_ret_t127 = s2_v36579;
      break;
    case 6:
      c_v36580 = ((tll_node)s1_v36578)->data[0];
      s1_v36581 = ((tll_node)s1_v36578)->data[1];
      call_ret_t128 = cats_i19(s1_v36581, s2_v36579);
      instr_struct(&String_t129, 6, 2, c_v36580, call_ret_t128);
      switch_ret_t127 = String_t129;
      break;
  }
  return switch_ret_t127;
}

tll_ptr lam_fun_t131(tll_ptr s2_v36584, tll_env env) {
  tll_ptr call_ret_t130;
  call_ret_t130 = cats_i19(env[0], s2_v36584);
  return call_ret_t130;
}

tll_ptr lam_fun_t133(tll_ptr s1_v36582, tll_env env) {
  tll_ptr lam_clo_t132;
  instr_clo(&lam_clo_t132, &lam_fun_t131, 1, s1_v36582);
  return lam_clo_t132;
}

tll_ptr strlen_i20(tll_ptr s_v36585) {
  tll_ptr __v36586; tll_ptr add_ret_t137; tll_ptr call_ret_t136;
  tll_ptr s_v36587; tll_ptr switch_ret_t135;
  switch(((tll_node)s_v36585)->tag) {
    case 5:
      switch_ret_t135 = (tll_ptr)0;
      break;
    case 6:
      __v36586 = ((tll_node)s_v36585)->data[0];
      s_v36587 = ((tll_node)s_v36585)->data[1];
      call_ret_t136 = strlen_i20(s_v36587);
      add_ret_t137 = call_ret_t136 + 1;
      switch_ret_t135 = add_ret_t137;
      break;
  }
  return switch_ret_t135;
}

tll_ptr lam_fun_t139(tll_ptr s_v36588, tll_env env) {
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i20(s_v36588);
  return call_ret_t138;
}

tll_ptr eqs_i21(tll_ptr s1_v36589, tll_ptr s2_v36590) {
  tll_ptr __v36591; tll_ptr __v36592; tll_ptr c1_v36593; tll_ptr c2_v36595;
  tll_ptr call_ret_t144; tll_ptr call_ret_t145; tll_ptr call_ret_t146;
  tll_ptr s1_v36594; tll_ptr s2_v36596; tll_ptr switch_ret_t141;
  tll_ptr switch_ret_t142; tll_ptr switch_ret_t143;
  switch(((tll_node)s1_v36589)->tag) {
    case 5:
      switch(((tll_node)s2_v36590)->tag) {
        case 5:
          switch_ret_t142 = (tll_ptr)1;
          break;
        case 6:
          __v36591 = ((tll_node)s2_v36590)->data[0];
          __v36592 = ((tll_node)s2_v36590)->data[1];
          switch_ret_t142 = (tll_ptr)0;
          break;
      }
      switch_ret_t141 = switch_ret_t142;
      break;
    case 6:
      c1_v36593 = ((tll_node)s1_v36589)->data[0];
      s1_v36594 = ((tll_node)s1_v36589)->data[1];
      switch(((tll_node)s2_v36590)->tag) {
        case 5:
          switch_ret_t143 = (tll_ptr)0;
          break;
        case 6:
          c2_v36595 = ((tll_node)s2_v36590)->data[0];
          s2_v36596 = ((tll_node)s2_v36590)->data[1];
          call_ret_t145 = eqc_i17(c1_v36593, c2_v36595);
          call_ret_t146 = eqs_i21(s1_v36594, s2_v36596);
          call_ret_t144 = andb_i1(call_ret_t145, call_ret_t146);
          switch_ret_t143 = call_ret_t144;
          break;
      }
      switch_ret_t141 = switch_ret_t143;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t148(tll_ptr s2_v36599, tll_env env) {
  tll_ptr call_ret_t147;
  call_ret_t147 = eqs_i21(env[0], s2_v36599);
  return call_ret_t147;
}

tll_ptr lam_fun_t150(tll_ptr s1_v36597, tll_env env) {
  tll_ptr lam_clo_t149;
  instr_clo(&lam_clo_t149, &lam_fun_t148, 1, s1_v36597);
  return lam_clo_t149;
}

tll_ptr compares_i22(tll_ptr s1_v36600, tll_ptr s2_v36601) {
  tll_ptr EQ_t154; tll_ptr GT_t157; tll_ptr GT_t162; tll_ptr LT_t155;
  tll_ptr LT_t161; tll_ptr __v36602; tll_ptr __v36603; tll_ptr c1_v36604;
  tll_ptr c2_v36606; tll_ptr call_ret_t158; tll_ptr call_ret_t160;
  tll_ptr s1_v36605; tll_ptr s2_v36607; tll_ptr switch_ret_t152;
  tll_ptr switch_ret_t153; tll_ptr switch_ret_t156; tll_ptr switch_ret_t159;
  switch(((tll_node)s1_v36600)->tag) {
    case 5:
      switch(((tll_node)s2_v36601)->tag) {
        case 5:
          instr_struct(&EQ_t154, 3, 0);
          switch_ret_t153 = EQ_t154;
          break;
        case 6:
          __v36602 = ((tll_node)s2_v36601)->data[0];
          __v36603 = ((tll_node)s2_v36601)->data[1];
          instr_struct(&LT_t155, 1, 0);
          switch_ret_t153 = LT_t155;
          break;
      }
      switch_ret_t152 = switch_ret_t153;
      break;
    case 6:
      c1_v36604 = ((tll_node)s1_v36600)->data[0];
      s1_v36605 = ((tll_node)s1_v36600)->data[1];
      switch(((tll_node)s2_v36601)->tag) {
        case 5:
          instr_struct(&GT_t157, 2, 0);
          switch_ret_t156 = GT_t157;
          break;
        case 6:
          c2_v36606 = ((tll_node)s2_v36601)->data[0];
          s2_v36607 = ((tll_node)s2_v36601)->data[1];
          call_ret_t158 = comparec_i18(c1_v36604, c2_v36606);
          switch(((tll_node)call_ret_t158)->tag) {
            case 3:
              call_ret_t160 = compares_i22(s1_v36605, s2_v36607);
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

tll_ptr lam_fun_t164(tll_ptr s2_v36610, tll_env env) {
  tll_ptr call_ret_t163;
  call_ret_t163 = compares_i22(env[0], s2_v36610);
  return call_ret_t163;
}

tll_ptr lam_fun_t166(tll_ptr s1_v36608, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, s1_v36608);
  return lam_clo_t165;
}

tll_ptr and_thenUUU_i61(tll_ptr A_v36611, tll_ptr B_v36612, tll_ptr opt_v36613, tll_ptr f_v36614) {
  tll_ptr NoneUU_t169; tll_ptr app_ret_t170; tll_ptr switch_ret_t168;
  tll_ptr x_v36615;
  switch(((tll_node)opt_v36613)->tag) {
    case 17:
      instr_struct(&NoneUU_t169, 17, 0);
      switch_ret_t168 = NoneUU_t169;
      break;
    case 18:
      x_v36615 = ((tll_node)opt_v36613)->data[0];
      instr_app(&app_ret_t170, f_v36614, x_v36615);
      switch_ret_t168 = app_ret_t170;
      break;
  }
  return switch_ret_t168;
}

tll_ptr lam_fun_t172(tll_ptr f_v36625, tll_env env) {
  tll_ptr call_ret_t171;
  call_ret_t171 = and_thenUUU_i61(env[2], env[1], env[0], f_v36625);
  return call_ret_t171;
}

tll_ptr lam_fun_t174(tll_ptr opt_v36623, tll_env env) {
  tll_ptr lam_clo_t173;
  instr_clo(&lam_clo_t173, &lam_fun_t172, 3, opt_v36623, env[0], env[1]);
  return lam_clo_t173;
}

tll_ptr lam_fun_t176(tll_ptr B_v36620, tll_env env) {
  tll_ptr lam_clo_t175;
  instr_clo(&lam_clo_t175, &lam_fun_t174, 2, B_v36620, env[0]);
  return lam_clo_t175;
}

tll_ptr lam_fun_t178(tll_ptr A_v36616, tll_env env) {
  tll_ptr lam_clo_t177;
  instr_clo(&lam_clo_t177, &lam_fun_t176, 1, A_v36616);
  return lam_clo_t177;
}

tll_ptr and_thenUUL_i60(tll_ptr A_v36626, tll_ptr B_v36627, tll_ptr opt_v36628, tll_ptr f_v36629) {
  tll_ptr NoneUL_t181; tll_ptr app_ret_t182; tll_ptr switch_ret_t180;
  tll_ptr x_v36630;
  switch(((tll_node)opt_v36628)->tag) {
    case 15:
      instr_free_struct(opt_v36628);
      instr_struct(&NoneUL_t181, 15, 0);
      switch_ret_t180 = NoneUL_t181;
      break;
    case 16:
      x_v36630 = ((tll_node)opt_v36628)->data[0];
      instr_free_struct(opt_v36628);
      instr_app(&app_ret_t182, f_v36629, x_v36630);
      switch_ret_t180 = app_ret_t182;
      break;
  }
  return switch_ret_t180;
}

tll_ptr lam_fun_t184(tll_ptr f_v36640, tll_env env) {
  tll_ptr call_ret_t183;
  call_ret_t183 = and_thenUUL_i60(env[2], env[1], env[0], f_v36640);
  return call_ret_t183;
}

tll_ptr lam_fun_t186(tll_ptr opt_v36638, tll_env env) {
  tll_ptr lam_clo_t185;
  instr_clo(&lam_clo_t185, &lam_fun_t184, 3, opt_v36638, env[0], env[1]);
  return lam_clo_t185;
}

tll_ptr lam_fun_t188(tll_ptr B_v36635, tll_env env) {
  tll_ptr lam_clo_t187;
  instr_clo(&lam_clo_t187, &lam_fun_t186, 2, B_v36635, env[0]);
  return lam_clo_t187;
}

tll_ptr lam_fun_t190(tll_ptr A_v36631, tll_env env) {
  tll_ptr lam_clo_t189;
  instr_clo(&lam_clo_t189, &lam_fun_t188, 1, A_v36631);
  return lam_clo_t189;
}

tll_ptr and_thenULU_i59(tll_ptr A_v36641, tll_ptr B_v36642, tll_ptr opt_v36643, tll_ptr f_v36644) {
  tll_ptr NoneLU_t193; tll_ptr app_ret_t194; tll_ptr switch_ret_t192;
  tll_ptr x_v36645;
  switch(((tll_node)opt_v36643)->tag) {
    case 17:
      instr_struct(&NoneLU_t193, 13, 0);
      switch_ret_t192 = NoneLU_t193;
      break;
    case 18:
      x_v36645 = ((tll_node)opt_v36643)->data[0];
      instr_app(&app_ret_t194, f_v36644, x_v36645);
      switch_ret_t192 = app_ret_t194;
      break;
  }
  return switch_ret_t192;
}

tll_ptr lam_fun_t196(tll_ptr f_v36655, tll_env env) {
  tll_ptr call_ret_t195;
  call_ret_t195 = and_thenULU_i59(env[2], env[1], env[0], f_v36655);
  return call_ret_t195;
}

tll_ptr lam_fun_t198(tll_ptr opt_v36653, tll_env env) {
  tll_ptr lam_clo_t197;
  instr_clo(&lam_clo_t197, &lam_fun_t196, 3, opt_v36653, env[0], env[1]);
  return lam_clo_t197;
}

tll_ptr lam_fun_t200(tll_ptr B_v36650, tll_env env) {
  tll_ptr lam_clo_t199;
  instr_clo(&lam_clo_t199, &lam_fun_t198, 2, B_v36650, env[0]);
  return lam_clo_t199;
}

tll_ptr lam_fun_t202(tll_ptr A_v36646, tll_env env) {
  tll_ptr lam_clo_t201;
  instr_clo(&lam_clo_t201, &lam_fun_t200, 1, A_v36646);
  return lam_clo_t201;
}

tll_ptr and_thenULL_i58(tll_ptr A_v36656, tll_ptr B_v36657, tll_ptr opt_v36658, tll_ptr f_v36659) {
  tll_ptr NoneLL_t205; tll_ptr app_ret_t206; tll_ptr switch_ret_t204;
  tll_ptr x_v36660;
  switch(((tll_node)opt_v36658)->tag) {
    case 15:
      instr_free_struct(opt_v36658);
      instr_struct(&NoneLL_t205, 11, 0);
      switch_ret_t204 = NoneLL_t205;
      break;
    case 16:
      x_v36660 = ((tll_node)opt_v36658)->data[0];
      instr_free_struct(opt_v36658);
      instr_app(&app_ret_t206, f_v36659, x_v36660);
      switch_ret_t204 = app_ret_t206;
      break;
  }
  return switch_ret_t204;
}

tll_ptr lam_fun_t208(tll_ptr f_v36670, tll_env env) {
  tll_ptr call_ret_t207;
  call_ret_t207 = and_thenULL_i58(env[2], env[1], env[0], f_v36670);
  return call_ret_t207;
}

tll_ptr lam_fun_t210(tll_ptr opt_v36668, tll_env env) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 3, opt_v36668, env[0], env[1]);
  return lam_clo_t209;
}

tll_ptr lam_fun_t212(tll_ptr B_v36665, tll_env env) {
  tll_ptr lam_clo_t211;
  instr_clo(&lam_clo_t211, &lam_fun_t210, 2, B_v36665, env[0]);
  return lam_clo_t211;
}

tll_ptr lam_fun_t214(tll_ptr A_v36661, tll_env env) {
  tll_ptr lam_clo_t213;
  instr_clo(&lam_clo_t213, &lam_fun_t212, 1, A_v36661);
  return lam_clo_t213;
}

tll_ptr and_thenLUL_i56(tll_ptr A_v36671, tll_ptr B_v36672, tll_ptr opt_v36673, tll_ptr f_v36674) {
  tll_ptr NoneUL_t217; tll_ptr app_ret_t218; tll_ptr switch_ret_t216;
  tll_ptr x_v36675;
  switch(((tll_node)opt_v36673)->tag) {
    case 11:
      instr_free_struct(opt_v36673);
      instr_struct(&NoneUL_t217, 15, 0);
      switch_ret_t216 = NoneUL_t217;
      break;
    case 12:
      x_v36675 = ((tll_node)opt_v36673)->data[0];
      instr_free_struct(opt_v36673);
      instr_app(&app_ret_t218, f_v36674, x_v36675);
      switch_ret_t216 = app_ret_t218;
      break;
  }
  return switch_ret_t216;
}

tll_ptr lam_fun_t220(tll_ptr f_v36685, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = and_thenLUL_i56(env[2], env[1], env[0], f_v36685);
  return call_ret_t219;
}

tll_ptr lam_fun_t222(tll_ptr opt_v36683, tll_env env) {
  tll_ptr lam_clo_t221;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 3, opt_v36683, env[0], env[1]);
  return lam_clo_t221;
}

tll_ptr lam_fun_t224(tll_ptr B_v36680, tll_env env) {
  tll_ptr lam_clo_t223;
  instr_clo(&lam_clo_t223, &lam_fun_t222, 2, B_v36680, env[0]);
  return lam_clo_t223;
}

tll_ptr lam_fun_t226(tll_ptr A_v36676, tll_env env) {
  tll_ptr lam_clo_t225;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 1, A_v36676);
  return lam_clo_t225;
}

tll_ptr and_thenLLL_i54(tll_ptr A_v36686, tll_ptr B_v36687, tll_ptr opt_v36688, tll_ptr f_v36689) {
  tll_ptr NoneLL_t229; tll_ptr app_ret_t230; tll_ptr switch_ret_t228;
  tll_ptr x_v36690;
  switch(((tll_node)opt_v36688)->tag) {
    case 11:
      instr_free_struct(opt_v36688);
      instr_struct(&NoneLL_t229, 11, 0);
      switch_ret_t228 = NoneLL_t229;
      break;
    case 12:
      x_v36690 = ((tll_node)opt_v36688)->data[0];
      instr_free_struct(opt_v36688);
      instr_app(&app_ret_t230, f_v36689, x_v36690);
      switch_ret_t228 = app_ret_t230;
      break;
  }
  return switch_ret_t228;
}

tll_ptr lam_fun_t232(tll_ptr f_v36700, tll_env env) {
  tll_ptr call_ret_t231;
  call_ret_t231 = and_thenLLL_i54(env[2], env[1], env[0], f_v36700);
  return call_ret_t231;
}

tll_ptr lam_fun_t234(tll_ptr opt_v36698, tll_env env) {
  tll_ptr lam_clo_t233;
  instr_clo(&lam_clo_t233, &lam_fun_t232, 3, opt_v36698, env[0], env[1]);
  return lam_clo_t233;
}

tll_ptr lam_fun_t236(tll_ptr B_v36695, tll_env env) {
  tll_ptr lam_clo_t235;
  instr_clo(&lam_clo_t235, &lam_fun_t234, 2, B_v36695, env[0]);
  return lam_clo_t235;
}

tll_ptr lam_fun_t238(tll_ptr A_v36691, tll_env env) {
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, A_v36691);
  return lam_clo_t237;
}

tll_ptr lenUU_i65(tll_ptr A_v36701, tll_ptr xs_v36702) {
  tll_ptr add_ret_t245; tll_ptr call_ret_t243; tll_ptr consUU_t246;
  tll_ptr n_v36705; tll_ptr nilUU_t241; tll_ptr pair_struct_t242;
  tll_ptr pair_struct_t247; tll_ptr switch_ret_t240; tll_ptr switch_ret_t244;
  tll_ptr x_v36703; tll_ptr xs_v36704; tll_ptr xs_v36706;
  switch(((tll_node)xs_v36702)->tag) {
    case 25:
      instr_struct(&nilUU_t241, 25, 0);
      instr_struct(&pair_struct_t242, 0, 2, (tll_ptr)0, nilUU_t241);
      switch_ret_t240 = pair_struct_t242;
      break;
    case 26:
      x_v36703 = ((tll_node)xs_v36702)->data[0];
      xs_v36704 = ((tll_node)xs_v36702)->data[1];
      call_ret_t243 = lenUU_i65(0, xs_v36704);
      switch(((tll_node)call_ret_t243)->tag) {
        case 0:
          n_v36705 = ((tll_node)call_ret_t243)->data[0];
          xs_v36706 = ((tll_node)call_ret_t243)->data[1];
          instr_free_struct(call_ret_t243);
          add_ret_t245 = n_v36705 + 1;
          instr_struct(&consUU_t246, 26, 2, x_v36703, xs_v36706);
          instr_struct(&pair_struct_t247, 0, 2, add_ret_t245, consUU_t246);
          switch_ret_t244 = pair_struct_t247;
          break;
      }
      switch_ret_t240 = switch_ret_t244;
      break;
  }
  return switch_ret_t240;
}

tll_ptr lam_fun_t249(tll_ptr xs_v36709, tll_env env) {
  tll_ptr call_ret_t248;
  call_ret_t248 = lenUU_i65(env[0], xs_v36709);
  return call_ret_t248;
}

tll_ptr lam_fun_t251(tll_ptr A_v36707, tll_env env) {
  tll_ptr lam_clo_t250;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 1, A_v36707);
  return lam_clo_t250;
}

tll_ptr lenUL_i64(tll_ptr A_v36710, tll_ptr xs_v36711) {
  tll_ptr add_ret_t258; tll_ptr call_ret_t256; tll_ptr consUL_t259;
  tll_ptr n_v36714; tll_ptr nilUL_t254; tll_ptr pair_struct_t255;
  tll_ptr pair_struct_t260; tll_ptr switch_ret_t253; tll_ptr switch_ret_t257;
  tll_ptr x_v36712; tll_ptr xs_v36713; tll_ptr xs_v36715;
  switch(((tll_node)xs_v36711)->tag) {
    case 23:
      instr_free_struct(xs_v36711);
      instr_struct(&nilUL_t254, 23, 0);
      instr_struct(&pair_struct_t255, 0, 2, (tll_ptr)0, nilUL_t254);
      switch_ret_t253 = pair_struct_t255;
      break;
    case 24:
      x_v36712 = ((tll_node)xs_v36711)->data[0];
      xs_v36713 = ((tll_node)xs_v36711)->data[1];
      instr_free_struct(xs_v36711);
      call_ret_t256 = lenUL_i64(0, xs_v36713);
      switch(((tll_node)call_ret_t256)->tag) {
        case 0:
          n_v36714 = ((tll_node)call_ret_t256)->data[0];
          xs_v36715 = ((tll_node)call_ret_t256)->data[1];
          instr_free_struct(call_ret_t256);
          add_ret_t258 = n_v36714 + 1;
          instr_struct(&consUL_t259, 24, 2, x_v36712, xs_v36715);
          instr_struct(&pair_struct_t260, 0, 2, add_ret_t258, consUL_t259);
          switch_ret_t257 = pair_struct_t260;
          break;
      }
      switch_ret_t253 = switch_ret_t257;
      break;
  }
  return switch_ret_t253;
}

tll_ptr lam_fun_t262(tll_ptr xs_v36718, tll_env env) {
  tll_ptr call_ret_t261;
  call_ret_t261 = lenUL_i64(env[0], xs_v36718);
  return call_ret_t261;
}

tll_ptr lam_fun_t264(tll_ptr A_v36716, tll_env env) {
  tll_ptr lam_clo_t263;
  instr_clo(&lam_clo_t263, &lam_fun_t262, 1, A_v36716);
  return lam_clo_t263;
}

tll_ptr lenLL_i62(tll_ptr A_v36719, tll_ptr xs_v36720) {
  tll_ptr add_ret_t271; tll_ptr call_ret_t269; tll_ptr consLL_t272;
  tll_ptr n_v36723; tll_ptr nilLL_t267; tll_ptr pair_struct_t268;
  tll_ptr pair_struct_t273; tll_ptr switch_ret_t266; tll_ptr switch_ret_t270;
  tll_ptr x_v36721; tll_ptr xs_v36722; tll_ptr xs_v36724;
  switch(((tll_node)xs_v36720)->tag) {
    case 19:
      instr_free_struct(xs_v36720);
      instr_struct(&nilLL_t267, 19, 0);
      instr_struct(&pair_struct_t268, 0, 2, (tll_ptr)0, nilLL_t267);
      switch_ret_t266 = pair_struct_t268;
      break;
    case 20:
      x_v36721 = ((tll_node)xs_v36720)->data[0];
      xs_v36722 = ((tll_node)xs_v36720)->data[1];
      instr_free_struct(xs_v36720);
      call_ret_t269 = lenLL_i62(0, xs_v36722);
      switch(((tll_node)call_ret_t269)->tag) {
        case 0:
          n_v36723 = ((tll_node)call_ret_t269)->data[0];
          xs_v36724 = ((tll_node)call_ret_t269)->data[1];
          instr_free_struct(call_ret_t269);
          add_ret_t271 = n_v36723 + 1;
          instr_struct(&consLL_t272, 20, 2, x_v36721, xs_v36724);
          instr_struct(&pair_struct_t273, 0, 2, add_ret_t271, consLL_t272);
          switch_ret_t270 = pair_struct_t273;
          break;
      }
      switch_ret_t266 = switch_ret_t270;
      break;
  }
  return switch_ret_t266;
}

tll_ptr lam_fun_t275(tll_ptr xs_v36727, tll_env env) {
  tll_ptr call_ret_t274;
  call_ret_t274 = lenLL_i62(env[0], xs_v36727);
  return call_ret_t274;
}

tll_ptr lam_fun_t277(tll_ptr A_v36725, tll_env env) {
  tll_ptr lam_clo_t276;
  instr_clo(&lam_clo_t276, &lam_fun_t275, 1, A_v36725);
  return lam_clo_t276;
}

tll_ptr appendUU_i69(tll_ptr A_v36728, tll_ptr xs_v36729, tll_ptr ys_v36730) {
  tll_ptr call_ret_t280; tll_ptr consUU_t281; tll_ptr switch_ret_t279;
  tll_ptr x_v36731; tll_ptr xs_v36732;
  switch(((tll_node)xs_v36729)->tag) {
    case 25:
      switch_ret_t279 = ys_v36730;
      break;
    case 26:
      x_v36731 = ((tll_node)xs_v36729)->data[0];
      xs_v36732 = ((tll_node)xs_v36729)->data[1];
      call_ret_t280 = appendUU_i69(0, xs_v36732, ys_v36730);
      instr_struct(&consUU_t281, 26, 2, x_v36731, call_ret_t280);
      switch_ret_t279 = consUU_t281;
      break;
  }
  return switch_ret_t279;
}

tll_ptr lam_fun_t283(tll_ptr ys_v36738, tll_env env) {
  tll_ptr call_ret_t282;
  call_ret_t282 = appendUU_i69(env[1], env[0], ys_v36738);
  return call_ret_t282;
}

tll_ptr lam_fun_t285(tll_ptr xs_v36736, tll_env env) {
  tll_ptr lam_clo_t284;
  instr_clo(&lam_clo_t284, &lam_fun_t283, 2, xs_v36736, env[0]);
  return lam_clo_t284;
}

tll_ptr lam_fun_t287(tll_ptr A_v36733, tll_env env) {
  tll_ptr lam_clo_t286;
  instr_clo(&lam_clo_t286, &lam_fun_t285, 1, A_v36733);
  return lam_clo_t286;
}

tll_ptr appendUL_i68(tll_ptr A_v36739, tll_ptr xs_v36740, tll_ptr ys_v36741) {
  tll_ptr call_ret_t290; tll_ptr consUL_t291; tll_ptr switch_ret_t289;
  tll_ptr x_v36742; tll_ptr xs_v36743;
  switch(((tll_node)xs_v36740)->tag) {
    case 23:
      instr_free_struct(xs_v36740);
      switch_ret_t289 = ys_v36741;
      break;
    case 24:
      x_v36742 = ((tll_node)xs_v36740)->data[0];
      xs_v36743 = ((tll_node)xs_v36740)->data[1];
      instr_free_struct(xs_v36740);
      call_ret_t290 = appendUL_i68(0, xs_v36743, ys_v36741);
      instr_struct(&consUL_t291, 24, 2, x_v36742, call_ret_t290);
      switch_ret_t289 = consUL_t291;
      break;
  }
  return switch_ret_t289;
}

tll_ptr lam_fun_t293(tll_ptr ys_v36749, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = appendUL_i68(env[1], env[0], ys_v36749);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v36747, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 2, xs_v36747, env[0]);
  return lam_clo_t294;
}

tll_ptr lam_fun_t297(tll_ptr A_v36744, tll_env env) {
  tll_ptr lam_clo_t296;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 1, A_v36744);
  return lam_clo_t296;
}

tll_ptr appendLL_i66(tll_ptr A_v36750, tll_ptr xs_v36751, tll_ptr ys_v36752) {
  tll_ptr call_ret_t300; tll_ptr consLL_t301; tll_ptr switch_ret_t299;
  tll_ptr x_v36753; tll_ptr xs_v36754;
  switch(((tll_node)xs_v36751)->tag) {
    case 19:
      instr_free_struct(xs_v36751);
      switch_ret_t299 = ys_v36752;
      break;
    case 20:
      x_v36753 = ((tll_node)xs_v36751)->data[0];
      xs_v36754 = ((tll_node)xs_v36751)->data[1];
      instr_free_struct(xs_v36751);
      call_ret_t300 = appendLL_i66(0, xs_v36754, ys_v36752);
      instr_struct(&consLL_t301, 20, 2, x_v36753, call_ret_t300);
      switch_ret_t299 = consLL_t301;
      break;
  }
  return switch_ret_t299;
}

tll_ptr lam_fun_t303(tll_ptr ys_v36760, tll_env env) {
  tll_ptr call_ret_t302;
  call_ret_t302 = appendLL_i66(env[1], env[0], ys_v36760);
  return call_ret_t302;
}

tll_ptr lam_fun_t305(tll_ptr xs_v36758, tll_env env) {
  tll_ptr lam_clo_t304;
  instr_clo(&lam_clo_t304, &lam_fun_t303, 2, xs_v36758, env[0]);
  return lam_clo_t304;
}

tll_ptr lam_fun_t307(tll_ptr A_v36755, tll_env env) {
  tll_ptr lam_clo_t306;
  instr_clo(&lam_clo_t306, &lam_fun_t305, 1, A_v36755);
  return lam_clo_t306;
}

tll_ptr lam_fun_t314(tll_ptr __v36762, tll_env env) {
  tll_ptr __v36771; tll_ptr ch_v36769; tll_ptr ch_v36770; tll_ptr ch_v36773;
  tll_ptr ch_v36774; tll_ptr prim_ch_t309; tll_ptr recv_msg_t311;
  tll_ptr s_v36772; tll_ptr send_ch_t310; tll_ptr send_ch_t313;
  tll_ptr switch_ret_t312;
  instr_open(&prim_ch_t309, &proc_stdin);
  ch_v36769 = prim_ch_t309;
  instr_send(&send_ch_t310, ch_v36769, (tll_ptr)1);
  ch_v36770 = send_ch_t310;
  instr_recv(&recv_msg_t311, ch_v36770);
  __v36771 = recv_msg_t311;
  switch(((tll_node)__v36771)->tag) {
    case 0:
      s_v36772 = ((tll_node)__v36771)->data[0];
      ch_v36773 = ((tll_node)__v36771)->data[1];
      instr_free_struct(__v36771);
      instr_send(&send_ch_t313, ch_v36773, (tll_ptr)0);
      ch_v36774 = send_ch_t313;
      switch_ret_t312 = s_v36772;
      break;
  }
  return switch_ret_t312;
}

tll_ptr readline_i32(tll_ptr __v36761) {
  tll_ptr lam_clo_t315;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 0);
  return lam_clo_t315;
}

tll_ptr lam_fun_t317(tll_ptr __v36775, tll_env env) {
  tll_ptr call_ret_t316;
  call_ret_t316 = readline_i32(__v36775);
  return call_ret_t316;
}

tll_ptr lam_fun_t323(tll_ptr __v36777, tll_env env) {
  tll_ptr ch_v36782; tll_ptr ch_v36783; tll_ptr ch_v36784; tll_ptr ch_v36785;
  tll_ptr prim_ch_t319; tll_ptr send_ch_t320; tll_ptr send_ch_t321;
  tll_ptr send_ch_t322;
  instr_open(&prim_ch_t319, &proc_stdout);
  ch_v36782 = prim_ch_t319;
  instr_send(&send_ch_t320, ch_v36782, (tll_ptr)1);
  ch_v36783 = send_ch_t320;
  instr_send(&send_ch_t321, ch_v36783, env[0]);
  ch_v36784 = send_ch_t321;
  instr_send(&send_ch_t322, ch_v36784, (tll_ptr)0);
  ch_v36785 = send_ch_t322;
  return 0;
}

tll_ptr print_i33(tll_ptr s_v36776) {
  tll_ptr lam_clo_t324;
  instr_clo(&lam_clo_t324, &lam_fun_t323, 1, s_v36776);
  return lam_clo_t324;
}

tll_ptr lam_fun_t326(tll_ptr s_v36786, tll_env env) {
  tll_ptr call_ret_t325;
  call_ret_t325 = print_i33(s_v36786);
  return call_ret_t325;
}

tll_ptr lam_fun_t332(tll_ptr __v36788, tll_env env) {
  tll_ptr ch_v36793; tll_ptr ch_v36794; tll_ptr ch_v36795; tll_ptr ch_v36796;
  tll_ptr prim_ch_t328; tll_ptr send_ch_t329; tll_ptr send_ch_t330;
  tll_ptr send_ch_t331;
  instr_open(&prim_ch_t328, &proc_stderr);
  ch_v36793 = prim_ch_t328;
  instr_send(&send_ch_t329, ch_v36793, (tll_ptr)1);
  ch_v36794 = send_ch_t329;
  instr_send(&send_ch_t330, ch_v36794, env[0]);
  ch_v36795 = send_ch_t330;
  instr_send(&send_ch_t331, ch_v36795, (tll_ptr)0);
  ch_v36796 = send_ch_t331;
  return 0;
}

tll_ptr prerr_i34(tll_ptr s_v36787) {
  tll_ptr lam_clo_t333;
  instr_clo(&lam_clo_t333, &lam_fun_t332, 1, s_v36787);
  return lam_clo_t333;
}

tll_ptr lam_fun_t335(tll_ptr s_v36797, tll_env env) {
  tll_ptr call_ret_t334;
  call_ret_t334 = prerr_i34(s_v36797);
  return call_ret_t334;
}

tll_ptr get_at_i36(tll_ptr A_v36798, tll_ptr n_v36799, tll_ptr xs_v36800, tll_ptr a_v36801) {
  tll_ptr __v36802; tll_ptr __v36805; tll_ptr add_ret_t380;
  tll_ptr call_ret_t379; tll_ptr ifte_ret_t382; tll_ptr switch_ret_t378;
  tll_ptr switch_ret_t381; tll_ptr x_v36804; tll_ptr xs_v36803;
  if (n_v36799) {
    switch(((tll_node)xs_v36800)->tag) {
      case 25:
        switch_ret_t378 = a_v36801;
        break;
      case 26:
        __v36802 = ((tll_node)xs_v36800)->data[0];
        xs_v36803 = ((tll_node)xs_v36800)->data[1];
        add_ret_t380 = n_v36799 - 1;
        call_ret_t379 = get_at_i36(0, add_ret_t380, xs_v36803, a_v36801);
        switch_ret_t378 = call_ret_t379;
        break;
    }
    ifte_ret_t382 = switch_ret_t378;
  }
  else {
    switch(((tll_node)xs_v36800)->tag) {
      case 25:
        switch_ret_t381 = a_v36801;
        break;
      case 26:
        x_v36804 = ((tll_node)xs_v36800)->data[0];
        __v36805 = ((tll_node)xs_v36800)->data[1];
        switch_ret_t381 = x_v36804;
        break;
    }
    ifte_ret_t382 = switch_ret_t381;
  }
  return ifte_ret_t382;
}

tll_ptr lam_fun_t384(tll_ptr a_v36815, tll_env env) {
  tll_ptr call_ret_t383;
  call_ret_t383 = get_at_i36(env[2], env[1], env[0], a_v36815);
  return call_ret_t383;
}

tll_ptr lam_fun_t386(tll_ptr xs_v36813, tll_env env) {
  tll_ptr lam_clo_t385;
  instr_clo(&lam_clo_t385, &lam_fun_t384, 3, xs_v36813, env[0], env[1]);
  return lam_clo_t385;
}

tll_ptr lam_fun_t388(tll_ptr n_v36810, tll_env env) {
  tll_ptr lam_clo_t387;
  instr_clo(&lam_clo_t387, &lam_fun_t386, 2, n_v36810, env[0]);
  return lam_clo_t387;
}

tll_ptr lam_fun_t390(tll_ptr A_v36806, tll_env env) {
  tll_ptr lam_clo_t389;
  instr_clo(&lam_clo_t389, &lam_fun_t388, 1, A_v36806);
  return lam_clo_t389;
}

tll_ptr string_of_digit_i37(tll_ptr n_v36816) {
  tll_ptr EmptyString_t393; tll_ptr call_ret_t392;
  instr_struct(&EmptyString_t393, 5, 0);
  call_ret_t392 = get_at_i36(0, n_v36816, digits_i35, EmptyString_t393);
  return call_ret_t392;
}

tll_ptr lam_fun_t395(tll_ptr n_v36817, tll_env env) {
  tll_ptr call_ret_t394;
  call_ret_t394 = string_of_digit_i37(n_v36817);
  return call_ret_t394;
}

tll_ptr string_of_nat_i38(tll_ptr n_v36818) {
  tll_ptr call_ret_t397; tll_ptr call_ret_t398; tll_ptr call_ret_t399;
  tll_ptr call_ret_t400; tll_ptr call_ret_t401; tll_ptr call_ret_t402;
  tll_ptr ifte_ret_t403; tll_ptr n_v36820; tll_ptr s_v36819;
  call_ret_t398 = modn_i16(n_v36818, (tll_ptr)10);
  call_ret_t397 = string_of_digit_i37(call_ret_t398);
  s_v36819 = call_ret_t397;
  call_ret_t399 = divn_i15(n_v36818, (tll_ptr)10);
  n_v36820 = call_ret_t399;
  call_ret_t400 = ltn_i7((tll_ptr)0, n_v36820);
  if (call_ret_t400) {
    call_ret_t402 = string_of_nat_i38(n_v36820);
    call_ret_t401 = cats_i19(call_ret_t402, s_v36819);
    ifte_ret_t403 = call_ret_t401;
  }
  else {
    ifte_ret_t403 = s_v36819;
  }
  return ifte_ret_t403;
}

tll_ptr lam_fun_t405(tll_ptr n_v36821, tll_env env) {
  tll_ptr call_ret_t404;
  call_ret_t404 = string_of_nat_i38(n_v36821);
  return call_ret_t404;
}

tll_ptr digit_of_char_i39(tll_ptr c_v36822) {
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
  instr_struct(&Char_t408, 4, 1, (tll_ptr)48);
  call_ret_t407 = eqc_i17(c_v36822, Char_t408);
  if (call_ret_t407) {
    instr_struct(&SomeUL_t409, 16, 1, (tll_ptr)0);
    ifte_ret_t447 = SomeUL_t409;
  }
  else {
    instr_struct(&Char_t411, 4, 1, (tll_ptr)49);
    call_ret_t410 = eqc_i17(c_v36822, Char_t411);
    if (call_ret_t410) {
      instr_struct(&SomeUL_t412, 16, 1, (tll_ptr)1);
      ifte_ret_t446 = SomeUL_t412;
    }
    else {
      instr_struct(&Char_t414, 4, 1, (tll_ptr)50);
      call_ret_t413 = eqc_i17(c_v36822, Char_t414);
      if (call_ret_t413) {
        instr_struct(&SomeUL_t415, 16, 1, (tll_ptr)2);
        ifte_ret_t445 = SomeUL_t415;
      }
      else {
        instr_struct(&Char_t417, 4, 1, (tll_ptr)51);
        call_ret_t416 = eqc_i17(c_v36822, Char_t417);
        if (call_ret_t416) {
          instr_struct(&SomeUL_t418, 16, 1, (tll_ptr)3);
          ifte_ret_t444 = SomeUL_t418;
        }
        else {
          instr_struct(&Char_t420, 4, 1, (tll_ptr)52);
          call_ret_t419 = eqc_i17(c_v36822, Char_t420);
          if (call_ret_t419) {
            instr_struct(&SomeUL_t421, 16, 1, (tll_ptr)4);
            ifte_ret_t443 = SomeUL_t421;
          }
          else {
            instr_struct(&Char_t423, 4, 1, (tll_ptr)53);
            call_ret_t422 = eqc_i17(c_v36822, Char_t423);
            if (call_ret_t422) {
              instr_struct(&SomeUL_t424, 16, 1, (tll_ptr)5);
              ifte_ret_t442 = SomeUL_t424;
            }
            else {
              instr_struct(&Char_t426, 4, 1, (tll_ptr)54);
              call_ret_t425 = eqc_i17(c_v36822, Char_t426);
              if (call_ret_t425) {
                instr_struct(&SomeUL_t427, 16, 1, (tll_ptr)6);
                ifte_ret_t441 = SomeUL_t427;
              }
              else {
                instr_struct(&Char_t429, 4, 1, (tll_ptr)55);
                call_ret_t428 = eqc_i17(c_v36822, Char_t429);
                if (call_ret_t428) {
                  instr_struct(&SomeUL_t430, 16, 1, (tll_ptr)7);
                  ifte_ret_t440 = SomeUL_t430;
                }
                else {
                  instr_struct(&Char_t432, 4, 1, (tll_ptr)56);
                  call_ret_t431 = eqc_i17(c_v36822, Char_t432);
                  if (call_ret_t431) {
                    instr_struct(&SomeUL_t433, 16, 1, (tll_ptr)8);
                    ifte_ret_t439 = SomeUL_t433;
                  }
                  else {
                    instr_struct(&Char_t435, 4, 1, (tll_ptr)57);
                    call_ret_t434 = eqc_i17(c_v36822, Char_t435);
                    if (call_ret_t434) {
                      instr_struct(&SomeUL_t436, 16, 1, (tll_ptr)9);
                      ifte_ret_t438 = SomeUL_t436;
                    }
                    else {
                      instr_struct(&NoneUL_t437, 15, 0);
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

tll_ptr lam_fun_t449(tll_ptr c_v36823, tll_env env) {
  tll_ptr call_ret_t448;
  call_ret_t448 = digit_of_char_i39(c_v36823);
  return call_ret_t448;
}

tll_ptr nat_of_string_loop_i40(tll_ptr s_v36824, tll_ptr acc_v36825) {
  tll_ptr NoneUL_t455; tll_ptr SomeUL_t452; tll_ptr c_v36826;
  tll_ptr call_ret_t453; tll_ptr call_ret_t456; tll_ptr call_ret_t457;
  tll_ptr call_ret_t458; tll_ptr n_v36828; tll_ptr s_v36827;
  tll_ptr switch_ret_t451; tll_ptr switch_ret_t454;
  switch(((tll_node)s_v36824)->tag) {
    case 5:
      instr_struct(&SomeUL_t452, 16, 1, acc_v36825);
      switch_ret_t451 = SomeUL_t452;
      break;
    case 6:
      c_v36826 = ((tll_node)s_v36824)->data[0];
      s_v36827 = ((tll_node)s_v36824)->data[1];
      call_ret_t453 = digit_of_char_i39(c_v36826);
      switch(((tll_node)call_ret_t453)->tag) {
        case 15:
          instr_free_struct(call_ret_t453);
          instr_struct(&NoneUL_t455, 15, 0);
          switch_ret_t454 = NoneUL_t455;
          break;
        case 16:
          n_v36828 = ((tll_node)call_ret_t453)->data[0];
          instr_free_struct(call_ret_t453);
          call_ret_t458 = muln_i14(acc_v36825, (tll_ptr)10);
          call_ret_t457 = addn_i12(call_ret_t458, n_v36828);
          call_ret_t456 = nat_of_string_loop_i40(s_v36827, call_ret_t457);
          switch_ret_t454 = call_ret_t456;
          break;
      }
      switch_ret_t451 = switch_ret_t454;
      break;
  }
  return switch_ret_t451;
}

tll_ptr lam_fun_t460(tll_ptr acc_v36831, tll_env env) {
  tll_ptr call_ret_t459;
  call_ret_t459 = nat_of_string_loop_i40(env[0], acc_v36831);
  return call_ret_t459;
}

tll_ptr lam_fun_t462(tll_ptr s_v36829, tll_env env) {
  tll_ptr lam_clo_t461;
  instr_clo(&lam_clo_t461, &lam_fun_t460, 1, s_v36829);
  return lam_clo_t461;
}

tll_ptr nat_of_string_i41(tll_ptr s_v36832) {
  tll_ptr call_ret_t464;
  call_ret_t464 = nat_of_string_loop_i40(s_v36832, (tll_ptr)0);
  return call_ret_t464;
}

tll_ptr lam_fun_t466(tll_ptr s_v36833, tll_env env) {
  tll_ptr call_ret_t465;
  call_ret_t465 = nat_of_string_i41(s_v36833);
  return call_ret_t465;
}

tll_ptr lam_fun_t537(tll_ptr __v36835, tll_env env) {
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
  tll_ptr __v36841; tll_ptr app_ret_t469; tll_ptr app_ret_t534;
  tll_ptr app_ret_t536; tll_ptr call_ret_t468; tll_ptr call_ret_t470;
  tll_ptr call_ret_t472; tll_ptr call_ret_t535; tll_ptr n_v36840;
  tll_ptr s_v36839; tll_ptr switch_ret_t471;
  call_ret_t468 = readline_i32(0);
  instr_app(&app_ret_t469, call_ret_t468, 0);
  instr_free_clo(call_ret_t468);
  s_v36839 = app_ret_t469;
  call_ret_t470 = nat_of_string_i41(s_v36839);
  switch(((tll_node)call_ret_t470)->tag) {
    case 16:
      n_v36840 = ((tll_node)call_ret_t470)->data[0];
      instr_free_struct(call_ret_t470);
      switch_ret_t471 = n_v36840;
      break;
    case 15:
      instr_free_struct(call_ret_t470);
      instr_struct(&Char_t473, 4, 1, (tll_ptr)112);
      instr_struct(&Char_t474, 4, 1, (tll_ptr)108);
      instr_struct(&Char_t475, 4, 1, (tll_ptr)101);
      instr_struct(&Char_t476, 4, 1, (tll_ptr)97);
      instr_struct(&Char_t477, 4, 1, (tll_ptr)115);
      instr_struct(&Char_t478, 4, 1, (tll_ptr)101);
      instr_struct(&Char_t479, 4, 1, (tll_ptr)32);
      instr_struct(&Char_t480, 4, 1, (tll_ptr)105);
      instr_struct(&Char_t481, 4, 1, (tll_ptr)110);
      instr_struct(&Char_t482, 4, 1, (tll_ptr)112);
      instr_struct(&Char_t483, 4, 1, (tll_ptr)117);
      instr_struct(&Char_t484, 4, 1, (tll_ptr)116);
      instr_struct(&Char_t485, 4, 1, (tll_ptr)32);
      instr_struct(&Char_t486, 4, 1, (tll_ptr)97);
      instr_struct(&Char_t487, 4, 1, (tll_ptr)32);
      instr_struct(&Char_t488, 4, 1, (tll_ptr)110);
      instr_struct(&Char_t489, 4, 1, (tll_ptr)97);
      instr_struct(&Char_t490, 4, 1, (tll_ptr)116);
      instr_struct(&Char_t491, 4, 1, (tll_ptr)117);
      instr_struct(&Char_t492, 4, 1, (tll_ptr)114);
      instr_struct(&Char_t493, 4, 1, (tll_ptr)97);
      instr_struct(&Char_t494, 4, 1, (tll_ptr)108);
      instr_struct(&Char_t495, 4, 1, (tll_ptr)32);
      instr_struct(&Char_t496, 4, 1, (tll_ptr)110);
      instr_struct(&Char_t497, 4, 1, (tll_ptr)117);
      instr_struct(&Char_t498, 4, 1, (tll_ptr)109);
      instr_struct(&Char_t499, 4, 1, (tll_ptr)98);
      instr_struct(&Char_t500, 4, 1, (tll_ptr)101);
      instr_struct(&Char_t501, 4, 1, (tll_ptr)114);
      instr_struct(&Char_t502, 4, 1, (tll_ptr)10);
      instr_struct(&EmptyString_t503, 5, 0);
      instr_struct(&String_t504, 6, 2, Char_t502, EmptyString_t503);
      instr_struct(&String_t505, 6, 2, Char_t501, String_t504);
      instr_struct(&String_t506, 6, 2, Char_t500, String_t505);
      instr_struct(&String_t507, 6, 2, Char_t499, String_t506);
      instr_struct(&String_t508, 6, 2, Char_t498, String_t507);
      instr_struct(&String_t509, 6, 2, Char_t497, String_t508);
      instr_struct(&String_t510, 6, 2, Char_t496, String_t509);
      instr_struct(&String_t511, 6, 2, Char_t495, String_t510);
      instr_struct(&String_t512, 6, 2, Char_t494, String_t511);
      instr_struct(&String_t513, 6, 2, Char_t493, String_t512);
      instr_struct(&String_t514, 6, 2, Char_t492, String_t513);
      instr_struct(&String_t515, 6, 2, Char_t491, String_t514);
      instr_struct(&String_t516, 6, 2, Char_t490, String_t515);
      instr_struct(&String_t517, 6, 2, Char_t489, String_t516);
      instr_struct(&String_t518, 6, 2, Char_t488, String_t517);
      instr_struct(&String_t519, 6, 2, Char_t487, String_t518);
      instr_struct(&String_t520, 6, 2, Char_t486, String_t519);
      instr_struct(&String_t521, 6, 2, Char_t485, String_t520);
      instr_struct(&String_t522, 6, 2, Char_t484, String_t521);
      instr_struct(&String_t523, 6, 2, Char_t483, String_t522);
      instr_struct(&String_t524, 6, 2, Char_t482, String_t523);
      instr_struct(&String_t525, 6, 2, Char_t481, String_t524);
      instr_struct(&String_t526, 6, 2, Char_t480, String_t525);
      instr_struct(&String_t527, 6, 2, Char_t479, String_t526);
      instr_struct(&String_t528, 6, 2, Char_t478, String_t527);
      instr_struct(&String_t529, 6, 2, Char_t477, String_t528);
      instr_struct(&String_t530, 6, 2, Char_t476, String_t529);
      instr_struct(&String_t531, 6, 2, Char_t475, String_t530);
      instr_struct(&String_t532, 6, 2, Char_t474, String_t531);
      instr_struct(&String_t533, 6, 2, Char_t473, String_t532);
      call_ret_t472 = print_i33(String_t533);
      instr_app(&app_ret_t534, call_ret_t472, 0);
      instr_free_clo(call_ret_t472);
      __v36841 = app_ret_t534;
      call_ret_t535 = read_nat_i48(0);
      instr_app(&app_ret_t536, call_ret_t535, 0);
      instr_free_clo(call_ret_t535);
      switch_ret_t471 = app_ret_t536;
      break;
  }
  return switch_ret_t471;
}

tll_ptr read_nat_i48(tll_ptr __v36834) {
  tll_ptr lam_clo_t538;
  instr_clo(&lam_clo_t538, &lam_fun_t537, 0);
  return lam_clo_t538;
}

tll_ptr lam_fun_t540(tll_ptr __v36842, tll_env env) {
  tll_ptr call_ret_t539;
  call_ret_t539 = read_nat_i48(__v36842);
  return call_ret_t539;
}

tll_ptr lam_fun_t772(tll_ptr __v36858, tll_env env) {
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
  tll_ptr String_t767; tll_ptr __v36871; tll_ptr __v36876; tll_ptr __v36877;
  tll_ptr __v36878; tll_ptr add_ret_t639; tll_ptr add_ret_t669;
  tll_ptr add_ret_t740; tll_ptr add_ret_t770; tll_ptr app_ret_t543;
  tll_ptr app_ret_t570; tll_ptr app_ret_t667; tll_ptr app_ret_t670;
  tll_ptr app_ret_t768; tll_ptr app_ret_t771; tll_ptr c_v36870;
  tll_ptr c_v36873; tll_ptr c_v36875; tll_ptr call_ret_t542;
  tll_ptr call_ret_t550; tll_ptr call_ret_t572; tll_ptr call_ret_t573;
  tll_ptr call_ret_t574; tll_ptr call_ret_t638; tll_ptr call_ret_t668;
  tll_ptr call_ret_t671; tll_ptr call_ret_t672; tll_ptr call_ret_t673;
  tll_ptr call_ret_t739; tll_ptr call_ret_t769; tll_ptr close_tmp_t571;
  tll_ptr guess_v36869; tll_ptr ord_v36872; tll_ptr pair_struct_t547;
  tll_ptr pf_v36874; tll_ptr recv_msg_t545; tll_ptr send_ch_t544;
  tll_ptr switch_ret_t546; tll_ptr switch_ret_t548; tll_ptr switch_ret_t549;
  call_ret_t542 = read_nat_i48(0);
  instr_app(&app_ret_t543, call_ret_t542, 0);
  instr_free_clo(call_ret_t542);
  guess_v36869 = app_ret_t543;
  instr_send(&send_ch_t544, env[0], guess_v36869);
  c_v36870 = send_ch_t544;
  instr_recv(&recv_msg_t545, c_v36870);
  __v36871 = recv_msg_t545;
  switch(((tll_node)__v36871)->tag) {
    case 0:
      ord_v36872 = ((tll_node)__v36871)->data[0];
      c_v36873 = ((tll_node)__v36871)->data[1];
      instr_free_struct(__v36871);
      instr_struct(&pair_struct_t547, 0, 2, 0, c_v36873);
      switch(((tll_node)pair_struct_t547)->tag) {
        case 0:
          pf_v36874 = ((tll_node)pair_struct_t547)->data[0];
          c_v36875 = ((tll_node)pair_struct_t547)->data[1];
          instr_free_struct(pair_struct_t547);
          switch(((tll_node)ord_v36872)->tag) {
            case 3:
              instr_struct(&Char_t551, 4, 1, (tll_ptr)89);
              instr_struct(&Char_t552, 4, 1, (tll_ptr)111);
              instr_struct(&Char_t553, 4, 1, (tll_ptr)117);
              instr_struct(&Char_t554, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t555, 4, 1, (tll_ptr)87);
              instr_struct(&Char_t556, 4, 1, (tll_ptr)105);
              instr_struct(&Char_t557, 4, 1, (tll_ptr)110);
              instr_struct(&Char_t558, 4, 1, (tll_ptr)33);
              instr_struct(&Char_t559, 4, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t560, 5, 0);
              instr_struct(&String_t561, 6, 2, Char_t559, EmptyString_t560);
              instr_struct(&String_t562, 6, 2, Char_t558, String_t561);
              instr_struct(&String_t563, 6, 2, Char_t557, String_t562);
              instr_struct(&String_t564, 6, 2, Char_t556, String_t563);
              instr_struct(&String_t565, 6, 2, Char_t555, String_t564);
              instr_struct(&String_t566, 6, 2, Char_t554, String_t565);
              instr_struct(&String_t567, 6, 2, Char_t553, String_t566);
              instr_struct(&String_t568, 6, 2, Char_t552, String_t567);
              instr_struct(&String_t569, 6, 2, Char_t551, String_t568);
              call_ret_t550 = print_i33(String_t569);
              instr_app(&app_ret_t570, call_ret_t550, 0);
              instr_free_clo(call_ret_t550);
              __v36876 = app_ret_t570;
              instr_close(&close_tmp_t571, c_v36875);
              switch_ret_t549 = close_tmp_t571;
              break;
            case 1:
              instr_struct(&Char_t575, 4, 1, (tll_ptr)84);
              instr_struct(&Char_t576, 4, 1, (tll_ptr)104);
              instr_struct(&Char_t577, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t578, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t579, 4, 1, (tll_ptr)97);
              instr_struct(&Char_t580, 4, 1, (tll_ptr)110);
              instr_struct(&Char_t581, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t582, 4, 1, (tll_ptr)119);
              instr_struct(&Char_t583, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t584, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t585, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t586, 4, 1, (tll_ptr)105);
              instr_struct(&Char_t587, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t588, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t589, 4, 1, (tll_ptr)108);
              instr_struct(&Char_t590, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t591, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t592, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t593, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t594, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t595, 4, 1, (tll_ptr)44);
              instr_struct(&Char_t596, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t597, 4, 1, (tll_ptr)121);
              instr_struct(&Char_t598, 4, 1, (tll_ptr)111);
              instr_struct(&Char_t599, 4, 1, (tll_ptr)117);
              instr_struct(&Char_t600, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t601, 4, 1, (tll_ptr)104);
              instr_struct(&Char_t602, 4, 1, (tll_ptr)97);
              instr_struct(&Char_t603, 4, 1, (tll_ptr)118);
              instr_struct(&Char_t604, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t605, 4, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t606, 5, 0);
              instr_struct(&String_t607, 6, 2, Char_t605, EmptyString_t606);
              instr_struct(&String_t608, 6, 2, Char_t604, String_t607);
              instr_struct(&String_t609, 6, 2, Char_t603, String_t608);
              instr_struct(&String_t610, 6, 2, Char_t602, String_t609);
              instr_struct(&String_t611, 6, 2, Char_t601, String_t610);
              instr_struct(&String_t612, 6, 2, Char_t600, String_t611);
              instr_struct(&String_t613, 6, 2, Char_t599, String_t612);
              instr_struct(&String_t614, 6, 2, Char_t598, String_t613);
              instr_struct(&String_t615, 6, 2, Char_t597, String_t614);
              instr_struct(&String_t616, 6, 2, Char_t596, String_t615);
              instr_struct(&String_t617, 6, 2, Char_t595, String_t616);
              instr_struct(&String_t618, 6, 2, Char_t594, String_t617);
              instr_struct(&String_t619, 6, 2, Char_t593, String_t618);
              instr_struct(&String_t620, 6, 2, Char_t592, String_t619);
              instr_struct(&String_t621, 6, 2, Char_t591, String_t620);
              instr_struct(&String_t622, 6, 2, Char_t590, String_t621);
              instr_struct(&String_t623, 6, 2, Char_t589, String_t622);
              instr_struct(&String_t624, 6, 2, Char_t588, String_t623);
              instr_struct(&String_t625, 6, 2, Char_t587, String_t624);
              instr_struct(&String_t626, 6, 2, Char_t586, String_t625);
              instr_struct(&String_t627, 6, 2, Char_t585, String_t626);
              instr_struct(&String_t628, 6, 2, Char_t584, String_t627);
              instr_struct(&String_t629, 6, 2, Char_t583, String_t628);
              instr_struct(&String_t630, 6, 2, Char_t582, String_t629);
              instr_struct(&String_t631, 6, 2, Char_t581, String_t630);
              instr_struct(&String_t632, 6, 2, Char_t580, String_t631);
              instr_struct(&String_t633, 6, 2, Char_t579, String_t632);
              instr_struct(&String_t634, 6, 2, Char_t578, String_t633);
              instr_struct(&String_t635, 6, 2, Char_t577, String_t634);
              instr_struct(&String_t636, 6, 2, Char_t576, String_t635);
              instr_struct(&String_t637, 6, 2, Char_t575, String_t636);
              add_ret_t639 = env[1] - 1;
              call_ret_t638 = string_of_nat_i38(add_ret_t639);
              call_ret_t574 = cats_i19(String_t637, call_ret_t638);
              instr_struct(&Char_t640, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t641, 4, 1, (tll_ptr)109);
              instr_struct(&Char_t642, 4, 1, (tll_ptr)111);
              instr_struct(&Char_t643, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t644, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t645, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t646, 4, 1, (tll_ptr)116);
              instr_struct(&Char_t647, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t648, 4, 1, (tll_ptr)105);
              instr_struct(&Char_t649, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t650, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t651, 4, 1, (tll_ptr)46);
              instr_struct(&Char_t652, 4, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t653, 5, 0);
              instr_struct(&String_t654, 6, 2, Char_t652, EmptyString_t653);
              instr_struct(&String_t655, 6, 2, Char_t651, String_t654);
              instr_struct(&String_t656, 6, 2, Char_t650, String_t655);
              instr_struct(&String_t657, 6, 2, Char_t649, String_t656);
              instr_struct(&String_t658, 6, 2, Char_t648, String_t657);
              instr_struct(&String_t659, 6, 2, Char_t647, String_t658);
              instr_struct(&String_t660, 6, 2, Char_t646, String_t659);
              instr_struct(&String_t661, 6, 2, Char_t645, String_t660);
              instr_struct(&String_t662, 6, 2, Char_t644, String_t661);
              instr_struct(&String_t663, 6, 2, Char_t643, String_t662);
              instr_struct(&String_t664, 6, 2, Char_t642, String_t663);
              instr_struct(&String_t665, 6, 2, Char_t641, String_t664);
              instr_struct(&String_t666, 6, 2, Char_t640, String_t665);
              call_ret_t573 = cats_i19(call_ret_t574, String_t666);
              call_ret_t572 = print_i33(call_ret_t573);
              instr_app(&app_ret_t667, call_ret_t572, 0);
              instr_free_clo(call_ret_t572);
              __v36877 = app_ret_t667;
              add_ret_t669 = env[1] - 1;
              call_ret_t668 = player_loop_i49(0, add_ret_t669, c_v36875);
              instr_app(&app_ret_t670, call_ret_t668, 0);
              instr_free_clo(call_ret_t668);
              switch_ret_t549 = app_ret_t670;
              break;
            case 2:
              instr_struct(&Char_t674, 4, 1, (tll_ptr)84);
              instr_struct(&Char_t675, 4, 1, (tll_ptr)104);
              instr_struct(&Char_t676, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t677, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t678, 4, 1, (tll_ptr)97);
              instr_struct(&Char_t679, 4, 1, (tll_ptr)110);
              instr_struct(&Char_t680, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t681, 4, 1, (tll_ptr)119);
              instr_struct(&Char_t682, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t683, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t684, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t685, 4, 1, (tll_ptr)105);
              instr_struct(&Char_t686, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t687, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t688, 4, 1, (tll_ptr)103);
              instr_struct(&Char_t689, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t690, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t691, 4, 1, (tll_ptr)97);
              instr_struct(&Char_t692, 4, 1, (tll_ptr)116);
              instr_struct(&Char_t693, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t694, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t695, 4, 1, (tll_ptr)44);
              instr_struct(&Char_t696, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t697, 4, 1, (tll_ptr)121);
              instr_struct(&Char_t698, 4, 1, (tll_ptr)111);
              instr_struct(&Char_t699, 4, 1, (tll_ptr)117);
              instr_struct(&Char_t700, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t701, 4, 1, (tll_ptr)104);
              instr_struct(&Char_t702, 4, 1, (tll_ptr)97);
              instr_struct(&Char_t703, 4, 1, (tll_ptr)118);
              instr_struct(&Char_t704, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t705, 4, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t706, 5, 0);
              instr_struct(&String_t707, 6, 2, Char_t705, EmptyString_t706);
              instr_struct(&String_t708, 6, 2, Char_t704, String_t707);
              instr_struct(&String_t709, 6, 2, Char_t703, String_t708);
              instr_struct(&String_t710, 6, 2, Char_t702, String_t709);
              instr_struct(&String_t711, 6, 2, Char_t701, String_t710);
              instr_struct(&String_t712, 6, 2, Char_t700, String_t711);
              instr_struct(&String_t713, 6, 2, Char_t699, String_t712);
              instr_struct(&String_t714, 6, 2, Char_t698, String_t713);
              instr_struct(&String_t715, 6, 2, Char_t697, String_t714);
              instr_struct(&String_t716, 6, 2, Char_t696, String_t715);
              instr_struct(&String_t717, 6, 2, Char_t695, String_t716);
              instr_struct(&String_t718, 6, 2, Char_t694, String_t717);
              instr_struct(&String_t719, 6, 2, Char_t693, String_t718);
              instr_struct(&String_t720, 6, 2, Char_t692, String_t719);
              instr_struct(&String_t721, 6, 2, Char_t691, String_t720);
              instr_struct(&String_t722, 6, 2, Char_t690, String_t721);
              instr_struct(&String_t723, 6, 2, Char_t689, String_t722);
              instr_struct(&String_t724, 6, 2, Char_t688, String_t723);
              instr_struct(&String_t725, 6, 2, Char_t687, String_t724);
              instr_struct(&String_t726, 6, 2, Char_t686, String_t725);
              instr_struct(&String_t727, 6, 2, Char_t685, String_t726);
              instr_struct(&String_t728, 6, 2, Char_t684, String_t727);
              instr_struct(&String_t729, 6, 2, Char_t683, String_t728);
              instr_struct(&String_t730, 6, 2, Char_t682, String_t729);
              instr_struct(&String_t731, 6, 2, Char_t681, String_t730);
              instr_struct(&String_t732, 6, 2, Char_t680, String_t731);
              instr_struct(&String_t733, 6, 2, Char_t679, String_t732);
              instr_struct(&String_t734, 6, 2, Char_t678, String_t733);
              instr_struct(&String_t735, 6, 2, Char_t677, String_t734);
              instr_struct(&String_t736, 6, 2, Char_t676, String_t735);
              instr_struct(&String_t737, 6, 2, Char_t675, String_t736);
              instr_struct(&String_t738, 6, 2, Char_t674, String_t737);
              add_ret_t740 = env[1] - 1;
              call_ret_t739 = string_of_nat_i38(add_ret_t740);
              call_ret_t673 = cats_i19(String_t738, call_ret_t739);
              instr_struct(&Char_t741, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t742, 4, 1, (tll_ptr)109);
              instr_struct(&Char_t743, 4, 1, (tll_ptr)111);
              instr_struct(&Char_t744, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t745, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t746, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t747, 4, 1, (tll_ptr)116);
              instr_struct(&Char_t748, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t749, 4, 1, (tll_ptr)105);
              instr_struct(&Char_t750, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t751, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t752, 4, 1, (tll_ptr)46);
              instr_struct(&Char_t753, 4, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t754, 5, 0);
              instr_struct(&String_t755, 6, 2, Char_t753, EmptyString_t754);
              instr_struct(&String_t756, 6, 2, Char_t752, String_t755);
              instr_struct(&String_t757, 6, 2, Char_t751, String_t756);
              instr_struct(&String_t758, 6, 2, Char_t750, String_t757);
              instr_struct(&String_t759, 6, 2, Char_t749, String_t758);
              instr_struct(&String_t760, 6, 2, Char_t748, String_t759);
              instr_struct(&String_t761, 6, 2, Char_t747, String_t760);
              instr_struct(&String_t762, 6, 2, Char_t746, String_t761);
              instr_struct(&String_t763, 6, 2, Char_t745, String_t762);
              instr_struct(&String_t764, 6, 2, Char_t744, String_t763);
              instr_struct(&String_t765, 6, 2, Char_t743, String_t764);
              instr_struct(&String_t766, 6, 2, Char_t742, String_t765);
              instr_struct(&String_t767, 6, 2, Char_t741, String_t766);
              call_ret_t672 = cats_i19(call_ret_t673, String_t767);
              call_ret_t671 = print_i33(call_ret_t672);
              instr_app(&app_ret_t768, call_ret_t671, 0);
              instr_free_clo(call_ret_t671);
              __v36878 = app_ret_t768;
              add_ret_t770 = env[1] - 1;
              call_ret_t769 = player_loop_i49(0, add_ret_t770, c_v36875);
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

tll_ptr lam_fun_t774(tll_ptr c_v36846, tll_env env) {
  tll_ptr lam_clo_t773;
  instr_clo(&lam_clo_t773, &lam_fun_t772, 2, c_v36846, env[0]);
  return lam_clo_t773;
}

tll_ptr lam_fun_t800(tll_ptr __v36882, tll_env env) {
  tll_ptr Char_t777; tll_ptr Char_t778; tll_ptr Char_t779; tll_ptr Char_t780;
  tll_ptr Char_t781; tll_ptr Char_t782; tll_ptr Char_t783; tll_ptr Char_t784;
  tll_ptr Char_t785; tll_ptr Char_t786; tll_ptr EmptyString_t787;
  tll_ptr String_t788; tll_ptr String_t789; tll_ptr String_t790;
  tll_ptr String_t791; tll_ptr String_t792; tll_ptr String_t793;
  tll_ptr String_t794; tll_ptr String_t795; tll_ptr String_t796;
  tll_ptr String_t797; tll_ptr __v36884; tll_ptr app_ret_t798;
  tll_ptr call_ret_t776; tll_ptr close_tmp_t799;
  instr_struct(&Char_t777, 4, 1, (tll_ptr)89);
  instr_struct(&Char_t778, 4, 1, (tll_ptr)111);
  instr_struct(&Char_t779, 4, 1, (tll_ptr)117);
  instr_struct(&Char_t780, 4, 1, (tll_ptr)32);
  instr_struct(&Char_t781, 4, 1, (tll_ptr)76);
  instr_struct(&Char_t782, 4, 1, (tll_ptr)111);
  instr_struct(&Char_t783, 4, 1, (tll_ptr)115);
  instr_struct(&Char_t784, 4, 1, (tll_ptr)101);
  instr_struct(&Char_t785, 4, 1, (tll_ptr)33);
  instr_struct(&Char_t786, 4, 1, (tll_ptr)10);
  instr_struct(&EmptyString_t787, 5, 0);
  instr_struct(&String_t788, 6, 2, Char_t786, EmptyString_t787);
  instr_struct(&String_t789, 6, 2, Char_t785, String_t788);
  instr_struct(&String_t790, 6, 2, Char_t784, String_t789);
  instr_struct(&String_t791, 6, 2, Char_t783, String_t790);
  instr_struct(&String_t792, 6, 2, Char_t782, String_t791);
  instr_struct(&String_t793, 6, 2, Char_t781, String_t792);
  instr_struct(&String_t794, 6, 2, Char_t780, String_t793);
  instr_struct(&String_t795, 6, 2, Char_t779, String_t794);
  instr_struct(&String_t796, 6, 2, Char_t778, String_t795);
  instr_struct(&String_t797, 6, 2, Char_t777, String_t796);
  call_ret_t776 = print_i33(String_t797);
  instr_app(&app_ret_t798, call_ret_t776, 0);
  instr_free_clo(call_ret_t776);
  __v36884 = app_ret_t798;
  instr_close(&close_tmp_t799, env[0]);
  return close_tmp_t799;
}

tll_ptr lam_fun_t802(tll_ptr c_v36879, tll_env env) {
  tll_ptr lam_clo_t801;
  instr_clo(&lam_clo_t801, &lam_fun_t800, 1, c_v36879);
  return lam_clo_t801;
}

tll_ptr player_loop_i49(tll_ptr ans_v36843, tll_ptr repeat_v36844, tll_ptr c_v36845) {
  tll_ptr app_ret_t805; tll_ptr ifte_ret_t804; tll_ptr lam_clo_t775;
  tll_ptr lam_clo_t803;
  if (repeat_v36844) {
    instr_clo(&lam_clo_t775, &lam_fun_t774, 1, repeat_v36844);
    ifte_ret_t804 = lam_clo_t775;
  }
  else {
    instr_clo(&lam_clo_t803, &lam_fun_t802, 0);
    ifte_ret_t804 = lam_clo_t803;
  }
  instr_app(&app_ret_t805, ifte_ret_t804, c_v36845);
  return app_ret_t805;
}

tll_ptr lam_fun_t807(tll_ptr c_v36890, tll_env env) {
  tll_ptr call_ret_t806;
  call_ret_t806 = player_loop_i49(env[1], env[0], c_v36890);
  return call_ret_t806;
}

tll_ptr lam_fun_t809(tll_ptr repeat_v36888, tll_env env) {
  tll_ptr lam_clo_t808;
  instr_clo(&lam_clo_t808, &lam_fun_t807, 2, repeat_v36888, env[0]);
  return lam_clo_t808;
}

tll_ptr lam_fun_t811(tll_ptr ans_v36885, tll_env env) {
  tll_ptr lam_clo_t810;
  instr_clo(&lam_clo_t810, &lam_fun_t809, 1, ans_v36885);
  return lam_clo_t810;
}

tll_ptr lam_fun_t949(tll_ptr __v36892, tll_env env) {
  tll_ptr Char_t830; tll_ptr Char_t831; tll_ptr Char_t832; tll_ptr Char_t833;
  tll_ptr Char_t834; tll_ptr Char_t835; tll_ptr Char_t836; tll_ptr Char_t837;
  tll_ptr Char_t838; tll_ptr Char_t839; tll_ptr Char_t840; tll_ptr Char_t841;
  tll_ptr Char_t842; tll_ptr Char_t843; tll_ptr Char_t844; tll_ptr Char_t845;
  tll_ptr Char_t846; tll_ptr Char_t847; tll_ptr Char_t848; tll_ptr Char_t849;
  tll_ptr Char_t850; tll_ptr Char_t851; tll_ptr Char_t852; tll_ptr Char_t853;
  tll_ptr Char_t854; tll_ptr Char_t855; tll_ptr Char_t856; tll_ptr Char_t857;
  tll_ptr Char_t888; tll_ptr Char_t889; tll_ptr Char_t890; tll_ptr Char_t891;
  tll_ptr Char_t892; tll_ptr Char_t900; tll_ptr Char_t901; tll_ptr Char_t909;
  tll_ptr Char_t910; tll_ptr Char_t911; tll_ptr Char_t912; tll_ptr Char_t913;
  tll_ptr Char_t914; tll_ptr Char_t915; tll_ptr Char_t916; tll_ptr Char_t917;
  tll_ptr Char_t929; tll_ptr Char_t930; tll_ptr Char_t931; tll_ptr Char_t932;
  tll_ptr Char_t933; tll_ptr Char_t934; tll_ptr Char_t935; tll_ptr Char_t936;
  tll_ptr EmptyString_t858; tll_ptr EmptyString_t893;
  tll_ptr EmptyString_t902; tll_ptr EmptyString_t918;
  tll_ptr EmptyString_t937; tll_ptr String_t859; tll_ptr String_t860;
  tll_ptr String_t861; tll_ptr String_t862; tll_ptr String_t863;
  tll_ptr String_t864; tll_ptr String_t865; tll_ptr String_t866;
  tll_ptr String_t867; tll_ptr String_t868; tll_ptr String_t869;
  tll_ptr String_t870; tll_ptr String_t871; tll_ptr String_t872;
  tll_ptr String_t873; tll_ptr String_t874; tll_ptr String_t875;
  tll_ptr String_t876; tll_ptr String_t877; tll_ptr String_t878;
  tll_ptr String_t879; tll_ptr String_t880; tll_ptr String_t881;
  tll_ptr String_t882; tll_ptr String_t883; tll_ptr String_t884;
  tll_ptr String_t885; tll_ptr String_t886; tll_ptr String_t894;
  tll_ptr String_t895; tll_ptr String_t896; tll_ptr String_t897;
  tll_ptr String_t898; tll_ptr String_t903; tll_ptr String_t904;
  tll_ptr String_t919; tll_ptr String_t920; tll_ptr String_t921;
  tll_ptr String_t922; tll_ptr String_t923; tll_ptr String_t924;
  tll_ptr String_t925; tll_ptr String_t926; tll_ptr String_t927;
  tll_ptr String_t938; tll_ptr String_t939; tll_ptr String_t940;
  tll_ptr String_t941; tll_ptr String_t942; tll_ptr String_t943;
  tll_ptr String_t944; tll_ptr String_t945; tll_ptr __v36910;
  tll_ptr __v36913; tll_ptr __v36922; tll_ptr __v36925; tll_ptr __v36926;
  tll_ptr ans_v36916; tll_ptr app_ret_t905; tll_ptr app_ret_t946;
  tll_ptr app_ret_t948; tll_ptr c_v36912; tll_ptr c_v36915; tll_ptr c_v36917;
  tll_ptr c_v36919; tll_ptr c_v36921; tll_ptr c_v36924;
  tll_ptr call_ret_t825; tll_ptr call_ret_t826; tll_ptr call_ret_t827;
  tll_ptr call_ret_t828; tll_ptr call_ret_t829; tll_ptr call_ret_t887;
  tll_ptr call_ret_t899; tll_ptr call_ret_t906; tll_ptr call_ret_t907;
  tll_ptr call_ret_t908; tll_ptr call_ret_t928; tll_ptr call_ret_t947;
  tll_ptr lower_v36911; tll_ptr pair_struct_t817; tll_ptr pair_struct_t819;
  tll_ptr pair_struct_t821; tll_ptr pf1_v36918; tll_ptr pf2_v36920;
  tll_ptr recv_msg_t813; tll_ptr recv_msg_t815; tll_ptr recv_msg_t823;
  tll_ptr repeat_v36923; tll_ptr switch_ret_t814; tll_ptr switch_ret_t816;
  tll_ptr switch_ret_t818; tll_ptr switch_ret_t820; tll_ptr switch_ret_t822;
  tll_ptr switch_ret_t824; tll_ptr upper_v36914;
  instr_recv(&recv_msg_t813, env[0]);
  __v36910 = recv_msg_t813;
  switch(((tll_node)__v36910)->tag) {
    case 0:
      lower_v36911 = ((tll_node)__v36910)->data[0];
      c_v36912 = ((tll_node)__v36910)->data[1];
      instr_free_struct(__v36910);
      instr_recv(&recv_msg_t815, c_v36912);
      __v36913 = recv_msg_t815;
      switch(((tll_node)__v36913)->tag) {
        case 0:
          upper_v36914 = ((tll_node)__v36913)->data[0];
          c_v36915 = ((tll_node)__v36913)->data[1];
          instr_free_struct(__v36913);
          instr_struct(&pair_struct_t817, 0, 2, 0, c_v36915);
          switch(((tll_node)pair_struct_t817)->tag) {
            case 0:
              ans_v36916 = ((tll_node)pair_struct_t817)->data[0];
              c_v36917 = ((tll_node)pair_struct_t817)->data[1];
              instr_free_struct(pair_struct_t817);
              instr_struct(&pair_struct_t819, 0, 2, 0, c_v36917);
              switch(((tll_node)pair_struct_t819)->tag) {
                case 0:
                  pf1_v36918 = ((tll_node)pair_struct_t819)->data[0];
                  c_v36919 = ((tll_node)pair_struct_t819)->data[1];
                  instr_free_struct(pair_struct_t819);
                  instr_struct(&pair_struct_t821, 0, 2, 0, c_v36919);
                  switch(((tll_node)pair_struct_t821)->tag) {
                    case 0:
                      pf2_v36920 = ((tll_node)pair_struct_t821)->data[0];
                      c_v36921 = ((tll_node)pair_struct_t821)->data[1];
                      instr_free_struct(pair_struct_t821);
                      instr_recv(&recv_msg_t823, c_v36921);
                      __v36922 = recv_msg_t823;
                      switch(((tll_node)__v36922)->tag) {
                        case 0:
                          repeat_v36923 = ((tll_node)__v36922)->data[0];
                          c_v36924 = ((tll_node)__v36922)->data[1];
                          instr_free_struct(__v36922);
                          instr_struct(&Char_t830, 4, 1, (tll_ptr)80);
                          instr_struct(&Char_t831, 4, 1, (tll_ptr)108);
                          instr_struct(&Char_t832, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t833, 4, 1, (tll_ptr)97);
                          instr_struct(&Char_t834, 4, 1, (tll_ptr)115);
                          instr_struct(&Char_t835, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t836, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t837, 4, 1, (tll_ptr)109);
                          instr_struct(&Char_t838, 4, 1, (tll_ptr)97);
                          instr_struct(&Char_t839, 4, 1, (tll_ptr)107);
                          instr_struct(&Char_t840, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t841, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t842, 4, 1, (tll_ptr)97);
                          instr_struct(&Char_t843, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t844, 4, 1, (tll_ptr)103);
                          instr_struct(&Char_t845, 4, 1, (tll_ptr)117);
                          instr_struct(&Char_t846, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t847, 4, 1, (tll_ptr)115);
                          instr_struct(&Char_t848, 4, 1, (tll_ptr)115);
                          instr_struct(&Char_t849, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t850, 4, 1, (tll_ptr)98);
                          instr_struct(&Char_t851, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t852, 4, 1, (tll_ptr)116);
                          instr_struct(&Char_t853, 4, 1, (tll_ptr)119);
                          instr_struct(&Char_t854, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t855, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t856, 4, 1, (tll_ptr)110);
                          instr_struct(&Char_t857, 4, 1, (tll_ptr)32);
                          instr_struct(&EmptyString_t858, 5, 0);
                          instr_struct(&String_t859, 6, 2,
                                       Char_t857, EmptyString_t858);
                          instr_struct(&String_t860, 6, 2,
                                       Char_t856, String_t859);
                          instr_struct(&String_t861, 6, 2,
                                       Char_t855, String_t860);
                          instr_struct(&String_t862, 6, 2,
                                       Char_t854, String_t861);
                          instr_struct(&String_t863, 6, 2,
                                       Char_t853, String_t862);
                          instr_struct(&String_t864, 6, 2,
                                       Char_t852, String_t863);
                          instr_struct(&String_t865, 6, 2,
                                       Char_t851, String_t864);
                          instr_struct(&String_t866, 6, 2,
                                       Char_t850, String_t865);
                          instr_struct(&String_t867, 6, 2,
                                       Char_t849, String_t866);
                          instr_struct(&String_t868, 6, 2,
                                       Char_t848, String_t867);
                          instr_struct(&String_t869, 6, 2,
                                       Char_t847, String_t868);
                          instr_struct(&String_t870, 6, 2,
                                       Char_t846, String_t869);
                          instr_struct(&String_t871, 6, 2,
                                       Char_t845, String_t870);
                          instr_struct(&String_t872, 6, 2,
                                       Char_t844, String_t871);
                          instr_struct(&String_t873, 6, 2,
                                       Char_t843, String_t872);
                          instr_struct(&String_t874, 6, 2,
                                       Char_t842, String_t873);
                          instr_struct(&String_t875, 6, 2,
                                       Char_t841, String_t874);
                          instr_struct(&String_t876, 6, 2,
                                       Char_t840, String_t875);
                          instr_struct(&String_t877, 6, 2,
                                       Char_t839, String_t876);
                          instr_struct(&String_t878, 6, 2,
                                       Char_t838, String_t877);
                          instr_struct(&String_t879, 6, 2,
                                       Char_t837, String_t878);
                          instr_struct(&String_t880, 6, 2,
                                       Char_t836, String_t879);
                          instr_struct(&String_t881, 6, 2,
                                       Char_t835, String_t880);
                          instr_struct(&String_t882, 6, 2,
                                       Char_t834, String_t881);
                          instr_struct(&String_t883, 6, 2,
                                       Char_t833, String_t882);
                          instr_struct(&String_t884, 6, 2,
                                       Char_t832, String_t883);
                          instr_struct(&String_t885, 6, 2,
                                       Char_t831, String_t884);
                          instr_struct(&String_t886, 6, 2,
                                       Char_t830, String_t885);
                          call_ret_t887 = string_of_nat_i38(lower_v36911);
                          call_ret_t829 = cats_i19(String_t886, call_ret_t887);
                          instr_struct(&Char_t888, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t889, 4, 1, (tll_ptr)97);
                          instr_struct(&Char_t890, 4, 1, (tll_ptr)110);
                          instr_struct(&Char_t891, 4, 1, (tll_ptr)100);
                          instr_struct(&Char_t892, 4, 1, (tll_ptr)32);
                          instr_struct(&EmptyString_t893, 5, 0);
                          instr_struct(&String_t894, 6, 2,
                                       Char_t892, EmptyString_t893);
                          instr_struct(&String_t895, 6, 2,
                                       Char_t891, String_t894);
                          instr_struct(&String_t896, 6, 2,
                                       Char_t890, String_t895);
                          instr_struct(&String_t897, 6, 2,
                                       Char_t889, String_t896);
                          instr_struct(&String_t898, 6, 2,
                                       Char_t888, String_t897);
                          call_ret_t828 = cats_i19(call_ret_t829, String_t898);
                          call_ret_t899 = string_of_nat_i38(upper_v36914);
                          call_ret_t827 = cats_i19(call_ret_t828,
                                                   call_ret_t899);
                          instr_struct(&Char_t900, 4, 1, (tll_ptr)46);
                          instr_struct(&Char_t901, 4, 1, (tll_ptr)10);
                          instr_struct(&EmptyString_t902, 5, 0);
                          instr_struct(&String_t903, 6, 2,
                                       Char_t901, EmptyString_t902);
                          instr_struct(&String_t904, 6, 2,
                                       Char_t900, String_t903);
                          call_ret_t826 = cats_i19(call_ret_t827, String_t904);
                          call_ret_t825 = print_i33(call_ret_t826);
                          instr_app(&app_ret_t905, call_ret_t825, 0);
                          instr_free_clo(call_ret_t825);
                          __v36925 = app_ret_t905;
                          instr_struct(&Char_t909, 4, 1, (tll_ptr)89);
                          instr_struct(&Char_t910, 4, 1, (tll_ptr)111);
                          instr_struct(&Char_t911, 4, 1, (tll_ptr)117);
                          instr_struct(&Char_t912, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t913, 4, 1, (tll_ptr)104);
                          instr_struct(&Char_t914, 4, 1, (tll_ptr)97);
                          instr_struct(&Char_t915, 4, 1, (tll_ptr)118);
                          instr_struct(&Char_t916, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t917, 4, 1, (tll_ptr)32);
                          instr_struct(&EmptyString_t918, 5, 0);
                          instr_struct(&String_t919, 6, 2,
                                       Char_t917, EmptyString_t918);
                          instr_struct(&String_t920, 6, 2,
                                       Char_t916, String_t919);
                          instr_struct(&String_t921, 6, 2,
                                       Char_t915, String_t920);
                          instr_struct(&String_t922, 6, 2,
                                       Char_t914, String_t921);
                          instr_struct(&String_t923, 6, 2,
                                       Char_t913, String_t922);
                          instr_struct(&String_t924, 6, 2,
                                       Char_t912, String_t923);
                          instr_struct(&String_t925, 6, 2,
                                       Char_t911, String_t924);
                          instr_struct(&String_t926, 6, 2,
                                       Char_t910, String_t925);
                          instr_struct(&String_t927, 6, 2,
                                       Char_t909, String_t926);
                          call_ret_t928 = string_of_nat_i38(repeat_v36923);
                          call_ret_t908 = cats_i19(String_t927, call_ret_t928);
                          instr_struct(&Char_t929, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t930, 4, 1, (tll_ptr)116);
                          instr_struct(&Char_t931, 4, 1, (tll_ptr)114);
                          instr_struct(&Char_t932, 4, 1, (tll_ptr)105);
                          instr_struct(&Char_t933, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t934, 4, 1, (tll_ptr)115);
                          instr_struct(&Char_t935, 4, 1, (tll_ptr)46);
                          instr_struct(&Char_t936, 4, 1, (tll_ptr)10);
                          instr_struct(&EmptyString_t937, 5, 0);
                          instr_struct(&String_t938, 6, 2,
                                       Char_t936, EmptyString_t937);
                          instr_struct(&String_t939, 6, 2,
                                       Char_t935, String_t938);
                          instr_struct(&String_t940, 6, 2,
                                       Char_t934, String_t939);
                          instr_struct(&String_t941, 6, 2,
                                       Char_t933, String_t940);
                          instr_struct(&String_t942, 6, 2,
                                       Char_t932, String_t941);
                          instr_struct(&String_t943, 6, 2,
                                       Char_t931, String_t942);
                          instr_struct(&String_t944, 6, 2,
                                       Char_t930, String_t943);
                          instr_struct(&String_t945, 6, 2,
                                       Char_t929, String_t944);
                          call_ret_t907 = cats_i19(call_ret_t908, String_t945);
                          call_ret_t906 = print_i33(call_ret_t907);
                          instr_app(&app_ret_t946, call_ret_t906, 0);
                          instr_free_clo(call_ret_t906);
                          __v36926 = app_ret_t946;
                          call_ret_t947 = player_loop_i49(0, repeat_v36923,
                                                          c_v36924);
                          instr_app(&app_ret_t948, call_ret_t947, 0);
                          instr_free_clo(call_ret_t947);
                          switch_ret_t824 = app_ret_t948;
                          break;
                      }
                      switch_ret_t822 = switch_ret_t824;
                      break;
                  }
                  switch_ret_t820 = switch_ret_t822;
                  break;
              }
              switch_ret_t818 = switch_ret_t820;
              break;
          }
          switch_ret_t816 = switch_ret_t818;
          break;
      }
      switch_ret_t814 = switch_ret_t816;
      break;
  }
  return switch_ret_t814;
}

tll_ptr player_i50(tll_ptr c_v36891) {
  tll_ptr lam_clo_t950;
  instr_clo(&lam_clo_t950, &lam_fun_t949, 1, c_v36891);
  return lam_clo_t950;
}

tll_ptr lam_fun_t952(tll_ptr c_v36927, tll_env env) {
  tll_ptr call_ret_t951;
  call_ret_t951 = player_i50(c_v36927);
  return call_ret_t951;
}

tll_ptr lam_fun_t965(tll_ptr __v36938, tll_env env) {
  tll_ptr __v36944; tll_ptr add_ret_t960; tll_ptr add_ret_t963;
  tll_ptr app_ret_t961; tll_ptr app_ret_t964; tll_ptr c_v36946;
  tll_ptr c_v36948; tll_ptr call_ret_t956; tll_ptr call_ret_t959;
  tll_ptr call_ret_t962; tll_ptr n_v36945; tll_ptr ord_v36947;
  tll_ptr recv_msg_t954; tll_ptr send_ch_t957; tll_ptr switch_ret_t955;
  tll_ptr switch_ret_t958;
  instr_recv(&recv_msg_t954, env[0]);
  __v36944 = recv_msg_t954;
  switch(((tll_node)__v36944)->tag) {
    case 0:
      n_v36945 = ((tll_node)__v36944)->data[0];
      c_v36946 = ((tll_node)__v36944)->data[1];
      instr_free_struct(__v36944);
      call_ret_t956 = comparen_i10(env[2], n_v36945);
      ord_v36947 = call_ret_t956;
      instr_send(&send_ch_t957, c_v36946, ord_v36947);
      c_v36948 = send_ch_t957;
      switch(((tll_node)ord_v36947)->tag) {
        case 3:
          switch_ret_t958 = 0;
          break;
        case 1:
          add_ret_t960 = env[1] - 1;
          call_ret_t959 = server_loop_i51(env[2], add_ret_t960, c_v36948);
          instr_app(&app_ret_t961, call_ret_t959, 0);
          switch_ret_t958 = app_ret_t961;
          break;
        case 2:
          add_ret_t963 = env[1] - 1;
          call_ret_t962 = server_loop_i51(env[2], add_ret_t963, c_v36948);
          instr_app(&app_ret_t964, call_ret_t962, 0);
          switch_ret_t958 = app_ret_t964;
          break;
      }
      switch_ret_t955 = switch_ret_t958;
      break;
  }
  return switch_ret_t955;
}

tll_ptr lam_fun_t967(tll_ptr c_v36931, tll_env env) {
  tll_ptr lam_clo_t966;
  instr_clo(&lam_clo_t966, &lam_fun_t965, 3, c_v36931, env[0], env[1]);
  return lam_clo_t966;
}

tll_ptr lam_fun_t969(tll_ptr __v36951, tll_env env) {
  
  
  return 0;
}

tll_ptr lam_fun_t971(tll_ptr c_v36949, tll_env env) {
  tll_ptr lam_clo_t970;
  instr_clo(&lam_clo_t970, &lam_fun_t969, 0);
  return lam_clo_t970;
}

tll_ptr server_loop_i51(tll_ptr ans_v36928, tll_ptr repeat_v36929, tll_ptr c_v36930) {
  tll_ptr app_ret_t974; tll_ptr ifte_ret_t973; tll_ptr lam_clo_t968;
  tll_ptr lam_clo_t972;
  if (repeat_v36929) {
    instr_clo(&lam_clo_t968, &lam_fun_t967, 2, repeat_v36929, ans_v36928);
    ifte_ret_t973 = lam_clo_t968;
  }
  else {
    instr_clo(&lam_clo_t972, &lam_fun_t971, 0);
    ifte_ret_t973 = lam_clo_t972;
  }
  instr_app(&app_ret_t974, ifte_ret_t973, c_v36930);
  return app_ret_t974;
}

tll_ptr lam_fun_t976(tll_ptr c_v36957, tll_env env) {
  tll_ptr call_ret_t975;
  call_ret_t975 = server_loop_i51(env[1], env[0], c_v36957);
  return call_ret_t975;
}

tll_ptr lam_fun_t978(tll_ptr repeat_v36955, tll_env env) {
  tll_ptr lam_clo_t977;
  instr_clo(&lam_clo_t977, &lam_fun_t976, 2, repeat_v36955, env[0]);
  return lam_clo_t977;
}

tll_ptr lam_fun_t980(tll_ptr ans_v36952, tll_env env) {
  tll_ptr lam_clo_t979;
  instr_clo(&lam_clo_t979, &lam_fun_t978, 1, ans_v36952);
  return lam_clo_t979;
}

tll_ptr lam_fun_t987(tll_ptr __v36959, tll_env env) {
  tll_ptr app_ret_t986; tll_ptr c_v36963; tll_ptr c_v36964; tll_ptr c_v36965;
  tll_ptr call_ret_t985; tll_ptr send_ch_t982; tll_ptr send_ch_t983;
  tll_ptr send_ch_t984;
  instr_send(&send_ch_t982, env[0], (tll_ptr)1);
  c_v36963 = send_ch_t982;
  instr_send(&send_ch_t983, c_v36963, (tll_ptr)128);
  c_v36964 = send_ch_t983;
  instr_send(&send_ch_t984, c_v36964, (tll_ptr)7);
  c_v36965 = send_ch_t984;
  call_ret_t985 = server_loop_i51((tll_ptr)71, (tll_ptr)7, c_v36965);
  instr_app(&app_ret_t986, call_ret_t985, 0);
  instr_free_clo(call_ret_t985);
  return app_ret_t986;
}

tll_ptr server_i52(tll_ptr c_v36958) {
  tll_ptr lam_clo_t988;
  instr_clo(&lam_clo_t988, &lam_fun_t987, 1, c_v36958);
  return lam_clo_t988;
}

tll_ptr lam_fun_t990(tll_ptr c_v36966, tll_env env) {
  tll_ptr call_ret_t989;
  call_ret_t989 = server_i52(c_v36966);
  return call_ret_t989;
}

tll_ptr fork_fun_t994(tll_env env) {
  tll_ptr app_ret_t993; tll_ptr call_ret_t992; tll_ptr fork_ret_t996;
  call_ret_t992 = server_i52(env[0]);
  instr_app(&app_ret_t993, call_ret_t992, 0);
  instr_free_clo(call_ret_t992);
  fork_ret_t996 = app_ret_t993;
  instr_free_thread(env);
  return fork_ret_t996;
}

tll_ptr fork_fun_t1002(tll_env env) {
  tll_ptr __v36976; tll_ptr __v36979; tll_ptr app_ret_t1000;
  tll_ptr c0_v36978; tll_ptr c0_v36980; tll_ptr c_v36977;
  tll_ptr call_ret_t999; tll_ptr fork_ret_t1004; tll_ptr recv_msg_t997;
  tll_ptr send_ch_t1001; tll_ptr switch_ret_t998;
  instr_recv(&recv_msg_t997, env[0]);
  __v36976 = recv_msg_t997;
  switch(((tll_node)__v36976)->tag) {
    case 0:
      c_v36977 = ((tll_node)__v36976)->data[0];
      c0_v36978 = ((tll_node)__v36976)->data[1];
      instr_free_struct(__v36976);
      call_ret_t999 = player_i50(c_v36977);
      instr_app(&app_ret_t1000, call_ret_t999, 0);
      instr_free_clo(call_ret_t999);
      __v36979 = app_ret_t1000;
      instr_send(&send_ch_t1001, c0_v36978, 0);
      c0_v36980 = send_ch_t1001;
      switch_ret_t998 = 0;
      break;
  }
  fork_ret_t1004 = switch_ret_t998;
  instr_free_thread(env);
  return fork_ret_t1004;
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
  tll_ptr String_t363; tll_ptr String_t366; tll_ptr __v36982;
  tll_ptr __v36983; tll_ptr c0_v36969; tll_ptr c0_v36981; tll_ptr c0_v36984;
  tll_ptr c_v36967; tll_ptr close_tmp_t1008; tll_ptr consUU_t368;
  tll_ptr consUU_t369; tll_ptr consUU_t370; tll_ptr consUU_t371;
  tll_ptr consUU_t372; tll_ptr consUU_t373; tll_ptr consUU_t374;
  tll_ptr consUU_t375; tll_ptr consUU_t376; tll_ptr consUU_t377;
  tll_ptr fork_ch_t1003; tll_ptr fork_ch_t995; tll_ptr lam_clo_t104;
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
  tll_ptr lam_clo_t467; tll_ptr lam_clo_t52; tll_ptr lam_clo_t541;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t6; tll_ptr lam_clo_t72;
  tll_ptr lam_clo_t77; tll_ptr lam_clo_t812; tll_ptr lam_clo_t83;
  tll_ptr lam_clo_t92; tll_ptr lam_clo_t953; tll_ptr lam_clo_t98;
  tll_ptr lam_clo_t981; tll_ptr lam_clo_t991; tll_ptr nilUU_t367;
  tll_ptr recv_msg_t1006; tll_ptr send_ch_t1005; tll_ptr switch_ret_t1007;
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
  instr_struct(&Char_t337, 4, 1, (tll_ptr)48);
  instr_struct(&EmptyString_t338, 5, 0);
  instr_struct(&String_t339, 6, 2, Char_t337, EmptyString_t338);
  instr_struct(&Char_t340, 4, 1, (tll_ptr)49);
  instr_struct(&EmptyString_t341, 5, 0);
  instr_struct(&String_t342, 6, 2, Char_t340, EmptyString_t341);
  instr_struct(&Char_t343, 4, 1, (tll_ptr)50);
  instr_struct(&EmptyString_t344, 5, 0);
  instr_struct(&String_t345, 6, 2, Char_t343, EmptyString_t344);
  instr_struct(&Char_t346, 4, 1, (tll_ptr)51);
  instr_struct(&EmptyString_t347, 5, 0);
  instr_struct(&String_t348, 6, 2, Char_t346, EmptyString_t347);
  instr_struct(&Char_t349, 4, 1, (tll_ptr)52);
  instr_struct(&EmptyString_t350, 5, 0);
  instr_struct(&String_t351, 6, 2, Char_t349, EmptyString_t350);
  instr_struct(&Char_t352, 4, 1, (tll_ptr)53);
  instr_struct(&EmptyString_t353, 5, 0);
  instr_struct(&String_t354, 6, 2, Char_t352, EmptyString_t353);
  instr_struct(&Char_t355, 4, 1, (tll_ptr)54);
  instr_struct(&EmptyString_t356, 5, 0);
  instr_struct(&String_t357, 6, 2, Char_t355, EmptyString_t356);
  instr_struct(&Char_t358, 4, 1, (tll_ptr)55);
  instr_struct(&EmptyString_t359, 5, 0);
  instr_struct(&String_t360, 6, 2, Char_t358, EmptyString_t359);
  instr_struct(&Char_t361, 4, 1, (tll_ptr)56);
  instr_struct(&EmptyString_t362, 5, 0);
  instr_struct(&String_t363, 6, 2, Char_t361, EmptyString_t362);
  instr_struct(&Char_t364, 4, 1, (tll_ptr)57);
  instr_struct(&EmptyString_t365, 5, 0);
  instr_struct(&String_t366, 6, 2, Char_t364, EmptyString_t365);
  instr_struct(&nilUU_t367, 25, 0);
  instr_struct(&consUU_t368, 26, 2, String_t366, nilUU_t367);
  instr_struct(&consUU_t369, 26, 2, String_t363, consUU_t368);
  instr_struct(&consUU_t370, 26, 2, String_t360, consUU_t369);
  instr_struct(&consUU_t371, 26, 2, String_t357, consUU_t370);
  instr_struct(&consUU_t372, 26, 2, String_t354, consUU_t371);
  instr_struct(&consUU_t373, 26, 2, String_t351, consUU_t372);
  instr_struct(&consUU_t374, 26, 2, String_t348, consUU_t373);
  instr_struct(&consUU_t375, 26, 2, String_t345, consUU_t374);
  instr_struct(&consUU_t376, 26, 2, String_t342, consUU_t375);
  instr_struct(&consUU_t377, 26, 2, String_t339, consUU_t376);
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
  instr_clo(&lam_clo_t812, &lam_fun_t811, 0);
  player_loopclo_i114 = lam_clo_t812;
  instr_clo(&lam_clo_t953, &lam_fun_t952, 0);
  playerclo_i115 = lam_clo_t953;
  instr_clo(&lam_clo_t981, &lam_fun_t980, 0);
  server_loopclo_i116 = lam_clo_t981;
  instr_clo(&lam_clo_t991, &lam_fun_t990, 0);
  serverclo_i117 = lam_clo_t991;
  instr_fork(&fork_ch_t995, &fork_fun_t994, 0);
  c_v36967 = fork_ch_t995;
  instr_fork(&fork_ch_t1003, &fork_fun_t1002, 0);
  c0_v36969 = fork_ch_t1003;
  instr_send(&send_ch_t1005, c0_v36969, c_v36967);
  c0_v36981 = send_ch_t1005;
  instr_recv(&recv_msg_t1006, c0_v36981);
  __v36982 = recv_msg_t1006;
  switch(((tll_node)__v36982)->tag) {
    case 0:
      __v36983 = ((tll_node)__v36982)->data[0];
      c0_v36984 = ((tll_node)__v36982)->data[1];
      instr_free_struct(__v36982);
      instr_close(&close_tmp_t1008, c0_v36984);
      switch_ret_t1007 = close_tmp_t1008;
      break;
  }
  return 0;
}

