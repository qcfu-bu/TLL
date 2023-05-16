#include"runtime.h"

tll_ptr andb_i2(tll_ptr b1_v141492, tll_ptr b2_v141493);
tll_ptr orb_i3(tll_ptr b1_v141497, tll_ptr b2_v141498);
tll_ptr notb_i4(tll_ptr b_v141502);
tll_ptr compareb_i5(tll_ptr b1_v141504, tll_ptr b2_v141505);
tll_ptr lten_i6(tll_ptr x_v141509, tll_ptr y_v141510);
tll_ptr gten_i7(tll_ptr x_v141514, tll_ptr y_v141515);
tll_ptr ltn_i8(tll_ptr x_v141519, tll_ptr y_v141520);
tll_ptr gtn_i9(tll_ptr x_v141524, tll_ptr y_v141525);
tll_ptr eqn_i10(tll_ptr x_v141529, tll_ptr y_v141530);
tll_ptr comparen_i11(tll_ptr n1_v141534, tll_ptr n2_v141535);
tll_ptr pred_i12(tll_ptr x_v141539);
tll_ptr addn_i13(tll_ptr x_v141541, tll_ptr y_v141542);
tll_ptr subn_i14(tll_ptr x_v141546, tll_ptr y_v141547);
tll_ptr muln_i15(tll_ptr x_v141551, tll_ptr y_v141552);
tll_ptr divn_i16(tll_ptr x_v141556, tll_ptr y_v141557);
tll_ptr modn_i17(tll_ptr x_v141561, tll_ptr y_v141562);
tll_ptr eqc_i18(tll_ptr c1_v141566, tll_ptr c2_v141567);
tll_ptr comparec_i19(tll_ptr c1_v141573, tll_ptr c2_v141574);
tll_ptr cats_i20(tll_ptr s1_v141580, tll_ptr s2_v141581);
tll_ptr strlen_i21(tll_ptr s_v141587);
tll_ptr eqs_i22(tll_ptr s1_v141591, tll_ptr s2_v141592);
tll_ptr compares_i23(tll_ptr s1_v141602, tll_ptr s2_v141603);
tll_ptr and_thenUUU_i74(tll_ptr A_v141613, tll_ptr B_v141614, tll_ptr opt_v141615, tll_ptr f_v141616);
tll_ptr and_thenUUL_i73(tll_ptr A_v141628, tll_ptr B_v141629, tll_ptr opt_v141630, tll_ptr f_v141631);
tll_ptr and_thenULU_i72(tll_ptr A_v141643, tll_ptr B_v141644, tll_ptr opt_v141645, tll_ptr f_v141646);
tll_ptr and_thenULL_i71(tll_ptr A_v141658, tll_ptr B_v141659, tll_ptr opt_v141660, tll_ptr f_v141661);
tll_ptr and_thenLUL_i69(tll_ptr A_v141673, tll_ptr B_v141674, tll_ptr opt_v141675, tll_ptr f_v141676);
tll_ptr and_thenLLL_i67(tll_ptr A_v141688, tll_ptr B_v141689, tll_ptr opt_v141690, tll_ptr f_v141691);
tll_ptr lenUU_i78(tll_ptr A_v141703, tll_ptr xs_v141704);
tll_ptr lenUL_i77(tll_ptr A_v141712, tll_ptr xs_v141713);
tll_ptr lenLL_i75(tll_ptr A_v141721, tll_ptr xs_v141722);
tll_ptr appendUU_i82(tll_ptr A_v141730, tll_ptr xs_v141731, tll_ptr ys_v141732);
tll_ptr appendUL_i81(tll_ptr A_v141741, tll_ptr xs_v141742, tll_ptr ys_v141743);
tll_ptr appendLL_i79(tll_ptr A_v141752, tll_ptr xs_v141753, tll_ptr ys_v141754);
tll_ptr readline_i33(tll_ptr __v141763);
tll_ptr print_i34(tll_ptr s_v141778);
tll_ptr prerr_i35(tll_ptr s_v141789);
tll_ptr get_at_i37(tll_ptr A_v141800, tll_ptr n_v141801, tll_ptr xs_v141802, tll_ptr a_v141803);
tll_ptr string_of_digit_i38(tll_ptr n_v141818);
tll_ptr string_of_nat_i39(tll_ptr n_v141820);
tll_ptr digit_of_char_i40(tll_ptr c_v141824);
tll_ptr nat_of_string_loop_i41(tll_ptr s_v141826, tll_ptr acc_v141827);
tll_ptr nat_of_string_i42(tll_ptr s_v141834);
tll_ptr string_diff_i49(tll_ptr s1_v141836, tll_ptr s2_v141837);
tll_ptr word_diff_i51(tll_ptr w1_v141845, tll_ptr w2_v141846);
tll_ptr eqw_i52(tll_ptr w1_v141854, tll_ptr w2_v141855);
tll_ptr read_word_i59(tll_ptr __v141863);
tll_ptr player_loop_i60(tll_ptr ans_v141882, tll_ptr repeat_v141883, tll_ptr c_v141884);
tll_ptr player_i61(tll_ptr c_v142001);
tll_ptr server_loop_i62(tll_ptr ans_v142020, tll_ptr repeat_v142021, tll_ptr c_v142022);
tll_ptr server_i63(tll_ptr c_v142077);

tll_ptr addnclo_i100;
tll_ptr and_thenLLLclo_i116;
tll_ptr and_thenLULclo_i115;
tll_ptr and_thenULLclo_i114;
tll_ptr and_thenULUclo_i113;
tll_ptr and_thenUULclo_i112;
tll_ptr and_thenUUUclo_i111;
tll_ptr andbclo_i89;
tll_ptr appendLLclo_i122;
tll_ptr appendULclo_i121;
tll_ptr appendUUclo_i120;
tll_ptr catsclo_i107;
tll_ptr comparebclo_i92;
tll_ptr comparecclo_i106;
tll_ptr comparenclo_i98;
tll_ptr comparesclo_i110;
tll_ptr digit_of_charclo_i129;
tll_ptr digits_i36;
tll_ptr divnclo_i103;
tll_ptr eqcclo_i105;
tll_ptr eqnclo_i97;
tll_ptr eqsclo_i109;
tll_ptr eqwclo_i134;
tll_ptr get_atclo_i126;
tll_ptr gtenclo_i94;
tll_ptr gtnclo_i96;
tll_ptr lenLLclo_i119;
tll_ptr lenULclo_i118;
tll_ptr lenUUclo_i117;
tll_ptr ltenclo_i93;
tll_ptr ltnclo_i95;
tll_ptr modnclo_i104;
tll_ptr mulnclo_i102;
tll_ptr nat_of_string_loopclo_i130;
tll_ptr nat_of_stringclo_i131;
tll_ptr notbclo_i91;
tll_ptr orbclo_i90;
tll_ptr player_loopclo_i136;
tll_ptr playerclo_i137;
tll_ptr predclo_i99;
tll_ptr prerrclo_i125;
tll_ptr printclo_i124;
tll_ptr read_wordclo_i135;
tll_ptr readlineclo_i123;
tll_ptr server_loopclo_i138;
tll_ptr serverclo_i139;
tll_ptr string_diffclo_i132;
tll_ptr string_of_digitclo_i127;
tll_ptr string_of_natclo_i128;
tll_ptr strlenclo_i108;
tll_ptr subnclo_i101;
tll_ptr word_diffclo_i133;

tll_ptr andb_i2(tll_ptr b1_v141492, tll_ptr b2_v141493) {
  tll_ptr ifte_ret_t1;
  if (b1_v141492) {
    ifte_ret_t1 = b2_v141493;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v141496, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i2(env[0], b2_v141496);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v141494, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v141494);
  return lam_clo_t4;
}

tll_ptr orb_i3(tll_ptr b1_v141497, tll_ptr b2_v141498) {
  tll_ptr ifte_ret_t7;
  if (b1_v141497) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v141498;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v141501, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i3(env[0], b2_v141501);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v141499, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v141499);
  return lam_clo_t10;
}

tll_ptr notb_i4(tll_ptr b_v141502) {
  tll_ptr ifte_ret_t13;
  if (b_v141502) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v141503, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i4(b_v141503);
  return call_ret_t14;
}

tll_ptr compareb_i5(tll_ptr b1_v141504, tll_ptr b2_v141505) {
  tll_ptr EQ_t17; tll_ptr EQ_t21; tll_ptr GT_t18; tll_ptr LT_t20;
  tll_ptr ifte_ret_t19; tll_ptr ifte_ret_t22; tll_ptr ifte_ret_t23;
  if (b1_v141504) {
    if (b2_v141505) {
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
    if (b2_v141505) {
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

tll_ptr lam_fun_t25(tll_ptr b2_v141508, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = compareb_i5(env[0], b2_v141508);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr b1_v141506, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, b1_v141506);
  return lam_clo_t26;
}

tll_ptr lten_i6(tll_ptr x_v141509, tll_ptr y_v141510) {
  tll_ptr lten_ret_t29;
  instr_lten(&lten_ret_t29, x_v141509, y_v141510);
  return lten_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v141513, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = lten_i6(env[0], y_v141513);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v141511, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v141511);
  return lam_clo_t32;
}

tll_ptr gten_i7(tll_ptr x_v141514, tll_ptr y_v141515) {
  tll_ptr gten_ret_t35;
  instr_gten(&gten_ret_t35, x_v141514, y_v141515);
  return gten_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v141518, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = gten_i7(env[0], y_v141518);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v141516, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v141516);
  return lam_clo_t38;
}

tll_ptr ltn_i8(tll_ptr x_v141519, tll_ptr y_v141520) {
  tll_ptr ltn_ret_t41;
  instr_ltn(&ltn_ret_t41, x_v141519, y_v141520);
  return ltn_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v141523, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = ltn_i8(env[0], y_v141523);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v141521, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v141521);
  return lam_clo_t44;
}

tll_ptr gtn_i9(tll_ptr x_v141524, tll_ptr y_v141525) {
  tll_ptr gtn_ret_t47;
  instr_gtn(&gtn_ret_t47, x_v141524, y_v141525);
  return gtn_ret_t47;
}

tll_ptr lam_fun_t49(tll_ptr y_v141528, tll_env env) {
  tll_ptr call_ret_t48;
  call_ret_t48 = gtn_i9(env[0], y_v141528);
  return call_ret_t48;
}

tll_ptr lam_fun_t51(tll_ptr x_v141526, tll_env env) {
  tll_ptr lam_clo_t50;
  instr_clo(&lam_clo_t50, &lam_fun_t49, 1, x_v141526);
  return lam_clo_t50;
}

tll_ptr eqn_i10(tll_ptr x_v141529, tll_ptr y_v141530) {
  tll_ptr eqn_ret_t53;
  instr_eqn(&eqn_ret_t53, x_v141529, y_v141530);
  return eqn_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v141533, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = eqn_i10(env[0], y_v141533);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v141531, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v141531);
  return lam_clo_t56;
}

tll_ptr comparen_i11(tll_ptr n1_v141534, tll_ptr n2_v141535) {
  tll_ptr EQ_t65; tll_ptr GT_t62; tll_ptr LT_t64; tll_ptr add_ret_t60;
  tll_ptr add_ret_t61; tll_ptr call_ret_t59; tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t66; tll_ptr ifte_ret_t67;
  if (n1_v141534) {
    if (n2_v141535) {
      add_ret_t60 = n1_v141534 - 1;
      add_ret_t61 = n2_v141535 - 1;
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
    if (n2_v141535) {
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

tll_ptr lam_fun_t69(tll_ptr n2_v141538, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = comparen_i11(env[0], n2_v141538);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr n1_v141536, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, n1_v141536);
  return lam_clo_t70;
}

tll_ptr pred_i12(tll_ptr x_v141539) {
  tll_ptr add_ret_t73; tll_ptr ifte_ret_t74;
  if (x_v141539) {
    add_ret_t73 = x_v141539 - 1;
    ifte_ret_t74 = add_ret_t73;
  }
  else {
    ifte_ret_t74 = (tll_ptr)0;
  }
  return ifte_ret_t74;
}

tll_ptr lam_fun_t76(tll_ptr x_v141540, tll_env env) {
  tll_ptr call_ret_t75;
  call_ret_t75 = pred_i12(x_v141540);
  return call_ret_t75;
}

tll_ptr addn_i13(tll_ptr x_v141541, tll_ptr y_v141542) {
  tll_ptr addn_ret_t78;
  instr_addn(&addn_ret_t78, x_v141541, y_v141542);
  return addn_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v141545, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i13(env[0], y_v141545);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v141543, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v141543);
  return lam_clo_t81;
}

tll_ptr subn_i14(tll_ptr x_v141546, tll_ptr y_v141547) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v141547) {
    call_ret_t85 = pred_i12(x_v141546);
    add_ret_t86 = y_v141547 - 1;
    call_ret_t84 = subn_i14(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v141546;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v141550, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i14(env[0], y_v141550);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v141548, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v141548);
  return lam_clo_t90;
}

tll_ptr muln_i15(tll_ptr x_v141551, tll_ptr y_v141552) {
  tll_ptr muln_ret_t93;
  instr_muln(&muln_ret_t93, x_v141551, y_v141552);
  return muln_ret_t93;
}

tll_ptr lam_fun_t95(tll_ptr y_v141555, tll_env env) {
  tll_ptr call_ret_t94;
  call_ret_t94 = muln_i15(env[0], y_v141555);
  return call_ret_t94;
}

tll_ptr lam_fun_t97(tll_ptr x_v141553, tll_env env) {
  tll_ptr lam_clo_t96;
  instr_clo(&lam_clo_t96, &lam_fun_t95, 1, x_v141553);
  return lam_clo_t96;
}

tll_ptr divn_i16(tll_ptr x_v141556, tll_ptr y_v141557) {
  tll_ptr divn_ret_t99;
  instr_divn(&divn_ret_t99, x_v141556, y_v141557);
  return divn_ret_t99;
}

tll_ptr lam_fun_t101(tll_ptr y_v141560, tll_env env) {
  tll_ptr call_ret_t100;
  call_ret_t100 = divn_i16(env[0], y_v141560);
  return call_ret_t100;
}

tll_ptr lam_fun_t103(tll_ptr x_v141558, tll_env env) {
  tll_ptr lam_clo_t102;
  instr_clo(&lam_clo_t102, &lam_fun_t101, 1, x_v141558);
  return lam_clo_t102;
}

tll_ptr modn_i17(tll_ptr x_v141561, tll_ptr y_v141562) {
  tll_ptr modn_ret_t105;
  instr_modn(&modn_ret_t105, x_v141561, y_v141562);
  return modn_ret_t105;
}

tll_ptr lam_fun_t107(tll_ptr y_v141565, tll_env env) {
  tll_ptr call_ret_t106;
  call_ret_t106 = modn_i17(env[0], y_v141565);
  return call_ret_t106;
}

tll_ptr lam_fun_t109(tll_ptr x_v141563, tll_env env) {
  tll_ptr lam_clo_t108;
  instr_clo(&lam_clo_t108, &lam_fun_t107, 1, x_v141563);
  return lam_clo_t108;
}

tll_ptr eqc_i18(tll_ptr c1_v141566, tll_ptr c2_v141567) {
  tll_ptr call_ret_t113; tll_ptr n1_v141568; tll_ptr n2_v141569;
  tll_ptr switch_ret_t111; tll_ptr switch_ret_t112;
  switch(((tll_node)c1_v141566)->tag) {
    case 5:
      n1_v141568 = ((tll_node)c1_v141566)->data[0];
      switch(((tll_node)c2_v141567)->tag) {
        case 5:
          n2_v141569 = ((tll_node)c2_v141567)->data[0];
          call_ret_t113 = eqn_i10(n1_v141568, n2_v141569);
          switch_ret_t112 = call_ret_t113;
          break;
      }
      switch_ret_t111 = switch_ret_t112;
      break;
  }
  return switch_ret_t111;
}

tll_ptr lam_fun_t115(tll_ptr c2_v141572, tll_env env) {
  tll_ptr call_ret_t114;
  call_ret_t114 = eqc_i18(env[0], c2_v141572);
  return call_ret_t114;
}

tll_ptr lam_fun_t117(tll_ptr c1_v141570, tll_env env) {
  tll_ptr lam_clo_t116;
  instr_clo(&lam_clo_t116, &lam_fun_t115, 1, c1_v141570);
  return lam_clo_t116;
}

tll_ptr comparec_i19(tll_ptr c1_v141573, tll_ptr c2_v141574) {
  tll_ptr call_ret_t121; tll_ptr n1_v141575; tll_ptr n2_v141576;
  tll_ptr switch_ret_t119; tll_ptr switch_ret_t120;
  switch(((tll_node)c1_v141573)->tag) {
    case 5:
      n1_v141575 = ((tll_node)c1_v141573)->data[0];
      switch(((tll_node)c2_v141574)->tag) {
        case 5:
          n2_v141576 = ((tll_node)c2_v141574)->data[0];
          call_ret_t121 = comparen_i11(n1_v141575, n2_v141576);
          switch_ret_t120 = call_ret_t121;
          break;
      }
      switch_ret_t119 = switch_ret_t120;
      break;
  }
  return switch_ret_t119;
}

tll_ptr lam_fun_t123(tll_ptr c2_v141579, tll_env env) {
  tll_ptr call_ret_t122;
  call_ret_t122 = comparec_i19(env[0], c2_v141579);
  return call_ret_t122;
}

tll_ptr lam_fun_t125(tll_ptr c1_v141577, tll_env env) {
  tll_ptr lam_clo_t124;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 1, c1_v141577);
  return lam_clo_t124;
}

tll_ptr cats_i20(tll_ptr s1_v141580, tll_ptr s2_v141581) {
  tll_ptr String_t129; tll_ptr c_v141582; tll_ptr call_ret_t128;
  tll_ptr s1_v141583; tll_ptr switch_ret_t127;
  switch(((tll_node)s1_v141580)->tag) {
    case 6:
      switch_ret_t127 = s2_v141581;
      break;
    case 7:
      c_v141582 = ((tll_node)s1_v141580)->data[0];
      s1_v141583 = ((tll_node)s1_v141580)->data[1];
      call_ret_t128 = cats_i20(s1_v141583, s2_v141581);
      instr_struct(&String_t129, 7, 2, c_v141582, call_ret_t128);
      switch_ret_t127 = String_t129;
      break;
  }
  return switch_ret_t127;
}

tll_ptr lam_fun_t131(tll_ptr s2_v141586, tll_env env) {
  tll_ptr call_ret_t130;
  call_ret_t130 = cats_i20(env[0], s2_v141586);
  return call_ret_t130;
}

tll_ptr lam_fun_t133(tll_ptr s1_v141584, tll_env env) {
  tll_ptr lam_clo_t132;
  instr_clo(&lam_clo_t132, &lam_fun_t131, 1, s1_v141584);
  return lam_clo_t132;
}

tll_ptr strlen_i21(tll_ptr s_v141587) {
  tll_ptr __v141588; tll_ptr add_ret_t137; tll_ptr call_ret_t136;
  tll_ptr s_v141589; tll_ptr switch_ret_t135;
  switch(((tll_node)s_v141587)->tag) {
    case 6:
      switch_ret_t135 = (tll_ptr)0;
      break;
    case 7:
      __v141588 = ((tll_node)s_v141587)->data[0];
      s_v141589 = ((tll_node)s_v141587)->data[1];
      call_ret_t136 = strlen_i21(s_v141589);
      add_ret_t137 = call_ret_t136 + 1;
      switch_ret_t135 = add_ret_t137;
      break;
  }
  return switch_ret_t135;
}

tll_ptr lam_fun_t139(tll_ptr s_v141590, tll_env env) {
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i21(s_v141590);
  return call_ret_t138;
}

tll_ptr eqs_i22(tll_ptr s1_v141591, tll_ptr s2_v141592) {
  tll_ptr __v141593; tll_ptr __v141594; tll_ptr c1_v141595;
  tll_ptr c2_v141597; tll_ptr call_ret_t144; tll_ptr call_ret_t145;
  tll_ptr call_ret_t146; tll_ptr s1_v141596; tll_ptr s2_v141598;
  tll_ptr switch_ret_t141; tll_ptr switch_ret_t142; tll_ptr switch_ret_t143;
  switch(((tll_node)s1_v141591)->tag) {
    case 6:
      switch(((tll_node)s2_v141592)->tag) {
        case 6:
          switch_ret_t142 = (tll_ptr)1;
          break;
        case 7:
          __v141593 = ((tll_node)s2_v141592)->data[0];
          __v141594 = ((tll_node)s2_v141592)->data[1];
          switch_ret_t142 = (tll_ptr)0;
          break;
      }
      switch_ret_t141 = switch_ret_t142;
      break;
    case 7:
      c1_v141595 = ((tll_node)s1_v141591)->data[0];
      s1_v141596 = ((tll_node)s1_v141591)->data[1];
      switch(((tll_node)s2_v141592)->tag) {
        case 6:
          switch_ret_t143 = (tll_ptr)0;
          break;
        case 7:
          c2_v141597 = ((tll_node)s2_v141592)->data[0];
          s2_v141598 = ((tll_node)s2_v141592)->data[1];
          call_ret_t145 = eqc_i18(c1_v141595, c2_v141597);
          call_ret_t146 = eqs_i22(s1_v141596, s2_v141598);
          call_ret_t144 = andb_i2(call_ret_t145, call_ret_t146);
          switch_ret_t143 = call_ret_t144;
          break;
      }
      switch_ret_t141 = switch_ret_t143;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t148(tll_ptr s2_v141601, tll_env env) {
  tll_ptr call_ret_t147;
  call_ret_t147 = eqs_i22(env[0], s2_v141601);
  return call_ret_t147;
}

tll_ptr lam_fun_t150(tll_ptr s1_v141599, tll_env env) {
  tll_ptr lam_clo_t149;
  instr_clo(&lam_clo_t149, &lam_fun_t148, 1, s1_v141599);
  return lam_clo_t149;
}

tll_ptr compares_i23(tll_ptr s1_v141602, tll_ptr s2_v141603) {
  tll_ptr EQ_t154; tll_ptr GT_t157; tll_ptr GT_t162; tll_ptr LT_t155;
  tll_ptr LT_t161; tll_ptr __v141604; tll_ptr __v141605; tll_ptr c1_v141606;
  tll_ptr c2_v141608; tll_ptr call_ret_t158; tll_ptr call_ret_t160;
  tll_ptr s1_v141607; tll_ptr s2_v141609; tll_ptr switch_ret_t152;
  tll_ptr switch_ret_t153; tll_ptr switch_ret_t156; tll_ptr switch_ret_t159;
  switch(((tll_node)s1_v141602)->tag) {
    case 6:
      switch(((tll_node)s2_v141603)->tag) {
        case 6:
          instr_struct(&EQ_t154, 3, 0);
          switch_ret_t153 = EQ_t154;
          break;
        case 7:
          __v141604 = ((tll_node)s2_v141603)->data[0];
          __v141605 = ((tll_node)s2_v141603)->data[1];
          instr_struct(&LT_t155, 1, 0);
          switch_ret_t153 = LT_t155;
          break;
      }
      switch_ret_t152 = switch_ret_t153;
      break;
    case 7:
      c1_v141606 = ((tll_node)s1_v141602)->data[0];
      s1_v141607 = ((tll_node)s1_v141602)->data[1];
      switch(((tll_node)s2_v141603)->tag) {
        case 6:
          instr_struct(&GT_t157, 2, 0);
          switch_ret_t156 = GT_t157;
          break;
        case 7:
          c2_v141608 = ((tll_node)s2_v141603)->data[0];
          s2_v141609 = ((tll_node)s2_v141603)->data[1];
          call_ret_t158 = comparec_i19(c1_v141606, c2_v141608);
          switch(((tll_node)call_ret_t158)->tag) {
            case 3:
              call_ret_t160 = compares_i23(s1_v141607, s2_v141609);
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

tll_ptr lam_fun_t164(tll_ptr s2_v141612, tll_env env) {
  tll_ptr call_ret_t163;
  call_ret_t163 = compares_i23(env[0], s2_v141612);
  return call_ret_t163;
}

tll_ptr lam_fun_t166(tll_ptr s1_v141610, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, s1_v141610);
  return lam_clo_t165;
}

tll_ptr and_thenUUU_i74(tll_ptr A_v141613, tll_ptr B_v141614, tll_ptr opt_v141615, tll_ptr f_v141616) {
  tll_ptr NoneUU_t169; tll_ptr app_ret_t170; tll_ptr switch_ret_t168;
  tll_ptr x_v141617;
  switch(((tll_node)opt_v141615)->tag) {
    case 19:
      instr_struct(&NoneUU_t169, 19, 0);
      switch_ret_t168 = NoneUU_t169;
      break;
    case 20:
      x_v141617 = ((tll_node)opt_v141615)->data[0];
      instr_app(&app_ret_t170, f_v141616, x_v141617);
      switch_ret_t168 = app_ret_t170;
      break;
  }
  return switch_ret_t168;
}

tll_ptr lam_fun_t172(tll_ptr f_v141627, tll_env env) {
  tll_ptr call_ret_t171;
  call_ret_t171 = and_thenUUU_i74(env[2], env[1], env[0], f_v141627);
  return call_ret_t171;
}

tll_ptr lam_fun_t174(tll_ptr opt_v141625, tll_env env) {
  tll_ptr lam_clo_t173;
  instr_clo(&lam_clo_t173, &lam_fun_t172, 3, opt_v141625, env[0], env[1]);
  return lam_clo_t173;
}

tll_ptr lam_fun_t176(tll_ptr B_v141622, tll_env env) {
  tll_ptr lam_clo_t175;
  instr_clo(&lam_clo_t175, &lam_fun_t174, 2, B_v141622, env[0]);
  return lam_clo_t175;
}

tll_ptr lam_fun_t178(tll_ptr A_v141618, tll_env env) {
  tll_ptr lam_clo_t177;
  instr_clo(&lam_clo_t177, &lam_fun_t176, 1, A_v141618);
  return lam_clo_t177;
}

tll_ptr and_thenUUL_i73(tll_ptr A_v141628, tll_ptr B_v141629, tll_ptr opt_v141630, tll_ptr f_v141631) {
  tll_ptr NoneUL_t181; tll_ptr app_ret_t182; tll_ptr switch_ret_t180;
  tll_ptr x_v141632;
  switch(((tll_node)opt_v141630)->tag) {
    case 17:
      instr_free_struct(opt_v141630);
      instr_struct(&NoneUL_t181, 17, 0);
      switch_ret_t180 = NoneUL_t181;
      break;
    case 18:
      x_v141632 = ((tll_node)opt_v141630)->data[0];
      instr_free_struct(opt_v141630);
      instr_app(&app_ret_t182, f_v141631, x_v141632);
      switch_ret_t180 = app_ret_t182;
      break;
  }
  return switch_ret_t180;
}

tll_ptr lam_fun_t184(tll_ptr f_v141642, tll_env env) {
  tll_ptr call_ret_t183;
  call_ret_t183 = and_thenUUL_i73(env[2], env[1], env[0], f_v141642);
  return call_ret_t183;
}

tll_ptr lam_fun_t186(tll_ptr opt_v141640, tll_env env) {
  tll_ptr lam_clo_t185;
  instr_clo(&lam_clo_t185, &lam_fun_t184, 3, opt_v141640, env[0], env[1]);
  return lam_clo_t185;
}

tll_ptr lam_fun_t188(tll_ptr B_v141637, tll_env env) {
  tll_ptr lam_clo_t187;
  instr_clo(&lam_clo_t187, &lam_fun_t186, 2, B_v141637, env[0]);
  return lam_clo_t187;
}

tll_ptr lam_fun_t190(tll_ptr A_v141633, tll_env env) {
  tll_ptr lam_clo_t189;
  instr_clo(&lam_clo_t189, &lam_fun_t188, 1, A_v141633);
  return lam_clo_t189;
}

tll_ptr and_thenULU_i72(tll_ptr A_v141643, tll_ptr B_v141644, tll_ptr opt_v141645, tll_ptr f_v141646) {
  tll_ptr NoneLU_t193; tll_ptr app_ret_t194; tll_ptr switch_ret_t192;
  tll_ptr x_v141647;
  switch(((tll_node)opt_v141645)->tag) {
    case 19:
      instr_struct(&NoneLU_t193, 15, 0);
      switch_ret_t192 = NoneLU_t193;
      break;
    case 20:
      x_v141647 = ((tll_node)opt_v141645)->data[0];
      instr_app(&app_ret_t194, f_v141646, x_v141647);
      switch_ret_t192 = app_ret_t194;
      break;
  }
  return switch_ret_t192;
}

tll_ptr lam_fun_t196(tll_ptr f_v141657, tll_env env) {
  tll_ptr call_ret_t195;
  call_ret_t195 = and_thenULU_i72(env[2], env[1], env[0], f_v141657);
  return call_ret_t195;
}

tll_ptr lam_fun_t198(tll_ptr opt_v141655, tll_env env) {
  tll_ptr lam_clo_t197;
  instr_clo(&lam_clo_t197, &lam_fun_t196, 3, opt_v141655, env[0], env[1]);
  return lam_clo_t197;
}

tll_ptr lam_fun_t200(tll_ptr B_v141652, tll_env env) {
  tll_ptr lam_clo_t199;
  instr_clo(&lam_clo_t199, &lam_fun_t198, 2, B_v141652, env[0]);
  return lam_clo_t199;
}

tll_ptr lam_fun_t202(tll_ptr A_v141648, tll_env env) {
  tll_ptr lam_clo_t201;
  instr_clo(&lam_clo_t201, &lam_fun_t200, 1, A_v141648);
  return lam_clo_t201;
}

tll_ptr and_thenULL_i71(tll_ptr A_v141658, tll_ptr B_v141659, tll_ptr opt_v141660, tll_ptr f_v141661) {
  tll_ptr NoneLL_t205; tll_ptr app_ret_t206; tll_ptr switch_ret_t204;
  tll_ptr x_v141662;
  switch(((tll_node)opt_v141660)->tag) {
    case 17:
      instr_free_struct(opt_v141660);
      instr_struct(&NoneLL_t205, 13, 0);
      switch_ret_t204 = NoneLL_t205;
      break;
    case 18:
      x_v141662 = ((tll_node)opt_v141660)->data[0];
      instr_free_struct(opt_v141660);
      instr_app(&app_ret_t206, f_v141661, x_v141662);
      switch_ret_t204 = app_ret_t206;
      break;
  }
  return switch_ret_t204;
}

tll_ptr lam_fun_t208(tll_ptr f_v141672, tll_env env) {
  tll_ptr call_ret_t207;
  call_ret_t207 = and_thenULL_i71(env[2], env[1], env[0], f_v141672);
  return call_ret_t207;
}

tll_ptr lam_fun_t210(tll_ptr opt_v141670, tll_env env) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 3, opt_v141670, env[0], env[1]);
  return lam_clo_t209;
}

tll_ptr lam_fun_t212(tll_ptr B_v141667, tll_env env) {
  tll_ptr lam_clo_t211;
  instr_clo(&lam_clo_t211, &lam_fun_t210, 2, B_v141667, env[0]);
  return lam_clo_t211;
}

tll_ptr lam_fun_t214(tll_ptr A_v141663, tll_env env) {
  tll_ptr lam_clo_t213;
  instr_clo(&lam_clo_t213, &lam_fun_t212, 1, A_v141663);
  return lam_clo_t213;
}

tll_ptr and_thenLUL_i69(tll_ptr A_v141673, tll_ptr B_v141674, tll_ptr opt_v141675, tll_ptr f_v141676) {
  tll_ptr NoneUL_t217; tll_ptr app_ret_t218; tll_ptr switch_ret_t216;
  tll_ptr x_v141677;
  switch(((tll_node)opt_v141675)->tag) {
    case 13:
      instr_free_struct(opt_v141675);
      instr_struct(&NoneUL_t217, 17, 0);
      switch_ret_t216 = NoneUL_t217;
      break;
    case 14:
      x_v141677 = ((tll_node)opt_v141675)->data[0];
      instr_free_struct(opt_v141675);
      instr_app(&app_ret_t218, f_v141676, x_v141677);
      switch_ret_t216 = app_ret_t218;
      break;
  }
  return switch_ret_t216;
}

tll_ptr lam_fun_t220(tll_ptr f_v141687, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = and_thenLUL_i69(env[2], env[1], env[0], f_v141687);
  return call_ret_t219;
}

tll_ptr lam_fun_t222(tll_ptr opt_v141685, tll_env env) {
  tll_ptr lam_clo_t221;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 3, opt_v141685, env[0], env[1]);
  return lam_clo_t221;
}

tll_ptr lam_fun_t224(tll_ptr B_v141682, tll_env env) {
  tll_ptr lam_clo_t223;
  instr_clo(&lam_clo_t223, &lam_fun_t222, 2, B_v141682, env[0]);
  return lam_clo_t223;
}

tll_ptr lam_fun_t226(tll_ptr A_v141678, tll_env env) {
  tll_ptr lam_clo_t225;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 1, A_v141678);
  return lam_clo_t225;
}

tll_ptr and_thenLLL_i67(tll_ptr A_v141688, tll_ptr B_v141689, tll_ptr opt_v141690, tll_ptr f_v141691) {
  tll_ptr NoneLL_t229; tll_ptr app_ret_t230; tll_ptr switch_ret_t228;
  tll_ptr x_v141692;
  switch(((tll_node)opt_v141690)->tag) {
    case 13:
      instr_free_struct(opt_v141690);
      instr_struct(&NoneLL_t229, 13, 0);
      switch_ret_t228 = NoneLL_t229;
      break;
    case 14:
      x_v141692 = ((tll_node)opt_v141690)->data[0];
      instr_free_struct(opt_v141690);
      instr_app(&app_ret_t230, f_v141691, x_v141692);
      switch_ret_t228 = app_ret_t230;
      break;
  }
  return switch_ret_t228;
}

tll_ptr lam_fun_t232(tll_ptr f_v141702, tll_env env) {
  tll_ptr call_ret_t231;
  call_ret_t231 = and_thenLLL_i67(env[2], env[1], env[0], f_v141702);
  return call_ret_t231;
}

tll_ptr lam_fun_t234(tll_ptr opt_v141700, tll_env env) {
  tll_ptr lam_clo_t233;
  instr_clo(&lam_clo_t233, &lam_fun_t232, 3, opt_v141700, env[0], env[1]);
  return lam_clo_t233;
}

tll_ptr lam_fun_t236(tll_ptr B_v141697, tll_env env) {
  tll_ptr lam_clo_t235;
  instr_clo(&lam_clo_t235, &lam_fun_t234, 2, B_v141697, env[0]);
  return lam_clo_t235;
}

tll_ptr lam_fun_t238(tll_ptr A_v141693, tll_env env) {
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, A_v141693);
  return lam_clo_t237;
}

tll_ptr lenUU_i78(tll_ptr A_v141703, tll_ptr xs_v141704) {
  tll_ptr add_ret_t245; tll_ptr call_ret_t243; tll_ptr consUU_t246;
  tll_ptr n_v141707; tll_ptr nilUU_t241; tll_ptr pair_struct_t242;
  tll_ptr pair_struct_t247; tll_ptr switch_ret_t240; tll_ptr switch_ret_t244;
  tll_ptr x_v141705; tll_ptr xs_v141706; tll_ptr xs_v141708;
  switch(((tll_node)xs_v141704)->tag) {
    case 27:
      instr_struct(&nilUU_t241, 27, 0);
      instr_struct(&pair_struct_t242, 0, 2, (tll_ptr)0, nilUU_t241);
      switch_ret_t240 = pair_struct_t242;
      break;
    case 28:
      x_v141705 = ((tll_node)xs_v141704)->data[0];
      xs_v141706 = ((tll_node)xs_v141704)->data[1];
      call_ret_t243 = lenUU_i78(0, xs_v141706);
      switch(((tll_node)call_ret_t243)->tag) {
        case 0:
          n_v141707 = ((tll_node)call_ret_t243)->data[0];
          xs_v141708 = ((tll_node)call_ret_t243)->data[1];
          instr_free_struct(call_ret_t243);
          add_ret_t245 = n_v141707 + 1;
          instr_struct(&consUU_t246, 28, 2, x_v141705, xs_v141708);
          instr_struct(&pair_struct_t247, 0, 2, add_ret_t245, consUU_t246);
          switch_ret_t244 = pair_struct_t247;
          break;
      }
      switch_ret_t240 = switch_ret_t244;
      break;
  }
  return switch_ret_t240;
}

tll_ptr lam_fun_t249(tll_ptr xs_v141711, tll_env env) {
  tll_ptr call_ret_t248;
  call_ret_t248 = lenUU_i78(env[0], xs_v141711);
  return call_ret_t248;
}

tll_ptr lam_fun_t251(tll_ptr A_v141709, tll_env env) {
  tll_ptr lam_clo_t250;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 1, A_v141709);
  return lam_clo_t250;
}

tll_ptr lenUL_i77(tll_ptr A_v141712, tll_ptr xs_v141713) {
  tll_ptr add_ret_t258; tll_ptr call_ret_t256; tll_ptr consUL_t259;
  tll_ptr n_v141716; tll_ptr nilUL_t254; tll_ptr pair_struct_t255;
  tll_ptr pair_struct_t260; tll_ptr switch_ret_t253; tll_ptr switch_ret_t257;
  tll_ptr x_v141714; tll_ptr xs_v141715; tll_ptr xs_v141717;
  switch(((tll_node)xs_v141713)->tag) {
    case 25:
      instr_free_struct(xs_v141713);
      instr_struct(&nilUL_t254, 25, 0);
      instr_struct(&pair_struct_t255, 0, 2, (tll_ptr)0, nilUL_t254);
      switch_ret_t253 = pair_struct_t255;
      break;
    case 26:
      x_v141714 = ((tll_node)xs_v141713)->data[0];
      xs_v141715 = ((tll_node)xs_v141713)->data[1];
      instr_free_struct(xs_v141713);
      call_ret_t256 = lenUL_i77(0, xs_v141715);
      switch(((tll_node)call_ret_t256)->tag) {
        case 0:
          n_v141716 = ((tll_node)call_ret_t256)->data[0];
          xs_v141717 = ((tll_node)call_ret_t256)->data[1];
          instr_free_struct(call_ret_t256);
          add_ret_t258 = n_v141716 + 1;
          instr_struct(&consUL_t259, 26, 2, x_v141714, xs_v141717);
          instr_struct(&pair_struct_t260, 0, 2, add_ret_t258, consUL_t259);
          switch_ret_t257 = pair_struct_t260;
          break;
      }
      switch_ret_t253 = switch_ret_t257;
      break;
  }
  return switch_ret_t253;
}

tll_ptr lam_fun_t262(tll_ptr xs_v141720, tll_env env) {
  tll_ptr call_ret_t261;
  call_ret_t261 = lenUL_i77(env[0], xs_v141720);
  return call_ret_t261;
}

tll_ptr lam_fun_t264(tll_ptr A_v141718, tll_env env) {
  tll_ptr lam_clo_t263;
  instr_clo(&lam_clo_t263, &lam_fun_t262, 1, A_v141718);
  return lam_clo_t263;
}

tll_ptr lenLL_i75(tll_ptr A_v141721, tll_ptr xs_v141722) {
  tll_ptr add_ret_t271; tll_ptr call_ret_t269; tll_ptr consLL_t272;
  tll_ptr n_v141725; tll_ptr nilLL_t267; tll_ptr pair_struct_t268;
  tll_ptr pair_struct_t273; tll_ptr switch_ret_t266; tll_ptr switch_ret_t270;
  tll_ptr x_v141723; tll_ptr xs_v141724; tll_ptr xs_v141726;
  switch(((tll_node)xs_v141722)->tag) {
    case 21:
      instr_free_struct(xs_v141722);
      instr_struct(&nilLL_t267, 21, 0);
      instr_struct(&pair_struct_t268, 0, 2, (tll_ptr)0, nilLL_t267);
      switch_ret_t266 = pair_struct_t268;
      break;
    case 22:
      x_v141723 = ((tll_node)xs_v141722)->data[0];
      xs_v141724 = ((tll_node)xs_v141722)->data[1];
      instr_free_struct(xs_v141722);
      call_ret_t269 = lenLL_i75(0, xs_v141724);
      switch(((tll_node)call_ret_t269)->tag) {
        case 0:
          n_v141725 = ((tll_node)call_ret_t269)->data[0];
          xs_v141726 = ((tll_node)call_ret_t269)->data[1];
          instr_free_struct(call_ret_t269);
          add_ret_t271 = n_v141725 + 1;
          instr_struct(&consLL_t272, 22, 2, x_v141723, xs_v141726);
          instr_struct(&pair_struct_t273, 0, 2, add_ret_t271, consLL_t272);
          switch_ret_t270 = pair_struct_t273;
          break;
      }
      switch_ret_t266 = switch_ret_t270;
      break;
  }
  return switch_ret_t266;
}

tll_ptr lam_fun_t275(tll_ptr xs_v141729, tll_env env) {
  tll_ptr call_ret_t274;
  call_ret_t274 = lenLL_i75(env[0], xs_v141729);
  return call_ret_t274;
}

tll_ptr lam_fun_t277(tll_ptr A_v141727, tll_env env) {
  tll_ptr lam_clo_t276;
  instr_clo(&lam_clo_t276, &lam_fun_t275, 1, A_v141727);
  return lam_clo_t276;
}

tll_ptr appendUU_i82(tll_ptr A_v141730, tll_ptr xs_v141731, tll_ptr ys_v141732) {
  tll_ptr call_ret_t280; tll_ptr consUU_t281; tll_ptr switch_ret_t279;
  tll_ptr x_v141733; tll_ptr xs_v141734;
  switch(((tll_node)xs_v141731)->tag) {
    case 27:
      switch_ret_t279 = ys_v141732;
      break;
    case 28:
      x_v141733 = ((tll_node)xs_v141731)->data[0];
      xs_v141734 = ((tll_node)xs_v141731)->data[1];
      call_ret_t280 = appendUU_i82(0, xs_v141734, ys_v141732);
      instr_struct(&consUU_t281, 28, 2, x_v141733, call_ret_t280);
      switch_ret_t279 = consUU_t281;
      break;
  }
  return switch_ret_t279;
}

tll_ptr lam_fun_t283(tll_ptr ys_v141740, tll_env env) {
  tll_ptr call_ret_t282;
  call_ret_t282 = appendUU_i82(env[1], env[0], ys_v141740);
  return call_ret_t282;
}

tll_ptr lam_fun_t285(tll_ptr xs_v141738, tll_env env) {
  tll_ptr lam_clo_t284;
  instr_clo(&lam_clo_t284, &lam_fun_t283, 2, xs_v141738, env[0]);
  return lam_clo_t284;
}

tll_ptr lam_fun_t287(tll_ptr A_v141735, tll_env env) {
  tll_ptr lam_clo_t286;
  instr_clo(&lam_clo_t286, &lam_fun_t285, 1, A_v141735);
  return lam_clo_t286;
}

tll_ptr appendUL_i81(tll_ptr A_v141741, tll_ptr xs_v141742, tll_ptr ys_v141743) {
  tll_ptr call_ret_t290; tll_ptr consUL_t291; tll_ptr switch_ret_t289;
  tll_ptr x_v141744; tll_ptr xs_v141745;
  switch(((tll_node)xs_v141742)->tag) {
    case 25:
      instr_free_struct(xs_v141742);
      switch_ret_t289 = ys_v141743;
      break;
    case 26:
      x_v141744 = ((tll_node)xs_v141742)->data[0];
      xs_v141745 = ((tll_node)xs_v141742)->data[1];
      instr_free_struct(xs_v141742);
      call_ret_t290 = appendUL_i81(0, xs_v141745, ys_v141743);
      instr_struct(&consUL_t291, 26, 2, x_v141744, call_ret_t290);
      switch_ret_t289 = consUL_t291;
      break;
  }
  return switch_ret_t289;
}

tll_ptr lam_fun_t293(tll_ptr ys_v141751, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = appendUL_i81(env[1], env[0], ys_v141751);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v141749, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 2, xs_v141749, env[0]);
  return lam_clo_t294;
}

tll_ptr lam_fun_t297(tll_ptr A_v141746, tll_env env) {
  tll_ptr lam_clo_t296;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 1, A_v141746);
  return lam_clo_t296;
}

tll_ptr appendLL_i79(tll_ptr A_v141752, tll_ptr xs_v141753, tll_ptr ys_v141754) {
  tll_ptr call_ret_t300; tll_ptr consLL_t301; tll_ptr switch_ret_t299;
  tll_ptr x_v141755; tll_ptr xs_v141756;
  switch(((tll_node)xs_v141753)->tag) {
    case 21:
      instr_free_struct(xs_v141753);
      switch_ret_t299 = ys_v141754;
      break;
    case 22:
      x_v141755 = ((tll_node)xs_v141753)->data[0];
      xs_v141756 = ((tll_node)xs_v141753)->data[1];
      instr_free_struct(xs_v141753);
      call_ret_t300 = appendLL_i79(0, xs_v141756, ys_v141754);
      instr_struct(&consLL_t301, 22, 2, x_v141755, call_ret_t300);
      switch_ret_t299 = consLL_t301;
      break;
  }
  return switch_ret_t299;
}

tll_ptr lam_fun_t303(tll_ptr ys_v141762, tll_env env) {
  tll_ptr call_ret_t302;
  call_ret_t302 = appendLL_i79(env[1], env[0], ys_v141762);
  return call_ret_t302;
}

tll_ptr lam_fun_t305(tll_ptr xs_v141760, tll_env env) {
  tll_ptr lam_clo_t304;
  instr_clo(&lam_clo_t304, &lam_fun_t303, 2, xs_v141760, env[0]);
  return lam_clo_t304;
}

tll_ptr lam_fun_t307(tll_ptr A_v141757, tll_env env) {
  tll_ptr lam_clo_t306;
  instr_clo(&lam_clo_t306, &lam_fun_t305, 1, A_v141757);
  return lam_clo_t306;
}

tll_ptr lam_fun_t314(tll_ptr __v141764, tll_env env) {
  tll_ptr __v141773; tll_ptr ch_v141771; tll_ptr ch_v141772;
  tll_ptr ch_v141775; tll_ptr ch_v141776; tll_ptr prim_ch_t309;
  tll_ptr recv_msg_t311; tll_ptr s_v141774; tll_ptr send_ch_t310;
  tll_ptr send_ch_t313; tll_ptr switch_ret_t312;
  instr_open(&prim_ch_t309, &proc_stdin);
  ch_v141771 = prim_ch_t309;
  instr_send(&send_ch_t310, ch_v141771, (tll_ptr)1);
  ch_v141772 = send_ch_t310;
  instr_recv(&recv_msg_t311, ch_v141772);
  __v141773 = recv_msg_t311;
  switch(((tll_node)__v141773)->tag) {
    case 0:
      s_v141774 = ((tll_node)__v141773)->data[0];
      ch_v141775 = ((tll_node)__v141773)->data[1];
      instr_free_struct(__v141773);
      instr_send(&send_ch_t313, ch_v141775, (tll_ptr)0);
      ch_v141776 = send_ch_t313;
      switch_ret_t312 = s_v141774;
      break;
  }
  return switch_ret_t312;
}

tll_ptr readline_i33(tll_ptr __v141763) {
  tll_ptr lam_clo_t315;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 0);
  return lam_clo_t315;
}

tll_ptr lam_fun_t317(tll_ptr __v141777, tll_env env) {
  tll_ptr call_ret_t316;
  call_ret_t316 = readline_i33(__v141777);
  return call_ret_t316;
}

tll_ptr lam_fun_t323(tll_ptr __v141779, tll_env env) {
  tll_ptr ch_v141784; tll_ptr ch_v141785; tll_ptr ch_v141786;
  tll_ptr ch_v141787; tll_ptr prim_ch_t319; tll_ptr send_ch_t320;
  tll_ptr send_ch_t321; tll_ptr send_ch_t322;
  instr_open(&prim_ch_t319, &proc_stdout);
  ch_v141784 = prim_ch_t319;
  instr_send(&send_ch_t320, ch_v141784, (tll_ptr)1);
  ch_v141785 = send_ch_t320;
  instr_send(&send_ch_t321, ch_v141785, env[0]);
  ch_v141786 = send_ch_t321;
  instr_send(&send_ch_t322, ch_v141786, (tll_ptr)0);
  ch_v141787 = send_ch_t322;
  return 0;
}

tll_ptr print_i34(tll_ptr s_v141778) {
  tll_ptr lam_clo_t324;
  instr_clo(&lam_clo_t324, &lam_fun_t323, 1, s_v141778);
  return lam_clo_t324;
}

tll_ptr lam_fun_t326(tll_ptr s_v141788, tll_env env) {
  tll_ptr call_ret_t325;
  call_ret_t325 = print_i34(s_v141788);
  return call_ret_t325;
}

tll_ptr lam_fun_t332(tll_ptr __v141790, tll_env env) {
  tll_ptr ch_v141795; tll_ptr ch_v141796; tll_ptr ch_v141797;
  tll_ptr ch_v141798; tll_ptr prim_ch_t328; tll_ptr send_ch_t329;
  tll_ptr send_ch_t330; tll_ptr send_ch_t331;
  instr_open(&prim_ch_t328, &proc_stderr);
  ch_v141795 = prim_ch_t328;
  instr_send(&send_ch_t329, ch_v141795, (tll_ptr)1);
  ch_v141796 = send_ch_t329;
  instr_send(&send_ch_t330, ch_v141796, env[0]);
  ch_v141797 = send_ch_t330;
  instr_send(&send_ch_t331, ch_v141797, (tll_ptr)0);
  ch_v141798 = send_ch_t331;
  return 0;
}

tll_ptr prerr_i35(tll_ptr s_v141789) {
  tll_ptr lam_clo_t333;
  instr_clo(&lam_clo_t333, &lam_fun_t332, 1, s_v141789);
  return lam_clo_t333;
}

tll_ptr lam_fun_t335(tll_ptr s_v141799, tll_env env) {
  tll_ptr call_ret_t334;
  call_ret_t334 = prerr_i35(s_v141799);
  return call_ret_t334;
}

tll_ptr get_at_i37(tll_ptr A_v141800, tll_ptr n_v141801, tll_ptr xs_v141802, tll_ptr a_v141803) {
  tll_ptr __v141804; tll_ptr __v141807; tll_ptr add_ret_t380;
  tll_ptr call_ret_t379; tll_ptr ifte_ret_t382; tll_ptr switch_ret_t378;
  tll_ptr switch_ret_t381; tll_ptr x_v141806; tll_ptr xs_v141805;
  if (n_v141801) {
    switch(((tll_node)xs_v141802)->tag) {
      case 27:
        switch_ret_t378 = a_v141803;
        break;
      case 28:
        __v141804 = ((tll_node)xs_v141802)->data[0];
        xs_v141805 = ((tll_node)xs_v141802)->data[1];
        add_ret_t380 = n_v141801 - 1;
        call_ret_t379 = get_at_i37(0, add_ret_t380, xs_v141805, a_v141803);
        switch_ret_t378 = call_ret_t379;
        break;
    }
    ifte_ret_t382 = switch_ret_t378;
  }
  else {
    switch(((tll_node)xs_v141802)->tag) {
      case 27:
        switch_ret_t381 = a_v141803;
        break;
      case 28:
        x_v141806 = ((tll_node)xs_v141802)->data[0];
        __v141807 = ((tll_node)xs_v141802)->data[1];
        switch_ret_t381 = x_v141806;
        break;
    }
    ifte_ret_t382 = switch_ret_t381;
  }
  return ifte_ret_t382;
}

tll_ptr lam_fun_t384(tll_ptr a_v141817, tll_env env) {
  tll_ptr call_ret_t383;
  call_ret_t383 = get_at_i37(env[2], env[1], env[0], a_v141817);
  return call_ret_t383;
}

tll_ptr lam_fun_t386(tll_ptr xs_v141815, tll_env env) {
  tll_ptr lam_clo_t385;
  instr_clo(&lam_clo_t385, &lam_fun_t384, 3, xs_v141815, env[0], env[1]);
  return lam_clo_t385;
}

tll_ptr lam_fun_t388(tll_ptr n_v141812, tll_env env) {
  tll_ptr lam_clo_t387;
  instr_clo(&lam_clo_t387, &lam_fun_t386, 2, n_v141812, env[0]);
  return lam_clo_t387;
}

tll_ptr lam_fun_t390(tll_ptr A_v141808, tll_env env) {
  tll_ptr lam_clo_t389;
  instr_clo(&lam_clo_t389, &lam_fun_t388, 1, A_v141808);
  return lam_clo_t389;
}

tll_ptr string_of_digit_i38(tll_ptr n_v141818) {
  tll_ptr EmptyString_t393; tll_ptr call_ret_t392;
  instr_struct(&EmptyString_t393, 6, 0);
  call_ret_t392 = get_at_i37(0, n_v141818, digits_i36, EmptyString_t393);
  return call_ret_t392;
}

tll_ptr lam_fun_t395(tll_ptr n_v141819, tll_env env) {
  tll_ptr call_ret_t394;
  call_ret_t394 = string_of_digit_i38(n_v141819);
  return call_ret_t394;
}

tll_ptr string_of_nat_i39(tll_ptr n_v141820) {
  tll_ptr call_ret_t397; tll_ptr call_ret_t398; tll_ptr call_ret_t399;
  tll_ptr call_ret_t400; tll_ptr call_ret_t401; tll_ptr call_ret_t402;
  tll_ptr ifte_ret_t403; tll_ptr n_v141822; tll_ptr s_v141821;
  call_ret_t398 = modn_i17(n_v141820, (tll_ptr)10);
  call_ret_t397 = string_of_digit_i38(call_ret_t398);
  s_v141821 = call_ret_t397;
  call_ret_t399 = divn_i16(n_v141820, (tll_ptr)10);
  n_v141822 = call_ret_t399;
  call_ret_t400 = ltn_i8((tll_ptr)0, n_v141822);
  if (call_ret_t400) {
    call_ret_t402 = string_of_nat_i39(n_v141822);
    call_ret_t401 = cats_i20(call_ret_t402, s_v141821);
    ifte_ret_t403 = call_ret_t401;
  }
  else {
    ifte_ret_t403 = s_v141821;
  }
  return ifte_ret_t403;
}

tll_ptr lam_fun_t405(tll_ptr n_v141823, tll_env env) {
  tll_ptr call_ret_t404;
  call_ret_t404 = string_of_nat_i39(n_v141823);
  return call_ret_t404;
}

tll_ptr digit_of_char_i40(tll_ptr c_v141824) {
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
  call_ret_t407 = eqc_i18(c_v141824, Char_t408);
  if (call_ret_t407) {
    instr_struct(&SomeUL_t409, 18, 1, (tll_ptr)0);
    ifte_ret_t447 = SomeUL_t409;
  }
  else {
    instr_struct(&Char_t411, 5, 1, (tll_ptr)49);
    call_ret_t410 = eqc_i18(c_v141824, Char_t411);
    if (call_ret_t410) {
      instr_struct(&SomeUL_t412, 18, 1, (tll_ptr)1);
      ifte_ret_t446 = SomeUL_t412;
    }
    else {
      instr_struct(&Char_t414, 5, 1, (tll_ptr)50);
      call_ret_t413 = eqc_i18(c_v141824, Char_t414);
      if (call_ret_t413) {
        instr_struct(&SomeUL_t415, 18, 1, (tll_ptr)2);
        ifte_ret_t445 = SomeUL_t415;
      }
      else {
        instr_struct(&Char_t417, 5, 1, (tll_ptr)51);
        call_ret_t416 = eqc_i18(c_v141824, Char_t417);
        if (call_ret_t416) {
          instr_struct(&SomeUL_t418, 18, 1, (tll_ptr)3);
          ifte_ret_t444 = SomeUL_t418;
        }
        else {
          instr_struct(&Char_t420, 5, 1, (tll_ptr)52);
          call_ret_t419 = eqc_i18(c_v141824, Char_t420);
          if (call_ret_t419) {
            instr_struct(&SomeUL_t421, 18, 1, (tll_ptr)4);
            ifte_ret_t443 = SomeUL_t421;
          }
          else {
            instr_struct(&Char_t423, 5, 1, (tll_ptr)53);
            call_ret_t422 = eqc_i18(c_v141824, Char_t423);
            if (call_ret_t422) {
              instr_struct(&SomeUL_t424, 18, 1, (tll_ptr)5);
              ifte_ret_t442 = SomeUL_t424;
            }
            else {
              instr_struct(&Char_t426, 5, 1, (tll_ptr)54);
              call_ret_t425 = eqc_i18(c_v141824, Char_t426);
              if (call_ret_t425) {
                instr_struct(&SomeUL_t427, 18, 1, (tll_ptr)6);
                ifte_ret_t441 = SomeUL_t427;
              }
              else {
                instr_struct(&Char_t429, 5, 1, (tll_ptr)55);
                call_ret_t428 = eqc_i18(c_v141824, Char_t429);
                if (call_ret_t428) {
                  instr_struct(&SomeUL_t430, 18, 1, (tll_ptr)7);
                  ifte_ret_t440 = SomeUL_t430;
                }
                else {
                  instr_struct(&Char_t432, 5, 1, (tll_ptr)56);
                  call_ret_t431 = eqc_i18(c_v141824, Char_t432);
                  if (call_ret_t431) {
                    instr_struct(&SomeUL_t433, 18, 1, (tll_ptr)8);
                    ifte_ret_t439 = SomeUL_t433;
                  }
                  else {
                    instr_struct(&Char_t435, 5, 1, (tll_ptr)57);
                    call_ret_t434 = eqc_i18(c_v141824, Char_t435);
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

tll_ptr lam_fun_t449(tll_ptr c_v141825, tll_env env) {
  tll_ptr call_ret_t448;
  call_ret_t448 = digit_of_char_i40(c_v141825);
  return call_ret_t448;
}

tll_ptr nat_of_string_loop_i41(tll_ptr s_v141826, tll_ptr acc_v141827) {
  tll_ptr NoneUL_t455; tll_ptr SomeUL_t452; tll_ptr c_v141828;
  tll_ptr call_ret_t453; tll_ptr call_ret_t456; tll_ptr call_ret_t457;
  tll_ptr call_ret_t458; tll_ptr n_v141830; tll_ptr s_v141829;
  tll_ptr switch_ret_t451; tll_ptr switch_ret_t454;
  switch(((tll_node)s_v141826)->tag) {
    case 6:
      instr_struct(&SomeUL_t452, 18, 1, acc_v141827);
      switch_ret_t451 = SomeUL_t452;
      break;
    case 7:
      c_v141828 = ((tll_node)s_v141826)->data[0];
      s_v141829 = ((tll_node)s_v141826)->data[1];
      call_ret_t453 = digit_of_char_i40(c_v141828);
      switch(((tll_node)call_ret_t453)->tag) {
        case 17:
          instr_free_struct(call_ret_t453);
          instr_struct(&NoneUL_t455, 17, 0);
          switch_ret_t454 = NoneUL_t455;
          break;
        case 18:
          n_v141830 = ((tll_node)call_ret_t453)->data[0];
          instr_free_struct(call_ret_t453);
          call_ret_t458 = muln_i15(acc_v141827, (tll_ptr)10);
          call_ret_t457 = addn_i13(call_ret_t458, n_v141830);
          call_ret_t456 = nat_of_string_loop_i41(s_v141829, call_ret_t457);
          switch_ret_t454 = call_ret_t456;
          break;
      }
      switch_ret_t451 = switch_ret_t454;
      break;
  }
  return switch_ret_t451;
}

tll_ptr lam_fun_t460(tll_ptr acc_v141833, tll_env env) {
  tll_ptr call_ret_t459;
  call_ret_t459 = nat_of_string_loop_i41(env[0], acc_v141833);
  return call_ret_t459;
}

tll_ptr lam_fun_t462(tll_ptr s_v141831, tll_env env) {
  tll_ptr lam_clo_t461;
  instr_clo(&lam_clo_t461, &lam_fun_t460, 1, s_v141831);
  return lam_clo_t461;
}

tll_ptr nat_of_string_i42(tll_ptr s_v141834) {
  tll_ptr call_ret_t464;
  call_ret_t464 = nat_of_string_loop_i41(s_v141834, (tll_ptr)0);
  return call_ret_t464;
}

tll_ptr lam_fun_t466(tll_ptr s_v141835, tll_env env) {
  tll_ptr call_ret_t465;
  call_ret_t465 = nat_of_string_i42(s_v141835);
  return call_ret_t465;
}

tll_ptr string_diff_i49(tll_ptr s1_v141836, tll_ptr s2_v141837) {
  tll_ptr Char_t474; tll_ptr Char_t479; tll_ptr EmptyString_t469;
  tll_ptr EmptyString_t471; tll_ptr EmptyString_t475;
  tll_ptr EmptyString_t480; tll_ptr String_t476; tll_ptr String_t481;
  tll_ptr c1_v141838; tll_ptr c2_v141840; tll_ptr call_ret_t472;
  tll_ptr call_ret_t473; tll_ptr call_ret_t477; tll_ptr call_ret_t478;
  tll_ptr call_ret_t482; tll_ptr ifte_ret_t483; tll_ptr s1_v141839;
  tll_ptr s2_v141841; tll_ptr switch_ret_t468; tll_ptr switch_ret_t470;
  switch(((tll_node)s1_v141836)->tag) {
    case 6:
      instr_struct(&EmptyString_t469, 6, 0);
      switch_ret_t468 = EmptyString_t469;
      break;
    case 7:
      c1_v141838 = ((tll_node)s1_v141836)->data[0];
      s1_v141839 = ((tll_node)s1_v141836)->data[1];
      switch(((tll_node)s2_v141837)->tag) {
        case 6:
          instr_struct(&EmptyString_t471, 6, 0);
          switch_ret_t470 = EmptyString_t471;
          break;
        case 7:
          c2_v141840 = ((tll_node)s2_v141837)->data[0];
          s2_v141841 = ((tll_node)s2_v141837)->data[1];
          call_ret_t472 = eqc_i18(c1_v141838, c2_v141840);
          if (call_ret_t472) {
            instr_struct(&Char_t474, 5, 1, (tll_ptr)89);
            instr_struct(&EmptyString_t475, 6, 0);
            instr_struct(&String_t476, 7, 2, Char_t474, EmptyString_t475);
            call_ret_t477 = string_diff_i49(s1_v141839, s2_v141841);
            call_ret_t473 = cats_i20(String_t476, call_ret_t477);
            ifte_ret_t483 = call_ret_t473;
          }
          else {
            instr_struct(&Char_t479, 5, 1, (tll_ptr)78);
            instr_struct(&EmptyString_t480, 6, 0);
            instr_struct(&String_t481, 7, 2, Char_t479, EmptyString_t480);
            call_ret_t482 = string_diff_i49(s1_v141839, s2_v141841);
            call_ret_t478 = cats_i20(String_t481, call_ret_t482);
            ifte_ret_t483 = call_ret_t478;
          }
          switch_ret_t470 = ifte_ret_t483;
          break;
      }
      switch_ret_t468 = switch_ret_t470;
      break;
  }
  return switch_ret_t468;
}

tll_ptr lam_fun_t485(tll_ptr s2_v141844, tll_env env) {
  tll_ptr call_ret_t484;
  call_ret_t484 = string_diff_i49(env[0], s2_v141844);
  return call_ret_t484;
}

tll_ptr lam_fun_t487(tll_ptr s1_v141842, tll_env env) {
  tll_ptr lam_clo_t486;
  instr_clo(&lam_clo_t486, &lam_fun_t485, 1, s1_v141842);
  return lam_clo_t486;
}

tll_ptr word_diff_i51(tll_ptr w1_v141845, tll_ptr w2_v141846) {
  tll_ptr Word_t492; tll_ptr call_ret_t491; tll_ptr pf1_v141848;
  tll_ptr pf2_v141850; tll_ptr s1_v141847; tll_ptr s2_v141849;
  tll_ptr switch_ret_t489; tll_ptr switch_ret_t490;
  switch(((tll_node)w1_v141845)->tag) {
    case 12:
      s1_v141847 = ((tll_node)w1_v141845)->data[0];
      pf1_v141848 = ((tll_node)w1_v141845)->data[1];
      switch(((tll_node)w2_v141846)->tag) {
        case 12:
          s2_v141849 = ((tll_node)w2_v141846)->data[0];
          pf2_v141850 = ((tll_node)w2_v141846)->data[1];
          call_ret_t491 = string_diff_i49(s1_v141847, s2_v141849);
          instr_struct(&Word_t492, 12, 2, call_ret_t491, 0);
          switch_ret_t490 = Word_t492;
          break;
      }
      switch_ret_t489 = switch_ret_t490;
      break;
  }
  return switch_ret_t489;
}

tll_ptr lam_fun_t494(tll_ptr w2_v141853, tll_env env) {
  tll_ptr call_ret_t493;
  call_ret_t493 = word_diff_i51(env[0], w2_v141853);
  return call_ret_t493;
}

tll_ptr lam_fun_t496(tll_ptr w1_v141851, tll_env env) {
  tll_ptr lam_clo_t495;
  instr_clo(&lam_clo_t495, &lam_fun_t494, 1, w1_v141851);
  return lam_clo_t495;
}

tll_ptr eqw_i52(tll_ptr w1_v141854, tll_ptr w2_v141855) {
  tll_ptr __v141857; tll_ptr __v141859; tll_ptr call_ret_t500;
  tll_ptr s1_v141856; tll_ptr s2_v141858; tll_ptr switch_ret_t498;
  tll_ptr switch_ret_t499;
  switch(((tll_node)w1_v141854)->tag) {
    case 12:
      s1_v141856 = ((tll_node)w1_v141854)->data[0];
      __v141857 = ((tll_node)w1_v141854)->data[1];
      switch(((tll_node)w2_v141855)->tag) {
        case 12:
          s2_v141858 = ((tll_node)w2_v141855)->data[0];
          __v141859 = ((tll_node)w2_v141855)->data[1];
          call_ret_t500 = eqs_i22(s1_v141856, s2_v141858);
          switch_ret_t499 = call_ret_t500;
          break;
      }
      switch_ret_t498 = switch_ret_t499;
      break;
  }
  return switch_ret_t498;
}

tll_ptr lam_fun_t502(tll_ptr w2_v141862, tll_env env) {
  tll_ptr call_ret_t501;
  call_ret_t501 = eqw_i52(env[0], w2_v141862);
  return call_ret_t501;
}

tll_ptr lam_fun_t504(tll_ptr w1_v141860, tll_env env) {
  tll_ptr lam_clo_t503;
  instr_clo(&lam_clo_t503, &lam_fun_t502, 1, w1_v141860);
  return lam_clo_t503;
}

tll_ptr lam_fun_t511(tll_ptr __v141874, tll_env env) {
  tll_ptr Word_t510;
  instr_struct(&Word_t510, 12, 2, env[0], 0);
  return Word_t510;
}

tll_ptr lam_fun_t513(tll_ptr e_v141872, tll_env env) {
  tll_ptr lam_clo_t512;
  instr_clo(&lam_clo_t512, &lam_fun_t511, 1, env[0]);
  return lam_clo_t512;
}

tll_ptr lam_fun_t594(tll_ptr __v141878, tll_env env) {
  tll_ptr Char_t516; tll_ptr Char_t517; tll_ptr Char_t518; tll_ptr Char_t519;
  tll_ptr Char_t520; tll_ptr Char_t521; tll_ptr Char_t522; tll_ptr Char_t523;
  tll_ptr Char_t524; tll_ptr Char_t525; tll_ptr Char_t526; tll_ptr Char_t527;
  tll_ptr Char_t528; tll_ptr Char_t529; tll_ptr Char_t530; tll_ptr Char_t531;
  tll_ptr Char_t532; tll_ptr Char_t533; tll_ptr Char_t534; tll_ptr Char_t535;
  tll_ptr Char_t536; tll_ptr Char_t537; tll_ptr Char_t538; tll_ptr Char_t539;
  tll_ptr Char_t540; tll_ptr Char_t541; tll_ptr Char_t542; tll_ptr Char_t543;
  tll_ptr Char_t544; tll_ptr Char_t545; tll_ptr Char_t546; tll_ptr Char_t547;
  tll_ptr Char_t548; tll_ptr Char_t549; tll_ptr Char_t550; tll_ptr Char_t551;
  tll_ptr Char_t552; tll_ptr EmptyString_t553; tll_ptr String_t554;
  tll_ptr String_t555; tll_ptr String_t556; tll_ptr String_t557;
  tll_ptr String_t558; tll_ptr String_t559; tll_ptr String_t560;
  tll_ptr String_t561; tll_ptr String_t562; tll_ptr String_t563;
  tll_ptr String_t564; tll_ptr String_t565; tll_ptr String_t566;
  tll_ptr String_t567; tll_ptr String_t568; tll_ptr String_t569;
  tll_ptr String_t570; tll_ptr String_t571; tll_ptr String_t572;
  tll_ptr String_t573; tll_ptr String_t574; tll_ptr String_t575;
  tll_ptr String_t576; tll_ptr String_t577; tll_ptr String_t578;
  tll_ptr String_t579; tll_ptr String_t580; tll_ptr String_t581;
  tll_ptr String_t582; tll_ptr String_t583; tll_ptr String_t584;
  tll_ptr String_t585; tll_ptr String_t586; tll_ptr String_t587;
  tll_ptr String_t588; tll_ptr String_t589; tll_ptr String_t590;
  tll_ptr __v141880; tll_ptr app_ret_t591; tll_ptr app_ret_t593;
  tll_ptr call_ret_t515; tll_ptr call_ret_t592;
  instr_struct(&Char_t516, 5, 1, (tll_ptr)112);
  instr_struct(&Char_t517, 5, 1, (tll_ptr)108);
  instr_struct(&Char_t518, 5, 1, (tll_ptr)101);
  instr_struct(&Char_t519, 5, 1, (tll_ptr)97);
  instr_struct(&Char_t520, 5, 1, (tll_ptr)115);
  instr_struct(&Char_t521, 5, 1, (tll_ptr)101);
  instr_struct(&Char_t522, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t523, 5, 1, (tll_ptr)105);
  instr_struct(&Char_t524, 5, 1, (tll_ptr)110);
  instr_struct(&Char_t525, 5, 1, (tll_ptr)112);
  instr_struct(&Char_t526, 5, 1, (tll_ptr)117);
  instr_struct(&Char_t527, 5, 1, (tll_ptr)116);
  instr_struct(&Char_t528, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t529, 5, 1, (tll_ptr)97);
  instr_struct(&Char_t530, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t531, 5, 1, (tll_ptr)119);
  instr_struct(&Char_t532, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t533, 5, 1, (tll_ptr)114);
  instr_struct(&Char_t534, 5, 1, (tll_ptr)100);
  instr_struct(&Char_t535, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t536, 5, 1, (tll_ptr)119);
  instr_struct(&Char_t537, 5, 1, (tll_ptr)105);
  instr_struct(&Char_t538, 5, 1, (tll_ptr)116);
  instr_struct(&Char_t539, 5, 1, (tll_ptr)104);
  instr_struct(&Char_t540, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t541, 5, 1, (tll_ptr)108);
  instr_struct(&Char_t542, 5, 1, (tll_ptr)101);
  instr_struct(&Char_t543, 5, 1, (tll_ptr)110);
  instr_struct(&Char_t544, 5, 1, (tll_ptr)103);
  instr_struct(&Char_t545, 5, 1, (tll_ptr)116);
  instr_struct(&Char_t546, 5, 1, (tll_ptr)104);
  instr_struct(&Char_t547, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t548, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t549, 5, 1, (tll_ptr)102);
  instr_struct(&Char_t550, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t551, 5, 1, (tll_ptr)53);
  instr_struct(&Char_t552, 5, 1, (tll_ptr)10);
  instr_struct(&EmptyString_t553, 6, 0);
  instr_struct(&String_t554, 7, 2, Char_t552, EmptyString_t553);
  instr_struct(&String_t555, 7, 2, Char_t551, String_t554);
  instr_struct(&String_t556, 7, 2, Char_t550, String_t555);
  instr_struct(&String_t557, 7, 2, Char_t549, String_t556);
  instr_struct(&String_t558, 7, 2, Char_t548, String_t557);
  instr_struct(&String_t559, 7, 2, Char_t547, String_t558);
  instr_struct(&String_t560, 7, 2, Char_t546, String_t559);
  instr_struct(&String_t561, 7, 2, Char_t545, String_t560);
  instr_struct(&String_t562, 7, 2, Char_t544, String_t561);
  instr_struct(&String_t563, 7, 2, Char_t543, String_t562);
  instr_struct(&String_t564, 7, 2, Char_t542, String_t563);
  instr_struct(&String_t565, 7, 2, Char_t541, String_t564);
  instr_struct(&String_t566, 7, 2, Char_t540, String_t565);
  instr_struct(&String_t567, 7, 2, Char_t539, String_t566);
  instr_struct(&String_t568, 7, 2, Char_t538, String_t567);
  instr_struct(&String_t569, 7, 2, Char_t537, String_t568);
  instr_struct(&String_t570, 7, 2, Char_t536, String_t569);
  instr_struct(&String_t571, 7, 2, Char_t535, String_t570);
  instr_struct(&String_t572, 7, 2, Char_t534, String_t571);
  instr_struct(&String_t573, 7, 2, Char_t533, String_t572);
  instr_struct(&String_t574, 7, 2, Char_t532, String_t573);
  instr_struct(&String_t575, 7, 2, Char_t531, String_t574);
  instr_struct(&String_t576, 7, 2, Char_t530, String_t575);
  instr_struct(&String_t577, 7, 2, Char_t529, String_t576);
  instr_struct(&String_t578, 7, 2, Char_t528, String_t577);
  instr_struct(&String_t579, 7, 2, Char_t527, String_t578);
  instr_struct(&String_t580, 7, 2, Char_t526, String_t579);
  instr_struct(&String_t581, 7, 2, Char_t525, String_t580);
  instr_struct(&String_t582, 7, 2, Char_t524, String_t581);
  instr_struct(&String_t583, 7, 2, Char_t523, String_t582);
  instr_struct(&String_t584, 7, 2, Char_t522, String_t583);
  instr_struct(&String_t585, 7, 2, Char_t521, String_t584);
  instr_struct(&String_t586, 7, 2, Char_t520, String_t585);
  instr_struct(&String_t587, 7, 2, Char_t519, String_t586);
  instr_struct(&String_t588, 7, 2, Char_t518, String_t587);
  instr_struct(&String_t589, 7, 2, Char_t517, String_t588);
  instr_struct(&String_t590, 7, 2, Char_t516, String_t589);
  call_ret_t515 = print_i34(String_t590);
  instr_app(&app_ret_t591, call_ret_t515, 0);
  instr_free_clo(call_ret_t515);
  __v141880 = app_ret_t591;
  call_ret_t592 = read_word_i59(0);
  instr_app(&app_ret_t593, call_ret_t592, 0);
  instr_free_clo(call_ret_t592);
  return app_ret_t593;
}

tll_ptr lam_fun_t596(tll_ptr __v141875, tll_env env) {
  tll_ptr lam_clo_t595;
  instr_clo(&lam_clo_t595, &lam_fun_t594, 0);
  return lam_clo_t595;
}

tll_ptr lam_fun_t601(tll_ptr __v141864, tll_env env) {
  tll_ptr app_ret_t507; tll_ptr app_ret_t599; tll_ptr app_ret_t600;
  tll_ptr call_ret_t506; tll_ptr call_ret_t508; tll_ptr call_ret_t509;
  tll_ptr ifte_ret_t598; tll_ptr lam_clo_t514; tll_ptr lam_clo_t597;
  tll_ptr s_v141871;
  call_ret_t506 = readline_i33(0);
  instr_app(&app_ret_t507, call_ret_t506, 0);
  instr_free_clo(call_ret_t506);
  s_v141871 = app_ret_t507;
  call_ret_t509 = strlen_i21(s_v141871);
  call_ret_t508 = eqn_i10(call_ret_t509, (tll_ptr)5);
  if (call_ret_t508) {
    instr_clo(&lam_clo_t514, &lam_fun_t513, 1, s_v141871);
    ifte_ret_t598 = lam_clo_t514;
  }
  else {
    instr_clo(&lam_clo_t597, &lam_fun_t596, 0);
    ifte_ret_t598 = lam_clo_t597;
  }
  instr_app(&app_ret_t599, ifte_ret_t598, 0);
  instr_app(&app_ret_t600, app_ret_t599, 0);
  instr_free_clo(app_ret_t599);
  return app_ret_t600;
}

tll_ptr read_word_i59(tll_ptr __v141863) {
  tll_ptr lam_clo_t602;
  instr_clo(&lam_clo_t602, &lam_fun_t601, 0);
  return lam_clo_t602;
}

tll_ptr lam_fun_t604(tll_ptr __v141881, tll_env env) {
  tll_ptr call_ret_t603;
  call_ret_t603 = read_word_i59(__v141881);
  return call_ret_t603;
}

tll_ptr lam_fun_t635(tll_ptr __v141938, tll_env env) {
  tll_ptr Char_t614; tll_ptr Char_t615; tll_ptr Char_t616; tll_ptr Char_t617;
  tll_ptr Char_t618; tll_ptr Char_t619; tll_ptr Char_t620; tll_ptr Char_t621;
  tll_ptr Char_t622; tll_ptr EmptyString_t623; tll_ptr String_t624;
  tll_ptr String_t625; tll_ptr String_t626; tll_ptr String_t627;
  tll_ptr String_t628; tll_ptr String_t629; tll_ptr String_t630;
  tll_ptr String_t631; tll_ptr String_t632; tll_ptr __v141940;
  tll_ptr app_ret_t633; tll_ptr call_ret_t613; tll_ptr close_tmp_t634;
  instr_struct(&Char_t614, 5, 1, (tll_ptr)89);
  instr_struct(&Char_t615, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t616, 5, 1, (tll_ptr)117);
  instr_struct(&Char_t617, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t618, 5, 1, (tll_ptr)87);
  instr_struct(&Char_t619, 5, 1, (tll_ptr)105);
  instr_struct(&Char_t620, 5, 1, (tll_ptr)110);
  instr_struct(&Char_t621, 5, 1, (tll_ptr)33);
  instr_struct(&Char_t622, 5, 1, (tll_ptr)10);
  instr_struct(&EmptyString_t623, 6, 0);
  instr_struct(&String_t624, 7, 2, Char_t622, EmptyString_t623);
  instr_struct(&String_t625, 7, 2, Char_t621, String_t624);
  instr_struct(&String_t626, 7, 2, Char_t620, String_t625);
  instr_struct(&String_t627, 7, 2, Char_t619, String_t626);
  instr_struct(&String_t628, 7, 2, Char_t618, String_t627);
  instr_struct(&String_t629, 7, 2, Char_t617, String_t628);
  instr_struct(&String_t630, 7, 2, Char_t616, String_t629);
  instr_struct(&String_t631, 7, 2, Char_t615, String_t630);
  instr_struct(&String_t632, 7, 2, Char_t614, String_t631);
  call_ret_t613 = print_i34(String_t632);
  instr_app(&app_ret_t633, call_ret_t613, 0);
  instr_free_clo(call_ret_t613);
  __v141940 = app_ret_t633;
  instr_close(&close_tmp_t634, env[0]);
  return close_tmp_t634;
}

tll_ptr lam_fun_t637(tll_ptr c_v141935, tll_env env) {
  tll_ptr lam_clo_t636;
  instr_clo(&lam_clo_t636, &lam_fun_t635, 1, c_v141935);
  return lam_clo_t636;
}

tll_ptr lam_fun_t740(tll_ptr __v141951, tll_env env) {
  tll_ptr Char_t649; tll_ptr Char_t650; tll_ptr Char_t651; tll_ptr Char_t652;
  tll_ptr Char_t653; tll_ptr Char_t654; tll_ptr Char_t655; tll_ptr Char_t656;
  tll_ptr Char_t657; tll_ptr Char_t658; tll_ptr Char_t659; tll_ptr Char_t660;
  tll_ptr Char_t661; tll_ptr Char_t662; tll_ptr Char_t663; tll_ptr Char_t664;
  tll_ptr Char_t665; tll_ptr Char_t684; tll_ptr Char_t685; tll_ptr Char_t686;
  tll_ptr Char_t687; tll_ptr Char_t688; tll_ptr Char_t689; tll_ptr Char_t690;
  tll_ptr Char_t691; tll_ptr Char_t692; tll_ptr Char_t693; tll_ptr Char_t694;
  tll_ptr Char_t709; tll_ptr Char_t710; tll_ptr Char_t711; tll_ptr Char_t712;
  tll_ptr Char_t713; tll_ptr Char_t714; tll_ptr Char_t715; tll_ptr Char_t716;
  tll_ptr Char_t717; tll_ptr Char_t718; tll_ptr Char_t719; tll_ptr Char_t720;
  tll_ptr Char_t721; tll_ptr EmptyString_t666; tll_ptr EmptyString_t695;
  tll_ptr EmptyString_t722; tll_ptr String_t667; tll_ptr String_t668;
  tll_ptr String_t669; tll_ptr String_t670; tll_ptr String_t671;
  tll_ptr String_t672; tll_ptr String_t673; tll_ptr String_t674;
  tll_ptr String_t675; tll_ptr String_t676; tll_ptr String_t677;
  tll_ptr String_t678; tll_ptr String_t679; tll_ptr String_t680;
  tll_ptr String_t681; tll_ptr String_t682; tll_ptr String_t683;
  tll_ptr String_t696; tll_ptr String_t697; tll_ptr String_t698;
  tll_ptr String_t699; tll_ptr String_t700; tll_ptr String_t701;
  tll_ptr String_t702; tll_ptr String_t703; tll_ptr String_t704;
  tll_ptr String_t705; tll_ptr String_t706; tll_ptr String_t723;
  tll_ptr String_t724; tll_ptr String_t725; tll_ptr String_t726;
  tll_ptr String_t727; tll_ptr String_t728; tll_ptr String_t729;
  tll_ptr String_t730; tll_ptr String_t731; tll_ptr String_t732;
  tll_ptr String_t733; tll_ptr String_t734; tll_ptr String_t735;
  tll_ptr __v141960; tll_ptr __v141966; tll_ptr __v141967;
  tll_ptr add_ret_t708; tll_ptr add_ret_t738; tll_ptr app_ret_t736;
  tll_ptr app_ret_t739; tll_ptr c_v141962; tll_ptr c_v141964;
  tll_ptr call_ret_t644; tll_ptr call_ret_t645; tll_ptr call_ret_t646;
  tll_ptr call_ret_t647; tll_ptr call_ret_t648; tll_ptr call_ret_t707;
  tll_ptr call_ret_t737; tll_ptr diff_v141961; tll_ptr pair_struct_t641;
  tll_ptr pf_v141963; tll_ptr recv_msg_t639; tll_ptr s_v141965;
  tll_ptr switch_ret_t640; tll_ptr switch_ret_t642; tll_ptr switch_ret_t643;
  instr_recv(&recv_msg_t639, env[0]);
  __v141960 = recv_msg_t639;
  switch(((tll_node)__v141960)->tag) {
    case 0:
      diff_v141961 = ((tll_node)__v141960)->data[0];
      c_v141962 = ((tll_node)__v141960)->data[1];
      instr_free_struct(__v141960);
      instr_struct(&pair_struct_t641, 0, 2, 0, c_v141962);
      switch(((tll_node)pair_struct_t641)->tag) {
        case 0:
          pf_v141963 = ((tll_node)pair_struct_t641)->data[0];
          c_v141964 = ((tll_node)pair_struct_t641)->data[1];
          instr_free_struct(pair_struct_t641);
          switch(((tll_node)diff_v141961)->tag) {
            case 12:
              s_v141965 = ((tll_node)diff_v141961)->data[0];
              __v141966 = ((tll_node)diff_v141961)->data[1];
              instr_struct(&Char_t649, 5, 1, (tll_ptr)73);
              instr_struct(&Char_t650, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t651, 5, 1, (tll_ptr)99);
              instr_struct(&Char_t652, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t653, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t654, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t655, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t656, 5, 1, (tll_ptr)99);
              instr_struct(&Char_t657, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t658, 5, 1, (tll_ptr)44);
              instr_struct(&Char_t659, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t660, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t661, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t662, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t663, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t664, 5, 1, (tll_ptr)58);
              instr_struct(&Char_t665, 5, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t666, 6, 0);
              instr_struct(&String_t667, 7, 2, Char_t665, EmptyString_t666);
              instr_struct(&String_t668, 7, 2, Char_t664, String_t667);
              instr_struct(&String_t669, 7, 2, Char_t663, String_t668);
              instr_struct(&String_t670, 7, 2, Char_t662, String_t669);
              instr_struct(&String_t671, 7, 2, Char_t661, String_t670);
              instr_struct(&String_t672, 7, 2, Char_t660, String_t671);
              instr_struct(&String_t673, 7, 2, Char_t659, String_t672);
              instr_struct(&String_t674, 7, 2, Char_t658, String_t673);
              instr_struct(&String_t675, 7, 2, Char_t657, String_t674);
              instr_struct(&String_t676, 7, 2, Char_t656, String_t675);
              instr_struct(&String_t677, 7, 2, Char_t655, String_t676);
              instr_struct(&String_t678, 7, 2, Char_t654, String_t677);
              instr_struct(&String_t679, 7, 2, Char_t653, String_t678);
              instr_struct(&String_t680, 7, 2, Char_t652, String_t679);
              instr_struct(&String_t681, 7, 2, Char_t651, String_t680);
              instr_struct(&String_t682, 7, 2, Char_t650, String_t681);
              instr_struct(&String_t683, 7, 2, Char_t649, String_t682);
              call_ret_t648 = cats_i20(String_t683, s_v141965);
              instr_struct(&Char_t684, 5, 1, (tll_ptr)46);
              instr_struct(&Char_t685, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t686, 5, 1, (tll_ptr)89);
              instr_struct(&Char_t687, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t688, 5, 1, (tll_ptr)117);
              instr_struct(&Char_t689, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t690, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t691, 5, 1, (tll_ptr)97);
              instr_struct(&Char_t692, 5, 1, (tll_ptr)118);
              instr_struct(&Char_t693, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t694, 5, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t695, 6, 0);
              instr_struct(&String_t696, 7, 2, Char_t694, EmptyString_t695);
              instr_struct(&String_t697, 7, 2, Char_t693, String_t696);
              instr_struct(&String_t698, 7, 2, Char_t692, String_t697);
              instr_struct(&String_t699, 7, 2, Char_t691, String_t698);
              instr_struct(&String_t700, 7, 2, Char_t690, String_t699);
              instr_struct(&String_t701, 7, 2, Char_t689, String_t700);
              instr_struct(&String_t702, 7, 2, Char_t688, String_t701);
              instr_struct(&String_t703, 7, 2, Char_t687, String_t702);
              instr_struct(&String_t704, 7, 2, Char_t686, String_t703);
              instr_struct(&String_t705, 7, 2, Char_t685, String_t704);
              instr_struct(&String_t706, 7, 2, Char_t684, String_t705);
              call_ret_t647 = cats_i20(call_ret_t648, String_t706);
              add_ret_t708 = env[1] - 1;
              call_ret_t707 = string_of_nat_i39(add_ret_t708);
              call_ret_t646 = cats_i20(call_ret_t647, call_ret_t707);
              instr_struct(&Char_t709, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t710, 5, 1, (tll_ptr)109);
              instr_struct(&Char_t711, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t712, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t713, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t714, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t715, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t716, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t717, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t718, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t719, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t720, 5, 1, (tll_ptr)46);
              instr_struct(&Char_t721, 5, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t722, 6, 0);
              instr_struct(&String_t723, 7, 2, Char_t721, EmptyString_t722);
              instr_struct(&String_t724, 7, 2, Char_t720, String_t723);
              instr_struct(&String_t725, 7, 2, Char_t719, String_t724);
              instr_struct(&String_t726, 7, 2, Char_t718, String_t725);
              instr_struct(&String_t727, 7, 2, Char_t717, String_t726);
              instr_struct(&String_t728, 7, 2, Char_t716, String_t727);
              instr_struct(&String_t729, 7, 2, Char_t715, String_t728);
              instr_struct(&String_t730, 7, 2, Char_t714, String_t729);
              instr_struct(&String_t731, 7, 2, Char_t713, String_t730);
              instr_struct(&String_t732, 7, 2, Char_t712, String_t731);
              instr_struct(&String_t733, 7, 2, Char_t711, String_t732);
              instr_struct(&String_t734, 7, 2, Char_t710, String_t733);
              instr_struct(&String_t735, 7, 2, Char_t709, String_t734);
              call_ret_t645 = cats_i20(call_ret_t646, String_t735);
              call_ret_t644 = print_i34(call_ret_t645);
              instr_app(&app_ret_t736, call_ret_t644, 0);
              instr_free_clo(call_ret_t644);
              __v141967 = app_ret_t736;
              add_ret_t738 = env[1] - 1;
              call_ret_t737 = player_loop_i60(0, add_ret_t738, c_v141964);
              instr_app(&app_ret_t739, call_ret_t737, 0);
              instr_free_clo(call_ret_t737);
              switch_ret_t643 = app_ret_t739;
              break;
          }
          switch_ret_t642 = switch_ret_t643;
          break;
      }
      switch_ret_t640 = switch_ret_t642;
      break;
  }
  return switch_ret_t640;
}

tll_ptr lam_fun_t742(tll_ptr c_v141941, tll_env env) {
  tll_ptr lam_clo_t741;
  instr_clo(&lam_clo_t741, &lam_fun_t740, 2, c_v141941, env[0]);
  return lam_clo_t741;
}

tll_ptr lam_fun_t747(tll_ptr __v141907, tll_env env) {
  tll_ptr __v141930; tll_ptr app_ret_t607; tll_ptr app_ret_t745;
  tll_ptr app_ret_t746; tll_ptr b_v141931; tll_ptr c_v141929;
  tll_ptr c_v141932; tll_ptr c_v141934; tll_ptr call_ret_t606;
  tll_ptr guess_v141928; tll_ptr ifte_ret_t744; tll_ptr lam_clo_t638;
  tll_ptr lam_clo_t743; tll_ptr pair_struct_t611; tll_ptr pf_v141933;
  tll_ptr recv_msg_t609; tll_ptr send_ch_t608; tll_ptr switch_ret_t610;
  tll_ptr switch_ret_t612;
  call_ret_t606 = read_word_i59(0);
  instr_app(&app_ret_t607, call_ret_t606, 0);
  instr_free_clo(call_ret_t606);
  guess_v141928 = app_ret_t607;
  instr_send(&send_ch_t608, env[0], guess_v141928);
  c_v141929 = send_ch_t608;
  instr_recv(&recv_msg_t609, c_v141929);
  __v141930 = recv_msg_t609;
  switch(((tll_node)__v141930)->tag) {
    case 0:
      b_v141931 = ((tll_node)__v141930)->data[0];
      c_v141932 = ((tll_node)__v141930)->data[1];
      instr_free_struct(__v141930);
      instr_struct(&pair_struct_t611, 0, 2, 0, c_v141932);
      switch(((tll_node)pair_struct_t611)->tag) {
        case 0:
          pf_v141933 = ((tll_node)pair_struct_t611)->data[0];
          c_v141934 = ((tll_node)pair_struct_t611)->data[1];
          instr_free_struct(pair_struct_t611);
          if (b_v141931) {
            instr_clo(&lam_clo_t638, &lam_fun_t637, 0);
            ifte_ret_t744 = lam_clo_t638;
          }
          else {
            instr_clo(&lam_clo_t743, &lam_fun_t742, 1, env[1]);
            ifte_ret_t744 = lam_clo_t743;
          }
          instr_app(&app_ret_t745, ifte_ret_t744, c_v141934);
          instr_free_clo(ifte_ret_t744);
          instr_app(&app_ret_t746, app_ret_t745, 0);
          instr_free_clo(app_ret_t745);
          switch_ret_t612 = app_ret_t746;
          break;
      }
      switch_ret_t610 = switch_ret_t612;
      break;
  }
  return switch_ret_t610;
}

tll_ptr lam_fun_t749(tll_ptr c_v141885, tll_env env) {
  tll_ptr lam_clo_t748;
  instr_clo(&lam_clo_t748, &lam_fun_t747, 2, c_v141885, env[0]);
  return lam_clo_t748;
}

tll_ptr lam_fun_t815(tll_ptr __v141978, tll_env env) {
  tll_ptr Char_t759; tll_ptr Char_t760; tll_ptr Char_t761; tll_ptr Char_t762;
  tll_ptr Char_t763; tll_ptr Char_t764; tll_ptr Char_t765; tll_ptr Char_t766;
  tll_ptr Char_t767; tll_ptr Char_t768; tll_ptr Char_t769; tll_ptr Char_t770;
  tll_ptr Char_t771; tll_ptr Char_t772; tll_ptr Char_t773; tll_ptr Char_t774;
  tll_ptr Char_t775; tll_ptr Char_t776; tll_ptr Char_t777; tll_ptr Char_t778;
  tll_ptr Char_t779; tll_ptr Char_t780; tll_ptr Char_t781; tll_ptr Char_t782;
  tll_ptr Char_t808; tll_ptr Char_t809; tll_ptr EmptyString_t783;
  tll_ptr EmptyString_t810; tll_ptr String_t784; tll_ptr String_t785;
  tll_ptr String_t786; tll_ptr String_t787; tll_ptr String_t788;
  tll_ptr String_t789; tll_ptr String_t790; tll_ptr String_t791;
  tll_ptr String_t792; tll_ptr String_t793; tll_ptr String_t794;
  tll_ptr String_t795; tll_ptr String_t796; tll_ptr String_t797;
  tll_ptr String_t798; tll_ptr String_t799; tll_ptr String_t800;
  tll_ptr String_t801; tll_ptr String_t802; tll_ptr String_t803;
  tll_ptr String_t804; tll_ptr String_t805; tll_ptr String_t806;
  tll_ptr String_t807; tll_ptr String_t811; tll_ptr String_t812;
  tll_ptr __v141987; tll_ptr __v141993; tll_ptr __v141994;
  tll_ptr ans_v141988; tll_ptr app_ret_t813; tll_ptr c_v141989;
  tll_ptr c_v141991; tll_ptr call_ret_t756; tll_ptr call_ret_t757;
  tll_ptr call_ret_t758; tll_ptr close_tmp_t814; tll_ptr pair_struct_t753;
  tll_ptr pf_v141990; tll_ptr recv_msg_t751; tll_ptr s_v141992;
  tll_ptr switch_ret_t752; tll_ptr switch_ret_t754; tll_ptr switch_ret_t755;
  instr_recv(&recv_msg_t751, env[0]);
  __v141987 = recv_msg_t751;
  switch(((tll_node)__v141987)->tag) {
    case 0:
      ans_v141988 = ((tll_node)__v141987)->data[0];
      c_v141989 = ((tll_node)__v141987)->data[1];
      instr_free_struct(__v141987);
      instr_struct(&pair_struct_t753, 0, 2, 0, c_v141989);
      switch(((tll_node)pair_struct_t753)->tag) {
        case 0:
          pf_v141990 = ((tll_node)pair_struct_t753)->data[0];
          c_v141991 = ((tll_node)pair_struct_t753)->data[1];
          instr_free_struct(pair_struct_t753);
          switch(((tll_node)ans_v141988)->tag) {
            case 12:
              s_v141992 = ((tll_node)ans_v141988)->data[0];
              __v141993 = ((tll_node)ans_v141988)->data[1];
              instr_struct(&Char_t759, 5, 1, (tll_ptr)89);
              instr_struct(&Char_t760, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t761, 5, 1, (tll_ptr)117);
              instr_struct(&Char_t762, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t763, 5, 1, (tll_ptr)76);
              instr_struct(&Char_t764, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t765, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t766, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t767, 5, 1, (tll_ptr)33);
              instr_struct(&Char_t768, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t769, 5, 1, (tll_ptr)84);
              instr_struct(&Char_t770, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t771, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t772, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t773, 5, 1, (tll_ptr)97);
              instr_struct(&Char_t774, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t775, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t776, 5, 1, (tll_ptr)119);
              instr_struct(&Char_t777, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t778, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t779, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t780, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t781, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t782, 5, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t783, 6, 0);
              instr_struct(&String_t784, 7, 2, Char_t782, EmptyString_t783);
              instr_struct(&String_t785, 7, 2, Char_t781, String_t784);
              instr_struct(&String_t786, 7, 2, Char_t780, String_t785);
              instr_struct(&String_t787, 7, 2, Char_t779, String_t786);
              instr_struct(&String_t788, 7, 2, Char_t778, String_t787);
              instr_struct(&String_t789, 7, 2, Char_t777, String_t788);
              instr_struct(&String_t790, 7, 2, Char_t776, String_t789);
              instr_struct(&String_t791, 7, 2, Char_t775, String_t790);
              instr_struct(&String_t792, 7, 2, Char_t774, String_t791);
              instr_struct(&String_t793, 7, 2, Char_t773, String_t792);
              instr_struct(&String_t794, 7, 2, Char_t772, String_t793);
              instr_struct(&String_t795, 7, 2, Char_t771, String_t794);
              instr_struct(&String_t796, 7, 2, Char_t770, String_t795);
              instr_struct(&String_t797, 7, 2, Char_t769, String_t796);
              instr_struct(&String_t798, 7, 2, Char_t768, String_t797);
              instr_struct(&String_t799, 7, 2, Char_t767, String_t798);
              instr_struct(&String_t800, 7, 2, Char_t766, String_t799);
              instr_struct(&String_t801, 7, 2, Char_t765, String_t800);
              instr_struct(&String_t802, 7, 2, Char_t764, String_t801);
              instr_struct(&String_t803, 7, 2, Char_t763, String_t802);
              instr_struct(&String_t804, 7, 2, Char_t762, String_t803);
              instr_struct(&String_t805, 7, 2, Char_t761, String_t804);
              instr_struct(&String_t806, 7, 2, Char_t760, String_t805);
              instr_struct(&String_t807, 7, 2, Char_t759, String_t806);
              call_ret_t758 = cats_i20(String_t807, s_v141992);
              instr_struct(&Char_t808, 5, 1, (tll_ptr)46);
              instr_struct(&Char_t809, 5, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t810, 6, 0);
              instr_struct(&String_t811, 7, 2, Char_t809, EmptyString_t810);
              instr_struct(&String_t812, 7, 2, Char_t808, String_t811);
              call_ret_t757 = cats_i20(call_ret_t758, String_t812);
              call_ret_t756 = print_i34(call_ret_t757);
              instr_app(&app_ret_t813, call_ret_t756, 0);
              instr_free_clo(call_ret_t756);
              __v141994 = app_ret_t813;
              instr_close(&close_tmp_t814, c_v141991);
              switch_ret_t755 = close_tmp_t814;
              break;
          }
          switch_ret_t754 = switch_ret_t755;
          break;
      }
      switch_ret_t752 = switch_ret_t754;
      break;
  }
  return switch_ret_t752;
}

tll_ptr lam_fun_t817(tll_ptr c_v141968, tll_env env) {
  tll_ptr lam_clo_t816;
  instr_clo(&lam_clo_t816, &lam_fun_t815, 1, c_v141968);
  return lam_clo_t816;
}

tll_ptr player_loop_i60(tll_ptr ans_v141882, tll_ptr repeat_v141883, tll_ptr c_v141884) {
  tll_ptr app_ret_t820; tll_ptr ifte_ret_t819; tll_ptr lam_clo_t750;
  tll_ptr lam_clo_t818;
  if (repeat_v141883) {
    instr_clo(&lam_clo_t750, &lam_fun_t749, 1, repeat_v141883);
    ifte_ret_t819 = lam_clo_t750;
  }
  else {
    instr_clo(&lam_clo_t818, &lam_fun_t817, 0);
    ifte_ret_t819 = lam_clo_t818;
  }
  instr_app(&app_ret_t820, ifte_ret_t819, c_v141884);
  return app_ret_t820;
}

tll_ptr lam_fun_t822(tll_ptr c_v142000, tll_env env) {
  tll_ptr call_ret_t821;
  call_ret_t821 = player_loop_i60(env[1], env[0], c_v142000);
  return call_ret_t821;
}

tll_ptr lam_fun_t824(tll_ptr repeat_v141998, tll_env env) {
  tll_ptr lam_clo_t823;
  instr_clo(&lam_clo_t823, &lam_fun_t822, 2, repeat_v141998, env[0]);
  return lam_clo_t823;
}

tll_ptr lam_fun_t826(tll_ptr ans_v141995, tll_env env) {
  tll_ptr lam_clo_t825;
  instr_clo(&lam_clo_t825, &lam_fun_t824, 1, ans_v141995);
  return lam_clo_t825;
}

tll_ptr lam_fun_t971(tll_ptr __v142002, tll_env env) {
  tll_ptr Char_t833; tll_ptr Char_t834; tll_ptr Char_t835; tll_ptr Char_t836;
  tll_ptr Char_t837; tll_ptr Char_t838; tll_ptr Char_t839; tll_ptr Char_t840;
  tll_ptr Char_t841; tll_ptr Char_t842; tll_ptr Char_t843; tll_ptr Char_t844;
  tll_ptr Char_t860; tll_ptr Char_t861; tll_ptr Char_t862; tll_ptr Char_t863;
  tll_ptr Char_t864; tll_ptr Char_t865; tll_ptr Char_t866; tll_ptr Char_t867;
  tll_ptr Char_t868; tll_ptr Char_t869; tll_ptr Char_t870; tll_ptr Char_t871;
  tll_ptr Char_t872; tll_ptr Char_t873; tll_ptr Char_t874; tll_ptr Char_t875;
  tll_ptr Char_t876; tll_ptr Char_t877; tll_ptr Char_t878; tll_ptr Char_t879;
  tll_ptr Char_t880; tll_ptr Char_t881; tll_ptr Char_t882; tll_ptr Char_t883;
  tll_ptr Char_t884; tll_ptr Char_t885; tll_ptr Char_t886; tll_ptr Char_t887;
  tll_ptr Char_t888; tll_ptr Char_t889; tll_ptr Char_t890; tll_ptr Char_t891;
  tll_ptr Char_t892; tll_ptr Char_t931; tll_ptr Char_t932; tll_ptr Char_t933;
  tll_ptr Char_t934; tll_ptr Char_t935; tll_ptr Char_t936; tll_ptr Char_t937;
  tll_ptr Char_t938; tll_ptr Char_t939; tll_ptr Char_t951; tll_ptr Char_t952;
  tll_ptr Char_t953; tll_ptr Char_t954; tll_ptr Char_t955; tll_ptr Char_t956;
  tll_ptr Char_t957; tll_ptr Char_t958; tll_ptr EmptyString_t845;
  tll_ptr EmptyString_t893; tll_ptr EmptyString_t940;
  tll_ptr EmptyString_t959; tll_ptr String_t846; tll_ptr String_t847;
  tll_ptr String_t848; tll_ptr String_t849; tll_ptr String_t850;
  tll_ptr String_t851; tll_ptr String_t852; tll_ptr String_t853;
  tll_ptr String_t854; tll_ptr String_t855; tll_ptr String_t856;
  tll_ptr String_t857; tll_ptr String_t894; tll_ptr String_t895;
  tll_ptr String_t896; tll_ptr String_t897; tll_ptr String_t898;
  tll_ptr String_t899; tll_ptr String_t900; tll_ptr String_t901;
  tll_ptr String_t902; tll_ptr String_t903; tll_ptr String_t904;
  tll_ptr String_t905; tll_ptr String_t906; tll_ptr String_t907;
  tll_ptr String_t908; tll_ptr String_t909; tll_ptr String_t910;
  tll_ptr String_t911; tll_ptr String_t912; tll_ptr String_t913;
  tll_ptr String_t914; tll_ptr String_t915; tll_ptr String_t916;
  tll_ptr String_t917; tll_ptr String_t918; tll_ptr String_t919;
  tll_ptr String_t920; tll_ptr String_t921; tll_ptr String_t922;
  tll_ptr String_t923; tll_ptr String_t924; tll_ptr String_t925;
  tll_ptr String_t926; tll_ptr String_t941; tll_ptr String_t942;
  tll_ptr String_t943; tll_ptr String_t944; tll_ptr String_t945;
  tll_ptr String_t946; tll_ptr String_t947; tll_ptr String_t948;
  tll_ptr String_t949; tll_ptr String_t960; tll_ptr String_t961;
  tll_ptr String_t962; tll_ptr String_t963; tll_ptr String_t964;
  tll_ptr String_t965; tll_ptr String_t966; tll_ptr String_t967;
  tll_ptr __v142013; tll_ptr __v142016; tll_ptr __v142017; tll_ptr __v142018;
  tll_ptr ans_v142011; tll_ptr app_ret_t858; tll_ptr app_ret_t927;
  tll_ptr app_ret_t968; tll_ptr app_ret_t970; tll_ptr c_v142012;
  tll_ptr c_v142015; tll_ptr call_ret_t832; tll_ptr call_ret_t859;
  tll_ptr call_ret_t928; tll_ptr call_ret_t929; tll_ptr call_ret_t930;
  tll_ptr call_ret_t950; tll_ptr call_ret_t969; tll_ptr pair_struct_t828;
  tll_ptr recv_msg_t830; tll_ptr repeat_v142014; tll_ptr switch_ret_t829;
  tll_ptr switch_ret_t831;
  instr_struct(&pair_struct_t828, 0, 2, 0, env[0]);
  switch(((tll_node)pair_struct_t828)->tag) {
    case 0:
      ans_v142011 = ((tll_node)pair_struct_t828)->data[0];
      c_v142012 = ((tll_node)pair_struct_t828)->data[1];
      instr_free_struct(pair_struct_t828);
      instr_recv(&recv_msg_t830, c_v142012);
      __v142013 = recv_msg_t830;
      switch(((tll_node)__v142013)->tag) {
        case 0:
          repeat_v142014 = ((tll_node)__v142013)->data[0];
          c_v142015 = ((tll_node)__v142013)->data[1];
          instr_free_struct(__v142013);
          instr_struct(&Char_t833, 5, 1, (tll_ptr)87);
          instr_struct(&Char_t834, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t835, 5, 1, (tll_ptr)114);
          instr_struct(&Char_t836, 5, 1, (tll_ptr)100);
          instr_struct(&Char_t837, 5, 1, (tll_ptr)108);
          instr_struct(&Char_t838, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t839, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t840, 5, 1, (tll_ptr)71);
          instr_struct(&Char_t841, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t842, 5, 1, (tll_ptr)109);
          instr_struct(&Char_t843, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t844, 5, 1, (tll_ptr)10);
          instr_struct(&EmptyString_t845, 6, 0);
          instr_struct(&String_t846, 7, 2, Char_t844, EmptyString_t845);
          instr_struct(&String_t847, 7, 2, Char_t843, String_t846);
          instr_struct(&String_t848, 7, 2, Char_t842, String_t847);
          instr_struct(&String_t849, 7, 2, Char_t841, String_t848);
          instr_struct(&String_t850, 7, 2, Char_t840, String_t849);
          instr_struct(&String_t851, 7, 2, Char_t839, String_t850);
          instr_struct(&String_t852, 7, 2, Char_t838, String_t851);
          instr_struct(&String_t853, 7, 2, Char_t837, String_t852);
          instr_struct(&String_t854, 7, 2, Char_t836, String_t853);
          instr_struct(&String_t855, 7, 2, Char_t835, String_t854);
          instr_struct(&String_t856, 7, 2, Char_t834, String_t855);
          instr_struct(&String_t857, 7, 2, Char_t833, String_t856);
          call_ret_t832 = print_i34(String_t857);
          instr_app(&app_ret_t858, call_ret_t832, 0);
          instr_free_clo(call_ret_t832);
          __v142016 = app_ret_t858;
          instr_struct(&Char_t860, 5, 1, (tll_ptr)80);
          instr_struct(&Char_t861, 5, 1, (tll_ptr)108);
          instr_struct(&Char_t862, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t863, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t864, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t865, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t866, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t867, 5, 1, (tll_ptr)103);
          instr_struct(&Char_t868, 5, 1, (tll_ptr)117);
          instr_struct(&Char_t869, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t870, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t871, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t872, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t873, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t874, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t875, 5, 1, (tll_ptr)119);
          instr_struct(&Char_t876, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t877, 5, 1, (tll_ptr)114);
          instr_struct(&Char_t878, 5, 1, (tll_ptr)100);
          instr_struct(&Char_t879, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t880, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t881, 5, 1, (tll_ptr)102);
          instr_struct(&Char_t882, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t883, 5, 1, (tll_ptr)108);
          instr_struct(&Char_t884, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t885, 5, 1, (tll_ptr)110);
          instr_struct(&Char_t886, 5, 1, (tll_ptr)103);
          instr_struct(&Char_t887, 5, 1, (tll_ptr)116);
          instr_struct(&Char_t888, 5, 1, (tll_ptr)104);
          instr_struct(&Char_t889, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t890, 5, 1, (tll_ptr)53);
          instr_struct(&Char_t891, 5, 1, (tll_ptr)46);
          instr_struct(&Char_t892, 5, 1, (tll_ptr)10);
          instr_struct(&EmptyString_t893, 6, 0);
          instr_struct(&String_t894, 7, 2, Char_t892, EmptyString_t893);
          instr_struct(&String_t895, 7, 2, Char_t891, String_t894);
          instr_struct(&String_t896, 7, 2, Char_t890, String_t895);
          instr_struct(&String_t897, 7, 2, Char_t889, String_t896);
          instr_struct(&String_t898, 7, 2, Char_t888, String_t897);
          instr_struct(&String_t899, 7, 2, Char_t887, String_t898);
          instr_struct(&String_t900, 7, 2, Char_t886, String_t899);
          instr_struct(&String_t901, 7, 2, Char_t885, String_t900);
          instr_struct(&String_t902, 7, 2, Char_t884, String_t901);
          instr_struct(&String_t903, 7, 2, Char_t883, String_t902);
          instr_struct(&String_t904, 7, 2, Char_t882, String_t903);
          instr_struct(&String_t905, 7, 2, Char_t881, String_t904);
          instr_struct(&String_t906, 7, 2, Char_t880, String_t905);
          instr_struct(&String_t907, 7, 2, Char_t879, String_t906);
          instr_struct(&String_t908, 7, 2, Char_t878, String_t907);
          instr_struct(&String_t909, 7, 2, Char_t877, String_t908);
          instr_struct(&String_t910, 7, 2, Char_t876, String_t909);
          instr_struct(&String_t911, 7, 2, Char_t875, String_t910);
          instr_struct(&String_t912, 7, 2, Char_t874, String_t911);
          instr_struct(&String_t913, 7, 2, Char_t873, String_t912);
          instr_struct(&String_t914, 7, 2, Char_t872, String_t913);
          instr_struct(&String_t915, 7, 2, Char_t871, String_t914);
          instr_struct(&String_t916, 7, 2, Char_t870, String_t915);
          instr_struct(&String_t917, 7, 2, Char_t869, String_t916);
          instr_struct(&String_t918, 7, 2, Char_t868, String_t917);
          instr_struct(&String_t919, 7, 2, Char_t867, String_t918);
          instr_struct(&String_t920, 7, 2, Char_t866, String_t919);
          instr_struct(&String_t921, 7, 2, Char_t865, String_t920);
          instr_struct(&String_t922, 7, 2, Char_t864, String_t921);
          instr_struct(&String_t923, 7, 2, Char_t863, String_t922);
          instr_struct(&String_t924, 7, 2, Char_t862, String_t923);
          instr_struct(&String_t925, 7, 2, Char_t861, String_t924);
          instr_struct(&String_t926, 7, 2, Char_t860, String_t925);
          call_ret_t859 = print_i34(String_t926);
          instr_app(&app_ret_t927, call_ret_t859, 0);
          instr_free_clo(call_ret_t859);
          __v142017 = app_ret_t927;
          instr_struct(&Char_t931, 5, 1, (tll_ptr)89);
          instr_struct(&Char_t932, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t933, 5, 1, (tll_ptr)117);
          instr_struct(&Char_t934, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t935, 5, 1, (tll_ptr)104);
          instr_struct(&Char_t936, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t937, 5, 1, (tll_ptr)118);
          instr_struct(&Char_t938, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t939, 5, 1, (tll_ptr)32);
          instr_struct(&EmptyString_t940, 6, 0);
          instr_struct(&String_t941, 7, 2, Char_t939, EmptyString_t940);
          instr_struct(&String_t942, 7, 2, Char_t938, String_t941);
          instr_struct(&String_t943, 7, 2, Char_t937, String_t942);
          instr_struct(&String_t944, 7, 2, Char_t936, String_t943);
          instr_struct(&String_t945, 7, 2, Char_t935, String_t944);
          instr_struct(&String_t946, 7, 2, Char_t934, String_t945);
          instr_struct(&String_t947, 7, 2, Char_t933, String_t946);
          instr_struct(&String_t948, 7, 2, Char_t932, String_t947);
          instr_struct(&String_t949, 7, 2, Char_t931, String_t948);
          call_ret_t950 = string_of_nat_i39(repeat_v142014);
          call_ret_t930 = cats_i20(String_t949, call_ret_t950);
          instr_struct(&Char_t951, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t952, 5, 1, (tll_ptr)116);
          instr_struct(&Char_t953, 5, 1, (tll_ptr)114);
          instr_struct(&Char_t954, 5, 1, (tll_ptr)105);
          instr_struct(&Char_t955, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t956, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t957, 5, 1, (tll_ptr)46);
          instr_struct(&Char_t958, 5, 1, (tll_ptr)10);
          instr_struct(&EmptyString_t959, 6, 0);
          instr_struct(&String_t960, 7, 2, Char_t958, EmptyString_t959);
          instr_struct(&String_t961, 7, 2, Char_t957, String_t960);
          instr_struct(&String_t962, 7, 2, Char_t956, String_t961);
          instr_struct(&String_t963, 7, 2, Char_t955, String_t962);
          instr_struct(&String_t964, 7, 2, Char_t954, String_t963);
          instr_struct(&String_t965, 7, 2, Char_t953, String_t964);
          instr_struct(&String_t966, 7, 2, Char_t952, String_t965);
          instr_struct(&String_t967, 7, 2, Char_t951, String_t966);
          call_ret_t929 = cats_i20(call_ret_t930, String_t967);
          call_ret_t928 = print_i34(call_ret_t929);
          instr_app(&app_ret_t968, call_ret_t928, 0);
          instr_free_clo(call_ret_t928);
          __v142018 = app_ret_t968;
          call_ret_t969 = player_loop_i60(0, repeat_v142014, c_v142015);
          instr_app(&app_ret_t970, call_ret_t969, 0);
          instr_free_clo(call_ret_t969);
          switch_ret_t831 = app_ret_t970;
          break;
      }
      switch_ret_t829 = switch_ret_t831;
      break;
  }
  return switch_ret_t829;
}

tll_ptr player_i61(tll_ptr c_v142001) {
  tll_ptr lam_clo_t972;
  instr_clo(&lam_clo_t972, &lam_fun_t971, 1, c_v142001);
  return lam_clo_t972;
}

tll_ptr lam_fun_t974(tll_ptr c_v142019, tll_env env) {
  tll_ptr call_ret_t973;
  call_ret_t973 = player_i61(c_v142019);
  return call_ret_t973;
}

tll_ptr lam_fun_t980(tll_ptr __v142055, tll_env env) {
  
  
  return 0;
}

tll_ptr lam_fun_t982(tll_ptr c_v142053, tll_env env) {
  tll_ptr lam_clo_t981;
  instr_clo(&lam_clo_t981, &lam_fun_t980, 0);
  return lam_clo_t981;
}

tll_ptr lam_fun_t989(tll_ptr __v142060, tll_env env) {
  tll_ptr add_ret_t987; tll_ptr app_ret_t988; tll_ptr c_v142063;
  tll_ptr call_ret_t984; tll_ptr call_ret_t986; tll_ptr send_ch_t985;
  tll_ptr x_v142064;
  call_ret_t984 = word_diff_i51(env[3], env[1]);
  x_v142064 = call_ret_t984;
  instr_send(&send_ch_t985, env[0], x_v142064);
  c_v142063 = send_ch_t985;
  add_ret_t987 = env[2] - 1;
  call_ret_t986 = server_loop_i62(env[3], add_ret_t987, c_v142063);
  instr_app(&app_ret_t988, call_ret_t986, 0);
  instr_free_clo(call_ret_t986);
  return app_ret_t988;
}

tll_ptr lam_fun_t991(tll_ptr c_v142056, tll_env env) {
  tll_ptr lam_clo_t990;
  instr_clo(&lam_clo_t990, &lam_fun_t989, 4,
            c_v142056, env[0], env[1], env[2]);
  return lam_clo_t990;
}

tll_ptr lam_fun_t996(tll_ptr __v142036, tll_env env) {
  tll_ptr __v142048; tll_ptr app_ret_t994; tll_ptr app_ret_t995;
  tll_ptr b_v142051; tll_ptr c_v142050; tll_ptr c_v142052;
  tll_ptr call_ret_t978; tll_ptr guess_v142049; tll_ptr ifte_ret_t993;
  tll_ptr lam_clo_t983; tll_ptr lam_clo_t992; tll_ptr recv_msg_t976;
  tll_ptr send_ch_t979; tll_ptr switch_ret_t977;
  instr_recv(&recv_msg_t976, env[0]);
  __v142048 = recv_msg_t976;
  switch(((tll_node)__v142048)->tag) {
    case 0:
      guess_v142049 = ((tll_node)__v142048)->data[0];
      c_v142050 = ((tll_node)__v142048)->data[1];
      instr_free_struct(__v142048);
      call_ret_t978 = eqw_i52(env[2], guess_v142049);
      b_v142051 = call_ret_t978;
      instr_send(&send_ch_t979, c_v142050, b_v142051);
      c_v142052 = send_ch_t979;
      if (b_v142051) {
        instr_clo(&lam_clo_t983, &lam_fun_t982, 0);
        ifte_ret_t993 = lam_clo_t983;
      }
      else {
        instr_clo(&lam_clo_t992, &lam_fun_t991, 3,
                  guess_v142049, env[1], env[2]);
        ifte_ret_t993 = lam_clo_t992;
      }
      instr_app(&app_ret_t994, ifte_ret_t993, c_v142052);
      instr_free_clo(ifte_ret_t993);
      instr_app(&app_ret_t995, app_ret_t994, 0);
      instr_free_clo(app_ret_t994);
      switch_ret_t977 = app_ret_t995;
      break;
  }
  return switch_ret_t977;
}

tll_ptr lam_fun_t998(tll_ptr c_v142023, tll_env env) {
  tll_ptr lam_clo_t997;
  instr_clo(&lam_clo_t997, &lam_fun_t996, 3, c_v142023, env[0], env[1]);
  return lam_clo_t997;
}

tll_ptr lam_fun_t1001(tll_ptr __v142068, tll_env env) {
  tll_ptr c_v142070; tll_ptr send_ch_t1000;
  instr_send(&send_ch_t1000, env[0], env[1]);
  c_v142070 = send_ch_t1000;
  return 0;
}

tll_ptr lam_fun_t1003(tll_ptr c_v142065, tll_env env) {
  tll_ptr lam_clo_t1002;
  instr_clo(&lam_clo_t1002, &lam_fun_t1001, 2, c_v142065, env[0]);
  return lam_clo_t1002;
}

tll_ptr server_loop_i62(tll_ptr ans_v142020, tll_ptr repeat_v142021, tll_ptr c_v142022) {
  tll_ptr app_ret_t1006; tll_ptr ifte_ret_t1005; tll_ptr lam_clo_t1004;
  tll_ptr lam_clo_t999;
  if (repeat_v142021) {
    instr_clo(&lam_clo_t999, &lam_fun_t998, 2, repeat_v142021, ans_v142020);
    ifte_ret_t1005 = lam_clo_t999;
  }
  else {
    instr_clo(&lam_clo_t1004, &lam_fun_t1003, 1, ans_v142020);
    ifte_ret_t1005 = lam_clo_t1004;
  }
  instr_app(&app_ret_t1006, ifte_ret_t1005, c_v142022);
  return app_ret_t1006;
}

tll_ptr lam_fun_t1008(tll_ptr c_v142076, tll_env env) {
  tll_ptr call_ret_t1007;
  call_ret_t1007 = server_loop_i62(env[1], env[0], c_v142076);
  return call_ret_t1007;
}

tll_ptr lam_fun_t1010(tll_ptr repeat_v142074, tll_env env) {
  tll_ptr lam_clo_t1009;
  instr_clo(&lam_clo_t1009, &lam_fun_t1008, 2, repeat_v142074, env[0]);
  return lam_clo_t1009;
}

tll_ptr lam_fun_t1012(tll_ptr ans_v142071, tll_env env) {
  tll_ptr lam_clo_t1011;
  instr_clo(&lam_clo_t1011, &lam_fun_t1010, 1, ans_v142071);
  return lam_clo_t1011;
}

tll_ptr lam_fun_t1029(tll_ptr __v142078, tll_env env) {
  tll_ptr Char_t1016; tll_ptr Char_t1017; tll_ptr Char_t1018;
  tll_ptr Char_t1019; tll_ptr Char_t1020; tll_ptr EmptyString_t1021;
  tll_ptr String_t1022; tll_ptr String_t1023; tll_ptr String_t1024;
  tll_ptr String_t1025; tll_ptr String_t1026; tll_ptr Word_t1027;
  tll_ptr app_ret_t1028; tll_ptr c_v142080; tll_ptr call_ret_t1015;
  tll_ptr send_ch_t1014;
  instr_send(&send_ch_t1014, env[0], (tll_ptr)5);
  c_v142080 = send_ch_t1014;
  instr_struct(&Char_t1016, 5, 1, (tll_ptr)119);
  instr_struct(&Char_t1017, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t1018, 5, 1, (tll_ptr)114);
  instr_struct(&Char_t1019, 5, 1, (tll_ptr)108);
  instr_struct(&Char_t1020, 5, 1, (tll_ptr)100);
  instr_struct(&EmptyString_t1021, 6, 0);
  instr_struct(&String_t1022, 7, 2, Char_t1020, EmptyString_t1021);
  instr_struct(&String_t1023, 7, 2, Char_t1019, String_t1022);
  instr_struct(&String_t1024, 7, 2, Char_t1018, String_t1023);
  instr_struct(&String_t1025, 7, 2, Char_t1017, String_t1024);
  instr_struct(&String_t1026, 7, 2, Char_t1016, String_t1025);
  instr_struct(&Word_t1027, 12, 2, String_t1026, 0);
  call_ret_t1015 = server_loop_i62(Word_t1027, (tll_ptr)5, c_v142080);
  instr_app(&app_ret_t1028, call_ret_t1015, 0);
  instr_free_clo(call_ret_t1015);
  return app_ret_t1028;
}

tll_ptr server_i63(tll_ptr c_v142077) {
  tll_ptr lam_clo_t1030;
  instr_clo(&lam_clo_t1030, &lam_fun_t1029, 1, c_v142077);
  return lam_clo_t1030;
}

tll_ptr lam_fun_t1032(tll_ptr c_v142081, tll_env env) {
  tll_ptr call_ret_t1031;
  call_ret_t1031 = server_i63(c_v142081);
  return call_ret_t1031;
}

tll_ptr fork_fun_t1036(tll_env env) {
  tll_ptr app_ret_t1035; tll_ptr call_ret_t1034; tll_ptr fork_ret_t1038;
  call_ret_t1034 = server_i63(env[0]);
  instr_app(&app_ret_t1035, call_ret_t1034, 0);
  instr_free_clo(call_ret_t1034);
  fork_ret_t1038 = app_ret_t1035;
  instr_free_thread(env);
  return fork_ret_t1038;
}

tll_ptr fork_fun_t1044(tll_env env) {
  tll_ptr __v142091; tll_ptr __v142094; tll_ptr app_ret_t1042;
  tll_ptr c0_v142093; tll_ptr c0_v142095; tll_ptr c_v142092;
  tll_ptr call_ret_t1041; tll_ptr fork_ret_t1046; tll_ptr recv_msg_t1039;
  tll_ptr send_ch_t1043; tll_ptr switch_ret_t1040;
  instr_recv(&recv_msg_t1039, env[0]);
  __v142091 = recv_msg_t1039;
  switch(((tll_node)__v142091)->tag) {
    case 0:
      c_v142092 = ((tll_node)__v142091)->data[0];
      c0_v142093 = ((tll_node)__v142091)->data[1];
      instr_free_struct(__v142091);
      call_ret_t1041 = player_i61(c_v142092);
      instr_app(&app_ret_t1042, call_ret_t1041, 0);
      instr_free_clo(call_ret_t1041);
      __v142094 = app_ret_t1042;
      instr_send(&send_ch_t1043, c0_v142093, 0);
      c0_v142095 = send_ch_t1043;
      switch_ret_t1040 = 0;
      break;
  }
  fork_ret_t1046 = switch_ret_t1040;
  instr_free_thread(env);
  return fork_ret_t1046;
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
  tll_ptr String_t363; tll_ptr String_t366; tll_ptr __v142097;
  tll_ptr __v142098; tll_ptr c0_v142084; tll_ptr c0_v142096;
  tll_ptr c0_v142099; tll_ptr c_v142082; tll_ptr close_tmp_t1050;
  tll_ptr consUU_t368; tll_ptr consUU_t369; tll_ptr consUU_t370;
  tll_ptr consUU_t371; tll_ptr consUU_t372; tll_ptr consUU_t373;
  tll_ptr consUU_t374; tll_ptr consUU_t375; tll_ptr consUU_t376;
  tll_ptr consUU_t377; tll_ptr fork_ch_t1037; tll_ptr fork_ch_t1045;
  tll_ptr lam_clo_t1013; tll_ptr lam_clo_t1033; tll_ptr lam_clo_t104;
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
  tll_ptr lam_clo_t467; tll_ptr lam_clo_t488; tll_ptr lam_clo_t497;
  tll_ptr lam_clo_t505; tll_ptr lam_clo_t52; tll_ptr lam_clo_t58;
  tll_ptr lam_clo_t6; tll_ptr lam_clo_t605; tll_ptr lam_clo_t72;
  tll_ptr lam_clo_t77; tll_ptr lam_clo_t827; tll_ptr lam_clo_t83;
  tll_ptr lam_clo_t92; tll_ptr lam_clo_t975; tll_ptr lam_clo_t98;
  tll_ptr nilUU_t367; tll_ptr recv_msg_t1048; tll_ptr send_ch_t1047;
  tll_ptr switch_ret_t1049;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i89 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i90 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i91 = lam_clo_t16;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  comparebclo_i92 = lam_clo_t28;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 0);
  ltenclo_i93 = lam_clo_t34;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 0);
  gtenclo_i94 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  ltnclo_i95 = lam_clo_t46;
  instr_clo(&lam_clo_t52, &lam_fun_t51, 0);
  gtnclo_i96 = lam_clo_t52;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  eqnclo_i97 = lam_clo_t58;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  comparenclo_i98 = lam_clo_t72;
  instr_clo(&lam_clo_t77, &lam_fun_t76, 0);
  predclo_i99 = lam_clo_t77;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i100 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i101 = lam_clo_t92;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  mulnclo_i102 = lam_clo_t98;
  instr_clo(&lam_clo_t104, &lam_fun_t103, 0);
  divnclo_i103 = lam_clo_t104;
  instr_clo(&lam_clo_t110, &lam_fun_t109, 0);
  modnclo_i104 = lam_clo_t110;
  instr_clo(&lam_clo_t118, &lam_fun_t117, 0);
  eqcclo_i105 = lam_clo_t118;
  instr_clo(&lam_clo_t126, &lam_fun_t125, 0);
  comparecclo_i106 = lam_clo_t126;
  instr_clo(&lam_clo_t134, &lam_fun_t133, 0);
  catsclo_i107 = lam_clo_t134;
  instr_clo(&lam_clo_t140, &lam_fun_t139, 0);
  strlenclo_i108 = lam_clo_t140;
  instr_clo(&lam_clo_t151, &lam_fun_t150, 0);
  eqsclo_i109 = lam_clo_t151;
  instr_clo(&lam_clo_t167, &lam_fun_t166, 0);
  comparesclo_i110 = lam_clo_t167;
  instr_clo(&lam_clo_t179, &lam_fun_t178, 0);
  and_thenUUUclo_i111 = lam_clo_t179;
  instr_clo(&lam_clo_t191, &lam_fun_t190, 0);
  and_thenUULclo_i112 = lam_clo_t191;
  instr_clo(&lam_clo_t203, &lam_fun_t202, 0);
  and_thenULUclo_i113 = lam_clo_t203;
  instr_clo(&lam_clo_t215, &lam_fun_t214, 0);
  and_thenULLclo_i114 = lam_clo_t215;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 0);
  and_thenLULclo_i115 = lam_clo_t227;
  instr_clo(&lam_clo_t239, &lam_fun_t238, 0);
  and_thenLLLclo_i116 = lam_clo_t239;
  instr_clo(&lam_clo_t252, &lam_fun_t251, 0);
  lenUUclo_i117 = lam_clo_t252;
  instr_clo(&lam_clo_t265, &lam_fun_t264, 0);
  lenULclo_i118 = lam_clo_t265;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 0);
  lenLLclo_i119 = lam_clo_t278;
  instr_clo(&lam_clo_t288, &lam_fun_t287, 0);
  appendUUclo_i120 = lam_clo_t288;
  instr_clo(&lam_clo_t298, &lam_fun_t297, 0);
  appendULclo_i121 = lam_clo_t298;
  instr_clo(&lam_clo_t308, &lam_fun_t307, 0);
  appendLLclo_i122 = lam_clo_t308;
  instr_clo(&lam_clo_t318, &lam_fun_t317, 0);
  readlineclo_i123 = lam_clo_t318;
  instr_clo(&lam_clo_t327, &lam_fun_t326, 0);
  printclo_i124 = lam_clo_t327;
  instr_clo(&lam_clo_t336, &lam_fun_t335, 0);
  prerrclo_i125 = lam_clo_t336;
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
  get_atclo_i126 = lam_clo_t391;
  instr_clo(&lam_clo_t396, &lam_fun_t395, 0);
  string_of_digitclo_i127 = lam_clo_t396;
  instr_clo(&lam_clo_t406, &lam_fun_t405, 0);
  string_of_natclo_i128 = lam_clo_t406;
  instr_clo(&lam_clo_t450, &lam_fun_t449, 0);
  digit_of_charclo_i129 = lam_clo_t450;
  instr_clo(&lam_clo_t463, &lam_fun_t462, 0);
  nat_of_string_loopclo_i130 = lam_clo_t463;
  instr_clo(&lam_clo_t467, &lam_fun_t466, 0);
  nat_of_stringclo_i131 = lam_clo_t467;
  instr_clo(&lam_clo_t488, &lam_fun_t487, 0);
  string_diffclo_i132 = lam_clo_t488;
  instr_clo(&lam_clo_t497, &lam_fun_t496, 0);
  word_diffclo_i133 = lam_clo_t497;
  instr_clo(&lam_clo_t505, &lam_fun_t504, 0);
  eqwclo_i134 = lam_clo_t505;
  instr_clo(&lam_clo_t605, &lam_fun_t604, 0);
  read_wordclo_i135 = lam_clo_t605;
  instr_clo(&lam_clo_t827, &lam_fun_t826, 0);
  player_loopclo_i136 = lam_clo_t827;
  instr_clo(&lam_clo_t975, &lam_fun_t974, 0);
  playerclo_i137 = lam_clo_t975;
  instr_clo(&lam_clo_t1013, &lam_fun_t1012, 0);
  server_loopclo_i138 = lam_clo_t1013;
  instr_clo(&lam_clo_t1033, &lam_fun_t1032, 0);
  serverclo_i139 = lam_clo_t1033;
  instr_fork(&fork_ch_t1037, &fork_fun_t1036, 0);
  c_v142082 = fork_ch_t1037;
  instr_fork(&fork_ch_t1045, &fork_fun_t1044, 0);
  c0_v142084 = fork_ch_t1045;
  instr_send(&send_ch_t1047, c0_v142084, c_v142082);
  c0_v142096 = send_ch_t1047;
  instr_recv(&recv_msg_t1048, c0_v142096);
  __v142097 = recv_msg_t1048;
  switch(((tll_node)__v142097)->tag) {
    case 0:
      __v142098 = ((tll_node)__v142097)->data[0];
      c0_v142099 = ((tll_node)__v142097)->data[1];
      instr_free_struct(__v142097);
      instr_close(&close_tmp_t1050, c0_v142099);
      switch_ret_t1049 = close_tmp_t1050;
      break;
  }
  return 0;
}

