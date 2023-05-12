#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v28378, tll_ptr b2_v28379);
tll_ptr orb_i2(tll_ptr b1_v28383, tll_ptr b2_v28384);
tll_ptr notb_i3(tll_ptr b_v28388);
tll_ptr compareb_i4(tll_ptr b1_v28390, tll_ptr b2_v28391);
tll_ptr lten_i5(tll_ptr x_v28395, tll_ptr y_v28396);
tll_ptr gten_i6(tll_ptr x_v28400, tll_ptr y_v28401);
tll_ptr ltn_i7(tll_ptr x_v28405, tll_ptr y_v28406);
tll_ptr gtn_i8(tll_ptr x_v28410, tll_ptr y_v28411);
tll_ptr eqn_i9(tll_ptr x_v28415, tll_ptr y_v28416);
tll_ptr comparen_i10(tll_ptr n1_v28420, tll_ptr n2_v28421);
tll_ptr pred_i11(tll_ptr x_v28425);
tll_ptr addn_i12(tll_ptr x_v28427, tll_ptr y_v28428);
tll_ptr subn_i13(tll_ptr x_v28432, tll_ptr y_v28433);
tll_ptr muln_i14(tll_ptr x_v28437, tll_ptr y_v28438);
tll_ptr divn_i15(tll_ptr x_v28442, tll_ptr y_v28443);
tll_ptr modn_i16(tll_ptr x_v28447, tll_ptr y_v28448);
tll_ptr eqc_i17(tll_ptr c1_v28452, tll_ptr c2_v28453);
tll_ptr comparec_i18(tll_ptr c1_v28459, tll_ptr c2_v28460);
tll_ptr cats_i19(tll_ptr s1_v28466, tll_ptr s2_v28467);
tll_ptr strlen_i20(tll_ptr s_v28473);
tll_ptr eqs_i21(tll_ptr s1_v28477, tll_ptr s2_v28478);
tll_ptr compares_i22(tll_ptr s1_v28488, tll_ptr s2_v28489);
tll_ptr lenUU_i56(tll_ptr A_v28499, tll_ptr xs_v28500);
tll_ptr lenUL_i55(tll_ptr A_v28508, tll_ptr xs_v28509);
tll_ptr lenLL_i53(tll_ptr A_v28517, tll_ptr xs_v28518);
tll_ptr appendUU_i60(tll_ptr A_v28526, tll_ptr xs_v28527, tll_ptr ys_v28528);
tll_ptr appendUL_i59(tll_ptr A_v28537, tll_ptr xs_v28538, tll_ptr ys_v28539);
tll_ptr appendLL_i57(tll_ptr A_v28548, tll_ptr xs_v28549, tll_ptr ys_v28550);
tll_ptr readline_i31(tll_ptr __v28559);
tll_ptr print_i32(tll_ptr s_v28574);
tll_ptr prerr_i33(tll_ptr s_v28585);
tll_ptr get_at_i35(tll_ptr A_v28596, tll_ptr n_v28597, tll_ptr xs_v28598, tll_ptr a_v28599);
tll_ptr string_of_digit_i36(tll_ptr n_v28614);
tll_ptr string_of_nat_i37(tll_ptr n_v28616);
tll_ptr digit_of_char_i38(tll_ptr c_v28620);
tll_ptr nat_of_string_loop_i39(tll_ptr s_v28622, tll_ptr acc_v28623);
tll_ptr nat_of_string_i40(tll_ptr s_v28630);
tll_ptr read_nat_i47(tll_ptr __v28632);
tll_ptr player_loop_i48(tll_ptr ans_v28641, tll_ptr repeat_v28642, tll_ptr c_v28643);
tll_ptr player_i49(tll_ptr c_v28689);
tll_ptr server_loop_i50(tll_ptr ans_v28726, tll_ptr repeat_v28727, tll_ptr c_v28728);
tll_ptr server_i51(tll_ptr c_v28756);

tll_ptr addnclo_i72;
tll_ptr andbclo_i61;
tll_ptr appendLLclo_i88;
tll_ptr appendULclo_i87;
tll_ptr appendUUclo_i86;
tll_ptr catsclo_i79;
tll_ptr comparebclo_i64;
tll_ptr comparecclo_i78;
tll_ptr comparenclo_i70;
tll_ptr comparesclo_i82;
tll_ptr digit_of_charclo_i95;
tll_ptr digits_i34;
tll_ptr divnclo_i75;
tll_ptr eqcclo_i77;
tll_ptr eqnclo_i69;
tll_ptr eqsclo_i81;
tll_ptr get_atclo_i92;
tll_ptr gtenclo_i66;
tll_ptr gtnclo_i68;
tll_ptr lenLLclo_i85;
tll_ptr lenULclo_i84;
tll_ptr lenUUclo_i83;
tll_ptr ltenclo_i65;
tll_ptr ltnclo_i67;
tll_ptr modnclo_i76;
tll_ptr mulnclo_i74;
tll_ptr nat_of_string_loopclo_i96;
tll_ptr nat_of_stringclo_i97;
tll_ptr notbclo_i63;
tll_ptr orbclo_i62;
tll_ptr player_loopclo_i99;
tll_ptr playerclo_i100;
tll_ptr predclo_i71;
tll_ptr prerrclo_i91;
tll_ptr printclo_i90;
tll_ptr read_natclo_i98;
tll_ptr readlineclo_i89;
tll_ptr server_loopclo_i101;
tll_ptr serverclo_i102;
tll_ptr string_of_digitclo_i93;
tll_ptr string_of_natclo_i94;
tll_ptr strlenclo_i80;
tll_ptr subnclo_i73;

tll_ptr andb_i1(tll_ptr b1_v28378, tll_ptr b2_v28379) {
  tll_ptr ifte_ret_t1;
  if (b1_v28378) {
    ifte_ret_t1 = b2_v28379;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v28382, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v28382);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v28380, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v28380);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v28383, tll_ptr b2_v28384) {
  tll_ptr ifte_ret_t7;
  if (b1_v28383) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v28384;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v28387, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v28387);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v28385, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v28385);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v28388) {
  tll_ptr ifte_ret_t13;
  if (b_v28388) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v28389, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v28389);
  return call_ret_t14;
}

tll_ptr compareb_i4(tll_ptr b1_v28390, tll_ptr b2_v28391) {
  tll_ptr EQ_t17; tll_ptr EQ_t21; tll_ptr GT_t18; tll_ptr LT_t20;
  tll_ptr ifte_ret_t19; tll_ptr ifte_ret_t22; tll_ptr ifte_ret_t23;
  if (b1_v28390) {
    if (b2_v28391) {
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
    if (b2_v28391) {
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

tll_ptr lam_fun_t25(tll_ptr b2_v28394, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = compareb_i4(env[0], b2_v28394);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr b1_v28392, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, b1_v28392);
  return lam_clo_t26;
}

tll_ptr lten_i5(tll_ptr x_v28395, tll_ptr y_v28396) {
  tll_ptr lten_ret_t29;
  instr_lten(&lten_ret_t29, x_v28395, y_v28396);
  return lten_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v28399, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = lten_i5(env[0], y_v28399);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v28397, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v28397);
  return lam_clo_t32;
}

tll_ptr gten_i6(tll_ptr x_v28400, tll_ptr y_v28401) {
  tll_ptr gten_ret_t35;
  instr_gten(&gten_ret_t35, x_v28400, y_v28401);
  return gten_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v28404, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = gten_i6(env[0], y_v28404);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v28402, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v28402);
  return lam_clo_t38;
}

tll_ptr ltn_i7(tll_ptr x_v28405, tll_ptr y_v28406) {
  tll_ptr ltn_ret_t41;
  instr_ltn(&ltn_ret_t41, x_v28405, y_v28406);
  return ltn_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v28409, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = ltn_i7(env[0], y_v28409);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v28407, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v28407);
  return lam_clo_t44;
}

tll_ptr gtn_i8(tll_ptr x_v28410, tll_ptr y_v28411) {
  tll_ptr gtn_ret_t47;
  instr_gtn(&gtn_ret_t47, x_v28410, y_v28411);
  return gtn_ret_t47;
}

tll_ptr lam_fun_t49(tll_ptr y_v28414, tll_env env) {
  tll_ptr call_ret_t48;
  call_ret_t48 = gtn_i8(env[0], y_v28414);
  return call_ret_t48;
}

tll_ptr lam_fun_t51(tll_ptr x_v28412, tll_env env) {
  tll_ptr lam_clo_t50;
  instr_clo(&lam_clo_t50, &lam_fun_t49, 1, x_v28412);
  return lam_clo_t50;
}

tll_ptr eqn_i9(tll_ptr x_v28415, tll_ptr y_v28416) {
  tll_ptr eqn_ret_t53;
  instr_eqn(&eqn_ret_t53, x_v28415, y_v28416);
  return eqn_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v28419, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = eqn_i9(env[0], y_v28419);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v28417, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v28417);
  return lam_clo_t56;
}

tll_ptr comparen_i10(tll_ptr n1_v28420, tll_ptr n2_v28421) {
  tll_ptr EQ_t65; tll_ptr GT_t62; tll_ptr LT_t64; tll_ptr add_ret_t60;
  tll_ptr add_ret_t61; tll_ptr call_ret_t59; tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t66; tll_ptr ifte_ret_t67;
  if (n1_v28420) {
    if (n2_v28421) {
      add_ret_t60 = n1_v28420 - 1;
      add_ret_t61 = n2_v28421 - 1;
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
    if (n2_v28421) {
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

tll_ptr lam_fun_t69(tll_ptr n2_v28424, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = comparen_i10(env[0], n2_v28424);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr n1_v28422, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, n1_v28422);
  return lam_clo_t70;
}

tll_ptr pred_i11(tll_ptr x_v28425) {
  tll_ptr add_ret_t73; tll_ptr ifte_ret_t74;
  if (x_v28425) {
    add_ret_t73 = x_v28425 - 1;
    ifte_ret_t74 = add_ret_t73;
  }
  else {
    ifte_ret_t74 = (tll_ptr)0;
  }
  return ifte_ret_t74;
}

tll_ptr lam_fun_t76(tll_ptr x_v28426, tll_env env) {
  tll_ptr call_ret_t75;
  call_ret_t75 = pred_i11(x_v28426);
  return call_ret_t75;
}

tll_ptr addn_i12(tll_ptr x_v28427, tll_ptr y_v28428) {
  tll_ptr addn_ret_t78;
  instr_addn(&addn_ret_t78, x_v28427, y_v28428);
  return addn_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v28431, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i12(env[0], y_v28431);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v28429, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v28429);
  return lam_clo_t81;
}

tll_ptr subn_i13(tll_ptr x_v28432, tll_ptr y_v28433) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v28433) {
    call_ret_t85 = pred_i11(x_v28432);
    add_ret_t86 = y_v28433 - 1;
    call_ret_t84 = subn_i13(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v28432;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v28436, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i13(env[0], y_v28436);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v28434, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v28434);
  return lam_clo_t90;
}

tll_ptr muln_i14(tll_ptr x_v28437, tll_ptr y_v28438) {
  tll_ptr muln_ret_t93;
  instr_muln(&muln_ret_t93, x_v28437, y_v28438);
  return muln_ret_t93;
}

tll_ptr lam_fun_t95(tll_ptr y_v28441, tll_env env) {
  tll_ptr call_ret_t94;
  call_ret_t94 = muln_i14(env[0], y_v28441);
  return call_ret_t94;
}

tll_ptr lam_fun_t97(tll_ptr x_v28439, tll_env env) {
  tll_ptr lam_clo_t96;
  instr_clo(&lam_clo_t96, &lam_fun_t95, 1, x_v28439);
  return lam_clo_t96;
}

tll_ptr divn_i15(tll_ptr x_v28442, tll_ptr y_v28443) {
  tll_ptr divn_ret_t99;
  instr_divn(&divn_ret_t99, x_v28442, y_v28443);
  return divn_ret_t99;
}

tll_ptr lam_fun_t101(tll_ptr y_v28446, tll_env env) {
  tll_ptr call_ret_t100;
  call_ret_t100 = divn_i15(env[0], y_v28446);
  return call_ret_t100;
}

tll_ptr lam_fun_t103(tll_ptr x_v28444, tll_env env) {
  tll_ptr lam_clo_t102;
  instr_clo(&lam_clo_t102, &lam_fun_t101, 1, x_v28444);
  return lam_clo_t102;
}

tll_ptr modn_i16(tll_ptr x_v28447, tll_ptr y_v28448) {
  tll_ptr modn_ret_t105;
  instr_modn(&modn_ret_t105, x_v28447, y_v28448);
  return modn_ret_t105;
}

tll_ptr lam_fun_t107(tll_ptr y_v28451, tll_env env) {
  tll_ptr call_ret_t106;
  call_ret_t106 = modn_i16(env[0], y_v28451);
  return call_ret_t106;
}

tll_ptr lam_fun_t109(tll_ptr x_v28449, tll_env env) {
  tll_ptr lam_clo_t108;
  instr_clo(&lam_clo_t108, &lam_fun_t107, 1, x_v28449);
  return lam_clo_t108;
}

tll_ptr eqc_i17(tll_ptr c1_v28452, tll_ptr c2_v28453) {
  tll_ptr call_ret_t113; tll_ptr n1_v28454; tll_ptr n2_v28455;
  tll_ptr switch_ret_t111; tll_ptr switch_ret_t112;
  switch(((tll_node)c1_v28452)->tag) {
    case 4:
      n1_v28454 = ((tll_node)c1_v28452)->data[0];
      switch(((tll_node)c2_v28453)->tag) {
        case 4:
          n2_v28455 = ((tll_node)c2_v28453)->data[0];
          call_ret_t113 = eqn_i9(n1_v28454, n2_v28455);
          switch_ret_t112 = call_ret_t113;
          break;
      }
      switch_ret_t111 = switch_ret_t112;
      break;
  }
  return switch_ret_t111;
}

tll_ptr lam_fun_t115(tll_ptr c2_v28458, tll_env env) {
  tll_ptr call_ret_t114;
  call_ret_t114 = eqc_i17(env[0], c2_v28458);
  return call_ret_t114;
}

tll_ptr lam_fun_t117(tll_ptr c1_v28456, tll_env env) {
  tll_ptr lam_clo_t116;
  instr_clo(&lam_clo_t116, &lam_fun_t115, 1, c1_v28456);
  return lam_clo_t116;
}

tll_ptr comparec_i18(tll_ptr c1_v28459, tll_ptr c2_v28460) {
  tll_ptr call_ret_t121; tll_ptr n1_v28461; tll_ptr n2_v28462;
  tll_ptr switch_ret_t119; tll_ptr switch_ret_t120;
  switch(((tll_node)c1_v28459)->tag) {
    case 4:
      n1_v28461 = ((tll_node)c1_v28459)->data[0];
      switch(((tll_node)c2_v28460)->tag) {
        case 4:
          n2_v28462 = ((tll_node)c2_v28460)->data[0];
          call_ret_t121 = comparen_i10(n1_v28461, n2_v28462);
          switch_ret_t120 = call_ret_t121;
          break;
      }
      switch_ret_t119 = switch_ret_t120;
      break;
  }
  return switch_ret_t119;
}

tll_ptr lam_fun_t123(tll_ptr c2_v28465, tll_env env) {
  tll_ptr call_ret_t122;
  call_ret_t122 = comparec_i18(env[0], c2_v28465);
  return call_ret_t122;
}

tll_ptr lam_fun_t125(tll_ptr c1_v28463, tll_env env) {
  tll_ptr lam_clo_t124;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 1, c1_v28463);
  return lam_clo_t124;
}

tll_ptr cats_i19(tll_ptr s1_v28466, tll_ptr s2_v28467) {
  tll_ptr String_t129; tll_ptr c_v28468; tll_ptr call_ret_t128;
  tll_ptr s1_v28469; tll_ptr switch_ret_t127;
  switch(((tll_node)s1_v28466)->tag) {
    case 5:
      switch_ret_t127 = s2_v28467;
      break;
    case 6:
      c_v28468 = ((tll_node)s1_v28466)->data[0];
      s1_v28469 = ((tll_node)s1_v28466)->data[1];
      call_ret_t128 = cats_i19(s1_v28469, s2_v28467);
      instr_struct(&String_t129, 6, 2, c_v28468, call_ret_t128);
      switch_ret_t127 = String_t129;
      break;
  }
  return switch_ret_t127;
}

tll_ptr lam_fun_t131(tll_ptr s2_v28472, tll_env env) {
  tll_ptr call_ret_t130;
  call_ret_t130 = cats_i19(env[0], s2_v28472);
  return call_ret_t130;
}

tll_ptr lam_fun_t133(tll_ptr s1_v28470, tll_env env) {
  tll_ptr lam_clo_t132;
  instr_clo(&lam_clo_t132, &lam_fun_t131, 1, s1_v28470);
  return lam_clo_t132;
}

tll_ptr strlen_i20(tll_ptr s_v28473) {
  tll_ptr __v28474; tll_ptr add_ret_t137; tll_ptr call_ret_t136;
  tll_ptr s_v28475; tll_ptr switch_ret_t135;
  switch(((tll_node)s_v28473)->tag) {
    case 5:
      switch_ret_t135 = (tll_ptr)0;
      break;
    case 6:
      __v28474 = ((tll_node)s_v28473)->data[0];
      s_v28475 = ((tll_node)s_v28473)->data[1];
      call_ret_t136 = strlen_i20(s_v28475);
      add_ret_t137 = call_ret_t136 + 1;
      switch_ret_t135 = add_ret_t137;
      break;
  }
  return switch_ret_t135;
}

tll_ptr lam_fun_t139(tll_ptr s_v28476, tll_env env) {
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i20(s_v28476);
  return call_ret_t138;
}

tll_ptr eqs_i21(tll_ptr s1_v28477, tll_ptr s2_v28478) {
  tll_ptr __v28479; tll_ptr __v28480; tll_ptr c1_v28481; tll_ptr c2_v28483;
  tll_ptr call_ret_t144; tll_ptr call_ret_t145; tll_ptr call_ret_t146;
  tll_ptr s1_v28482; tll_ptr s2_v28484; tll_ptr switch_ret_t141;
  tll_ptr switch_ret_t142; tll_ptr switch_ret_t143;
  switch(((tll_node)s1_v28477)->tag) {
    case 5:
      switch(((tll_node)s2_v28478)->tag) {
        case 5:
          switch_ret_t142 = (tll_ptr)1;
          break;
        case 6:
          __v28479 = ((tll_node)s2_v28478)->data[0];
          __v28480 = ((tll_node)s2_v28478)->data[1];
          switch_ret_t142 = (tll_ptr)0;
          break;
      }
      switch_ret_t141 = switch_ret_t142;
      break;
    case 6:
      c1_v28481 = ((tll_node)s1_v28477)->data[0];
      s1_v28482 = ((tll_node)s1_v28477)->data[1];
      switch(((tll_node)s2_v28478)->tag) {
        case 5:
          switch_ret_t143 = (tll_ptr)0;
          break;
        case 6:
          c2_v28483 = ((tll_node)s2_v28478)->data[0];
          s2_v28484 = ((tll_node)s2_v28478)->data[1];
          call_ret_t145 = eqc_i17(c1_v28481, c2_v28483);
          call_ret_t146 = eqs_i21(s1_v28482, s2_v28484);
          call_ret_t144 = andb_i1(call_ret_t145, call_ret_t146);
          switch_ret_t143 = call_ret_t144;
          break;
      }
      switch_ret_t141 = switch_ret_t143;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t148(tll_ptr s2_v28487, tll_env env) {
  tll_ptr call_ret_t147;
  call_ret_t147 = eqs_i21(env[0], s2_v28487);
  return call_ret_t147;
}

tll_ptr lam_fun_t150(tll_ptr s1_v28485, tll_env env) {
  tll_ptr lam_clo_t149;
  instr_clo(&lam_clo_t149, &lam_fun_t148, 1, s1_v28485);
  return lam_clo_t149;
}

tll_ptr compares_i22(tll_ptr s1_v28488, tll_ptr s2_v28489) {
  tll_ptr EQ_t154; tll_ptr GT_t157; tll_ptr GT_t162; tll_ptr LT_t155;
  tll_ptr LT_t161; tll_ptr __v28490; tll_ptr __v28491; tll_ptr c1_v28492;
  tll_ptr c2_v28494; tll_ptr call_ret_t158; tll_ptr call_ret_t160;
  tll_ptr s1_v28493; tll_ptr s2_v28495; tll_ptr switch_ret_t152;
  tll_ptr switch_ret_t153; tll_ptr switch_ret_t156; tll_ptr switch_ret_t159;
  switch(((tll_node)s1_v28488)->tag) {
    case 5:
      switch(((tll_node)s2_v28489)->tag) {
        case 5:
          instr_struct(&EQ_t154, 3, 0);
          switch_ret_t153 = EQ_t154;
          break;
        case 6:
          __v28490 = ((tll_node)s2_v28489)->data[0];
          __v28491 = ((tll_node)s2_v28489)->data[1];
          instr_struct(&LT_t155, 1, 0);
          switch_ret_t153 = LT_t155;
          break;
      }
      switch_ret_t152 = switch_ret_t153;
      break;
    case 6:
      c1_v28492 = ((tll_node)s1_v28488)->data[0];
      s1_v28493 = ((tll_node)s1_v28488)->data[1];
      switch(((tll_node)s2_v28489)->tag) {
        case 5:
          instr_struct(&GT_t157, 2, 0);
          switch_ret_t156 = GT_t157;
          break;
        case 6:
          c2_v28494 = ((tll_node)s2_v28489)->data[0];
          s2_v28495 = ((tll_node)s2_v28489)->data[1];
          call_ret_t158 = comparec_i18(c1_v28492, c2_v28494);
          switch(((tll_node)call_ret_t158)->tag) {
            case 3:
              call_ret_t160 = compares_i22(s1_v28493, s2_v28495);
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

tll_ptr lam_fun_t164(tll_ptr s2_v28498, tll_env env) {
  tll_ptr call_ret_t163;
  call_ret_t163 = compares_i22(env[0], s2_v28498);
  return call_ret_t163;
}

tll_ptr lam_fun_t166(tll_ptr s1_v28496, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, s1_v28496);
  return lam_clo_t165;
}

tll_ptr lenUU_i56(tll_ptr A_v28499, tll_ptr xs_v28500) {
  tll_ptr add_ret_t173; tll_ptr call_ret_t171; tll_ptr consUU_t174;
  tll_ptr n_v28503; tll_ptr nilUU_t169; tll_ptr pair_struct_t170;
  tll_ptr pair_struct_t175; tll_ptr switch_ret_t168; tll_ptr switch_ret_t172;
  tll_ptr x_v28501; tll_ptr xs_v28502; tll_ptr xs_v28504;
  switch(((tll_node)xs_v28500)->tag) {
    case 25:
      instr_struct(&nilUU_t169, 25, 0);
      instr_struct(&pair_struct_t170, 0, 2, (tll_ptr)0, nilUU_t169);
      switch_ret_t168 = pair_struct_t170;
      break;
    case 26:
      x_v28501 = ((tll_node)xs_v28500)->data[0];
      xs_v28502 = ((tll_node)xs_v28500)->data[1];
      call_ret_t171 = lenUU_i56(0, xs_v28502);
      switch(((tll_node)call_ret_t171)->tag) {
        case 0:
          n_v28503 = ((tll_node)call_ret_t171)->data[0];
          xs_v28504 = ((tll_node)call_ret_t171)->data[1];
          instr_free_struct(call_ret_t171);
          add_ret_t173 = n_v28503 + 1;
          instr_struct(&consUU_t174, 26, 2, x_v28501, xs_v28504);
          instr_struct(&pair_struct_t175, 0, 2, add_ret_t173, consUU_t174);
          switch_ret_t172 = pair_struct_t175;
          break;
      }
      switch_ret_t168 = switch_ret_t172;
      break;
  }
  return switch_ret_t168;
}

tll_ptr lam_fun_t177(tll_ptr xs_v28507, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = lenUU_i56(env[0], xs_v28507);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr A_v28505, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 1, A_v28505);
  return lam_clo_t178;
}

tll_ptr lenUL_i55(tll_ptr A_v28508, tll_ptr xs_v28509) {
  tll_ptr add_ret_t186; tll_ptr call_ret_t184; tll_ptr consUL_t187;
  tll_ptr n_v28512; tll_ptr nilUL_t182; tll_ptr pair_struct_t183;
  tll_ptr pair_struct_t188; tll_ptr switch_ret_t181; tll_ptr switch_ret_t185;
  tll_ptr x_v28510; tll_ptr xs_v28511; tll_ptr xs_v28513;
  switch(((tll_node)xs_v28509)->tag) {
    case 23:
      instr_free_struct(xs_v28509);
      instr_struct(&nilUL_t182, 23, 0);
      instr_struct(&pair_struct_t183, 0, 2, (tll_ptr)0, nilUL_t182);
      switch_ret_t181 = pair_struct_t183;
      break;
    case 24:
      x_v28510 = ((tll_node)xs_v28509)->data[0];
      xs_v28511 = ((tll_node)xs_v28509)->data[1];
      instr_free_struct(xs_v28509);
      call_ret_t184 = lenUL_i55(0, xs_v28511);
      switch(((tll_node)call_ret_t184)->tag) {
        case 0:
          n_v28512 = ((tll_node)call_ret_t184)->data[0];
          xs_v28513 = ((tll_node)call_ret_t184)->data[1];
          instr_free_struct(call_ret_t184);
          add_ret_t186 = n_v28512 + 1;
          instr_struct(&consUL_t187, 24, 2, x_v28510, xs_v28513);
          instr_struct(&pair_struct_t188, 0, 2, add_ret_t186, consUL_t187);
          switch_ret_t185 = pair_struct_t188;
          break;
      }
      switch_ret_t181 = switch_ret_t185;
      break;
  }
  return switch_ret_t181;
}

tll_ptr lam_fun_t190(tll_ptr xs_v28516, tll_env env) {
  tll_ptr call_ret_t189;
  call_ret_t189 = lenUL_i55(env[0], xs_v28516);
  return call_ret_t189;
}

tll_ptr lam_fun_t192(tll_ptr A_v28514, tll_env env) {
  tll_ptr lam_clo_t191;
  instr_clo(&lam_clo_t191, &lam_fun_t190, 1, A_v28514);
  return lam_clo_t191;
}

tll_ptr lenLL_i53(tll_ptr A_v28517, tll_ptr xs_v28518) {
  tll_ptr add_ret_t199; tll_ptr call_ret_t197; tll_ptr consLL_t200;
  tll_ptr n_v28521; tll_ptr nilLL_t195; tll_ptr pair_struct_t196;
  tll_ptr pair_struct_t201; tll_ptr switch_ret_t194; tll_ptr switch_ret_t198;
  tll_ptr x_v28519; tll_ptr xs_v28520; tll_ptr xs_v28522;
  switch(((tll_node)xs_v28518)->tag) {
    case 19:
      instr_free_struct(xs_v28518);
      instr_struct(&nilLL_t195, 19, 0);
      instr_struct(&pair_struct_t196, 0, 2, (tll_ptr)0, nilLL_t195);
      switch_ret_t194 = pair_struct_t196;
      break;
    case 20:
      x_v28519 = ((tll_node)xs_v28518)->data[0];
      xs_v28520 = ((tll_node)xs_v28518)->data[1];
      instr_free_struct(xs_v28518);
      call_ret_t197 = lenLL_i53(0, xs_v28520);
      switch(((tll_node)call_ret_t197)->tag) {
        case 0:
          n_v28521 = ((tll_node)call_ret_t197)->data[0];
          xs_v28522 = ((tll_node)call_ret_t197)->data[1];
          instr_free_struct(call_ret_t197);
          add_ret_t199 = n_v28521 + 1;
          instr_struct(&consLL_t200, 20, 2, x_v28519, xs_v28522);
          instr_struct(&pair_struct_t201, 0, 2, add_ret_t199, consLL_t200);
          switch_ret_t198 = pair_struct_t201;
          break;
      }
      switch_ret_t194 = switch_ret_t198;
      break;
  }
  return switch_ret_t194;
}

tll_ptr lam_fun_t203(tll_ptr xs_v28525, tll_env env) {
  tll_ptr call_ret_t202;
  call_ret_t202 = lenLL_i53(env[0], xs_v28525);
  return call_ret_t202;
}

tll_ptr lam_fun_t205(tll_ptr A_v28523, tll_env env) {
  tll_ptr lam_clo_t204;
  instr_clo(&lam_clo_t204, &lam_fun_t203, 1, A_v28523);
  return lam_clo_t204;
}

tll_ptr appendUU_i60(tll_ptr A_v28526, tll_ptr xs_v28527, tll_ptr ys_v28528) {
  tll_ptr call_ret_t208; tll_ptr consUU_t209; tll_ptr switch_ret_t207;
  tll_ptr x_v28529; tll_ptr xs_v28530;
  switch(((tll_node)xs_v28527)->tag) {
    case 25:
      switch_ret_t207 = ys_v28528;
      break;
    case 26:
      x_v28529 = ((tll_node)xs_v28527)->data[0];
      xs_v28530 = ((tll_node)xs_v28527)->data[1];
      call_ret_t208 = appendUU_i60(0, xs_v28530, ys_v28528);
      instr_struct(&consUU_t209, 26, 2, x_v28529, call_ret_t208);
      switch_ret_t207 = consUU_t209;
      break;
  }
  return switch_ret_t207;
}

tll_ptr lam_fun_t211(tll_ptr ys_v28536, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = appendUU_i60(env[1], env[0], ys_v28536);
  return call_ret_t210;
}

tll_ptr lam_fun_t213(tll_ptr xs_v28534, tll_env env) {
  tll_ptr lam_clo_t212;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 2, xs_v28534, env[0]);
  return lam_clo_t212;
}

tll_ptr lam_fun_t215(tll_ptr A_v28531, tll_env env) {
  tll_ptr lam_clo_t214;
  instr_clo(&lam_clo_t214, &lam_fun_t213, 1, A_v28531);
  return lam_clo_t214;
}

tll_ptr appendUL_i59(tll_ptr A_v28537, tll_ptr xs_v28538, tll_ptr ys_v28539) {
  tll_ptr call_ret_t218; tll_ptr consUL_t219; tll_ptr switch_ret_t217;
  tll_ptr x_v28540; tll_ptr xs_v28541;
  switch(((tll_node)xs_v28538)->tag) {
    case 23:
      instr_free_struct(xs_v28538);
      switch_ret_t217 = ys_v28539;
      break;
    case 24:
      x_v28540 = ((tll_node)xs_v28538)->data[0];
      xs_v28541 = ((tll_node)xs_v28538)->data[1];
      instr_free_struct(xs_v28538);
      call_ret_t218 = appendUL_i59(0, xs_v28541, ys_v28539);
      instr_struct(&consUL_t219, 24, 2, x_v28540, call_ret_t218);
      switch_ret_t217 = consUL_t219;
      break;
  }
  return switch_ret_t217;
}

tll_ptr lam_fun_t221(tll_ptr ys_v28547, tll_env env) {
  tll_ptr call_ret_t220;
  call_ret_t220 = appendUL_i59(env[1], env[0], ys_v28547);
  return call_ret_t220;
}

tll_ptr lam_fun_t223(tll_ptr xs_v28545, tll_env env) {
  tll_ptr lam_clo_t222;
  instr_clo(&lam_clo_t222, &lam_fun_t221, 2, xs_v28545, env[0]);
  return lam_clo_t222;
}

tll_ptr lam_fun_t225(tll_ptr A_v28542, tll_env env) {
  tll_ptr lam_clo_t224;
  instr_clo(&lam_clo_t224, &lam_fun_t223, 1, A_v28542);
  return lam_clo_t224;
}

tll_ptr appendLL_i57(tll_ptr A_v28548, tll_ptr xs_v28549, tll_ptr ys_v28550) {
  tll_ptr call_ret_t228; tll_ptr consLL_t229; tll_ptr switch_ret_t227;
  tll_ptr x_v28551; tll_ptr xs_v28552;
  switch(((tll_node)xs_v28549)->tag) {
    case 19:
      instr_free_struct(xs_v28549);
      switch_ret_t227 = ys_v28550;
      break;
    case 20:
      x_v28551 = ((tll_node)xs_v28549)->data[0];
      xs_v28552 = ((tll_node)xs_v28549)->data[1];
      instr_free_struct(xs_v28549);
      call_ret_t228 = appendLL_i57(0, xs_v28552, ys_v28550);
      instr_struct(&consLL_t229, 20, 2, x_v28551, call_ret_t228);
      switch_ret_t227 = consLL_t229;
      break;
  }
  return switch_ret_t227;
}

tll_ptr lam_fun_t231(tll_ptr ys_v28558, tll_env env) {
  tll_ptr call_ret_t230;
  call_ret_t230 = appendLL_i57(env[1], env[0], ys_v28558);
  return call_ret_t230;
}

tll_ptr lam_fun_t233(tll_ptr xs_v28556, tll_env env) {
  tll_ptr lam_clo_t232;
  instr_clo(&lam_clo_t232, &lam_fun_t231, 2, xs_v28556, env[0]);
  return lam_clo_t232;
}

tll_ptr lam_fun_t235(tll_ptr A_v28553, tll_env env) {
  tll_ptr lam_clo_t234;
  instr_clo(&lam_clo_t234, &lam_fun_t233, 1, A_v28553);
  return lam_clo_t234;
}

tll_ptr lam_fun_t242(tll_ptr __v28560, tll_env env) {
  tll_ptr __v28569; tll_ptr ch_v28567; tll_ptr ch_v28568; tll_ptr ch_v28571;
  tll_ptr ch_v28572; tll_ptr prim_ch_t237; tll_ptr recv_msg_t239;
  tll_ptr s_v28570; tll_ptr send_ch_t238; tll_ptr send_ch_t241;
  tll_ptr switch_ret_t240;
  instr_open(&prim_ch_t237, &proc_stdin);
  ch_v28567 = prim_ch_t237;
  instr_send(&send_ch_t238, ch_v28567, (tll_ptr)1);
  ch_v28568 = send_ch_t238;
  instr_recv(&recv_msg_t239, ch_v28568);
  __v28569 = recv_msg_t239;
  switch(((tll_node)__v28569)->tag) {
    case 0:
      s_v28570 = ((tll_node)__v28569)->data[0];
      ch_v28571 = ((tll_node)__v28569)->data[1];
      instr_free_struct(__v28569);
      instr_send(&send_ch_t241, ch_v28571, (tll_ptr)0);
      ch_v28572 = send_ch_t241;
      switch_ret_t240 = s_v28570;
      break;
  }
  return switch_ret_t240;
}

tll_ptr readline_i31(tll_ptr __v28559) {
  tll_ptr lam_clo_t243;
  instr_clo(&lam_clo_t243, &lam_fun_t242, 0);
  return lam_clo_t243;
}

tll_ptr lam_fun_t245(tll_ptr __v28573, tll_env env) {
  tll_ptr call_ret_t244;
  call_ret_t244 = readline_i31(__v28573);
  return call_ret_t244;
}

tll_ptr lam_fun_t251(tll_ptr __v28575, tll_env env) {
  tll_ptr ch_v28580; tll_ptr ch_v28581; tll_ptr ch_v28582; tll_ptr ch_v28583;
  tll_ptr prim_ch_t247; tll_ptr send_ch_t248; tll_ptr send_ch_t249;
  tll_ptr send_ch_t250;
  instr_open(&prim_ch_t247, &proc_stdout);
  ch_v28580 = prim_ch_t247;
  instr_send(&send_ch_t248, ch_v28580, (tll_ptr)1);
  ch_v28581 = send_ch_t248;
  instr_send(&send_ch_t249, ch_v28581, env[0]);
  ch_v28582 = send_ch_t249;
  instr_send(&send_ch_t250, ch_v28582, (tll_ptr)0);
  ch_v28583 = send_ch_t250;
  return 0;
}

tll_ptr print_i32(tll_ptr s_v28574) {
  tll_ptr lam_clo_t252;
  instr_clo(&lam_clo_t252, &lam_fun_t251, 1, s_v28574);
  return lam_clo_t252;
}

tll_ptr lam_fun_t254(tll_ptr s_v28584, tll_env env) {
  tll_ptr call_ret_t253;
  call_ret_t253 = print_i32(s_v28584);
  return call_ret_t253;
}

tll_ptr lam_fun_t260(tll_ptr __v28586, tll_env env) {
  tll_ptr ch_v28591; tll_ptr ch_v28592; tll_ptr ch_v28593; tll_ptr ch_v28594;
  tll_ptr prim_ch_t256; tll_ptr send_ch_t257; tll_ptr send_ch_t258;
  tll_ptr send_ch_t259;
  instr_open(&prim_ch_t256, &proc_stderr);
  ch_v28591 = prim_ch_t256;
  instr_send(&send_ch_t257, ch_v28591, (tll_ptr)1);
  ch_v28592 = send_ch_t257;
  instr_send(&send_ch_t258, ch_v28592, env[0]);
  ch_v28593 = send_ch_t258;
  instr_send(&send_ch_t259, ch_v28593, (tll_ptr)0);
  ch_v28594 = send_ch_t259;
  return 0;
}

tll_ptr prerr_i33(tll_ptr s_v28585) {
  tll_ptr lam_clo_t261;
  instr_clo(&lam_clo_t261, &lam_fun_t260, 1, s_v28585);
  return lam_clo_t261;
}

tll_ptr lam_fun_t263(tll_ptr s_v28595, tll_env env) {
  tll_ptr call_ret_t262;
  call_ret_t262 = prerr_i33(s_v28595);
  return call_ret_t262;
}

tll_ptr get_at_i35(tll_ptr A_v28596, tll_ptr n_v28597, tll_ptr xs_v28598, tll_ptr a_v28599) {
  tll_ptr __v28600; tll_ptr __v28603; tll_ptr add_ret_t308;
  tll_ptr call_ret_t307; tll_ptr ifte_ret_t310; tll_ptr switch_ret_t306;
  tll_ptr switch_ret_t309; tll_ptr x_v28602; tll_ptr xs_v28601;
  if (n_v28597) {
    switch(((tll_node)xs_v28598)->tag) {
      case 25:
        switch_ret_t306 = a_v28599;
        break;
      case 26:
        __v28600 = ((tll_node)xs_v28598)->data[0];
        xs_v28601 = ((tll_node)xs_v28598)->data[1];
        add_ret_t308 = n_v28597 - 1;
        call_ret_t307 = get_at_i35(0, add_ret_t308, xs_v28601, a_v28599);
        switch_ret_t306 = call_ret_t307;
        break;
    }
    ifte_ret_t310 = switch_ret_t306;
  }
  else {
    switch(((tll_node)xs_v28598)->tag) {
      case 25:
        switch_ret_t309 = a_v28599;
        break;
      case 26:
        x_v28602 = ((tll_node)xs_v28598)->data[0];
        __v28603 = ((tll_node)xs_v28598)->data[1];
        switch_ret_t309 = x_v28602;
        break;
    }
    ifte_ret_t310 = switch_ret_t309;
  }
  return ifte_ret_t310;
}

tll_ptr lam_fun_t312(tll_ptr a_v28613, tll_env env) {
  tll_ptr call_ret_t311;
  call_ret_t311 = get_at_i35(env[2], env[1], env[0], a_v28613);
  return call_ret_t311;
}

tll_ptr lam_fun_t314(tll_ptr xs_v28611, tll_env env) {
  tll_ptr lam_clo_t313;
  instr_clo(&lam_clo_t313, &lam_fun_t312, 3, xs_v28611, env[0], env[1]);
  return lam_clo_t313;
}

tll_ptr lam_fun_t316(tll_ptr n_v28608, tll_env env) {
  tll_ptr lam_clo_t315;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 2, n_v28608, env[0]);
  return lam_clo_t315;
}

tll_ptr lam_fun_t318(tll_ptr A_v28604, tll_env env) {
  tll_ptr lam_clo_t317;
  instr_clo(&lam_clo_t317, &lam_fun_t316, 1, A_v28604);
  return lam_clo_t317;
}

tll_ptr string_of_digit_i36(tll_ptr n_v28614) {
  tll_ptr EmptyString_t321; tll_ptr call_ret_t320;
  instr_struct(&EmptyString_t321, 5, 0);
  call_ret_t320 = get_at_i35(0, n_v28614, digits_i34, EmptyString_t321);
  return call_ret_t320;
}

tll_ptr lam_fun_t323(tll_ptr n_v28615, tll_env env) {
  tll_ptr call_ret_t322;
  call_ret_t322 = string_of_digit_i36(n_v28615);
  return call_ret_t322;
}

tll_ptr string_of_nat_i37(tll_ptr n_v28616) {
  tll_ptr call_ret_t325; tll_ptr call_ret_t326; tll_ptr call_ret_t327;
  tll_ptr call_ret_t328; tll_ptr call_ret_t329; tll_ptr call_ret_t330;
  tll_ptr ifte_ret_t331; tll_ptr n_v28618; tll_ptr s_v28617;
  call_ret_t326 = modn_i16(n_v28616, (tll_ptr)10);
  call_ret_t325 = string_of_digit_i36(call_ret_t326);
  s_v28617 = call_ret_t325;
  call_ret_t327 = divn_i15(n_v28616, (tll_ptr)10);
  n_v28618 = call_ret_t327;
  call_ret_t328 = ltn_i7((tll_ptr)0, n_v28618);
  if (call_ret_t328) {
    call_ret_t330 = string_of_nat_i37(n_v28618);
    call_ret_t329 = cats_i19(call_ret_t330, s_v28617);
    ifte_ret_t331 = call_ret_t329;
  }
  else {
    ifte_ret_t331 = s_v28617;
  }
  return ifte_ret_t331;
}

tll_ptr lam_fun_t333(tll_ptr n_v28619, tll_env env) {
  tll_ptr call_ret_t332;
  call_ret_t332 = string_of_nat_i37(n_v28619);
  return call_ret_t332;
}

tll_ptr digit_of_char_i38(tll_ptr c_v28620) {
  tll_ptr Char_t336; tll_ptr Char_t339; tll_ptr Char_t342; tll_ptr Char_t345;
  tll_ptr Char_t348; tll_ptr Char_t351; tll_ptr Char_t354; tll_ptr Char_t357;
  tll_ptr Char_t360; tll_ptr Char_t363; tll_ptr NoneUL_t365;
  tll_ptr SomeUL_t337; tll_ptr SomeUL_t340; tll_ptr SomeUL_t343;
  tll_ptr SomeUL_t346; tll_ptr SomeUL_t349; tll_ptr SomeUL_t352;
  tll_ptr SomeUL_t355; tll_ptr SomeUL_t358; tll_ptr SomeUL_t361;
  tll_ptr SomeUL_t364; tll_ptr call_ret_t335; tll_ptr call_ret_t338;
  tll_ptr call_ret_t341; tll_ptr call_ret_t344; tll_ptr call_ret_t347;
  tll_ptr call_ret_t350; tll_ptr call_ret_t353; tll_ptr call_ret_t356;
  tll_ptr call_ret_t359; tll_ptr call_ret_t362; tll_ptr ifte_ret_t366;
  tll_ptr ifte_ret_t367; tll_ptr ifte_ret_t368; tll_ptr ifte_ret_t369;
  tll_ptr ifte_ret_t370; tll_ptr ifte_ret_t371; tll_ptr ifte_ret_t372;
  tll_ptr ifte_ret_t373; tll_ptr ifte_ret_t374; tll_ptr ifte_ret_t375;
  instr_struct(&Char_t336, 4, 1, (tll_ptr)48);
  call_ret_t335 = eqc_i17(c_v28620, Char_t336);
  if (call_ret_t335) {
    instr_struct(&SomeUL_t337, 16, 1, (tll_ptr)0);
    ifte_ret_t375 = SomeUL_t337;
  }
  else {
    instr_struct(&Char_t339, 4, 1, (tll_ptr)49);
    call_ret_t338 = eqc_i17(c_v28620, Char_t339);
    if (call_ret_t338) {
      instr_struct(&SomeUL_t340, 16, 1, (tll_ptr)1);
      ifte_ret_t374 = SomeUL_t340;
    }
    else {
      instr_struct(&Char_t342, 4, 1, (tll_ptr)50);
      call_ret_t341 = eqc_i17(c_v28620, Char_t342);
      if (call_ret_t341) {
        instr_struct(&SomeUL_t343, 16, 1, (tll_ptr)2);
        ifte_ret_t373 = SomeUL_t343;
      }
      else {
        instr_struct(&Char_t345, 4, 1, (tll_ptr)51);
        call_ret_t344 = eqc_i17(c_v28620, Char_t345);
        if (call_ret_t344) {
          instr_struct(&SomeUL_t346, 16, 1, (tll_ptr)3);
          ifte_ret_t372 = SomeUL_t346;
        }
        else {
          instr_struct(&Char_t348, 4, 1, (tll_ptr)52);
          call_ret_t347 = eqc_i17(c_v28620, Char_t348);
          if (call_ret_t347) {
            instr_struct(&SomeUL_t349, 16, 1, (tll_ptr)4);
            ifte_ret_t371 = SomeUL_t349;
          }
          else {
            instr_struct(&Char_t351, 4, 1, (tll_ptr)53);
            call_ret_t350 = eqc_i17(c_v28620, Char_t351);
            if (call_ret_t350) {
              instr_struct(&SomeUL_t352, 16, 1, (tll_ptr)5);
              ifte_ret_t370 = SomeUL_t352;
            }
            else {
              instr_struct(&Char_t354, 4, 1, (tll_ptr)54);
              call_ret_t353 = eqc_i17(c_v28620, Char_t354);
              if (call_ret_t353) {
                instr_struct(&SomeUL_t355, 16, 1, (tll_ptr)6);
                ifte_ret_t369 = SomeUL_t355;
              }
              else {
                instr_struct(&Char_t357, 4, 1, (tll_ptr)55);
                call_ret_t356 = eqc_i17(c_v28620, Char_t357);
                if (call_ret_t356) {
                  instr_struct(&SomeUL_t358, 16, 1, (tll_ptr)7);
                  ifte_ret_t368 = SomeUL_t358;
                }
                else {
                  instr_struct(&Char_t360, 4, 1, (tll_ptr)56);
                  call_ret_t359 = eqc_i17(c_v28620, Char_t360);
                  if (call_ret_t359) {
                    instr_struct(&SomeUL_t361, 16, 1, (tll_ptr)8);
                    ifte_ret_t367 = SomeUL_t361;
                  }
                  else {
                    instr_struct(&Char_t363, 4, 1, (tll_ptr)57);
                    call_ret_t362 = eqc_i17(c_v28620, Char_t363);
                    if (call_ret_t362) {
                      instr_struct(&SomeUL_t364, 16, 1, (tll_ptr)9);
                      ifte_ret_t366 = SomeUL_t364;
                    }
                    else {
                      instr_struct(&NoneUL_t365, 15, 0);
                      ifte_ret_t366 = NoneUL_t365;
                    }
                    ifte_ret_t367 = ifte_ret_t366;
                  }
                  ifte_ret_t368 = ifte_ret_t367;
                }
                ifte_ret_t369 = ifte_ret_t368;
              }
              ifte_ret_t370 = ifte_ret_t369;
            }
            ifte_ret_t371 = ifte_ret_t370;
          }
          ifte_ret_t372 = ifte_ret_t371;
        }
        ifte_ret_t373 = ifte_ret_t372;
      }
      ifte_ret_t374 = ifte_ret_t373;
    }
    ifte_ret_t375 = ifte_ret_t374;
  }
  return ifte_ret_t375;
}

tll_ptr lam_fun_t377(tll_ptr c_v28621, tll_env env) {
  tll_ptr call_ret_t376;
  call_ret_t376 = digit_of_char_i38(c_v28621);
  return call_ret_t376;
}

tll_ptr nat_of_string_loop_i39(tll_ptr s_v28622, tll_ptr acc_v28623) {
  tll_ptr NoneUL_t383; tll_ptr SomeUL_t380; tll_ptr c_v28624;
  tll_ptr call_ret_t381; tll_ptr call_ret_t384; tll_ptr call_ret_t385;
  tll_ptr call_ret_t386; tll_ptr n_v28626; tll_ptr s_v28625;
  tll_ptr switch_ret_t379; tll_ptr switch_ret_t382;
  switch(((tll_node)s_v28622)->tag) {
    case 5:
      instr_struct(&SomeUL_t380, 16, 1, acc_v28623);
      switch_ret_t379 = SomeUL_t380;
      break;
    case 6:
      c_v28624 = ((tll_node)s_v28622)->data[0];
      s_v28625 = ((tll_node)s_v28622)->data[1];
      call_ret_t381 = digit_of_char_i38(c_v28624);
      switch(((tll_node)call_ret_t381)->tag) {
        case 15:
          instr_free_struct(call_ret_t381);
          instr_struct(&NoneUL_t383, 15, 0);
          switch_ret_t382 = NoneUL_t383;
          break;
        case 16:
          n_v28626 = ((tll_node)call_ret_t381)->data[0];
          instr_free_struct(call_ret_t381);
          call_ret_t386 = muln_i14(acc_v28623, (tll_ptr)10);
          call_ret_t385 = addn_i12(call_ret_t386, n_v28626);
          call_ret_t384 = nat_of_string_loop_i39(s_v28625, call_ret_t385);
          switch_ret_t382 = call_ret_t384;
          break;
      }
      switch_ret_t379 = switch_ret_t382;
      break;
  }
  return switch_ret_t379;
}

tll_ptr lam_fun_t388(tll_ptr acc_v28629, tll_env env) {
  tll_ptr call_ret_t387;
  call_ret_t387 = nat_of_string_loop_i39(env[0], acc_v28629);
  return call_ret_t387;
}

tll_ptr lam_fun_t390(tll_ptr s_v28627, tll_env env) {
  tll_ptr lam_clo_t389;
  instr_clo(&lam_clo_t389, &lam_fun_t388, 1, s_v28627);
  return lam_clo_t389;
}

tll_ptr nat_of_string_i40(tll_ptr s_v28630) {
  tll_ptr call_ret_t392;
  call_ret_t392 = nat_of_string_loop_i39(s_v28630, (tll_ptr)0);
  return call_ret_t392;
}

tll_ptr lam_fun_t394(tll_ptr s_v28631, tll_env env) {
  tll_ptr call_ret_t393;
  call_ret_t393 = nat_of_string_i40(s_v28631);
  return call_ret_t393;
}

tll_ptr lam_fun_t465(tll_ptr __v28633, tll_env env) {
  tll_ptr Char_t401; tll_ptr Char_t402; tll_ptr Char_t403; tll_ptr Char_t404;
  tll_ptr Char_t405; tll_ptr Char_t406; tll_ptr Char_t407; tll_ptr Char_t408;
  tll_ptr Char_t409; tll_ptr Char_t410; tll_ptr Char_t411; tll_ptr Char_t412;
  tll_ptr Char_t413; tll_ptr Char_t414; tll_ptr Char_t415; tll_ptr Char_t416;
  tll_ptr Char_t417; tll_ptr Char_t418; tll_ptr Char_t419; tll_ptr Char_t420;
  tll_ptr Char_t421; tll_ptr Char_t422; tll_ptr Char_t423; tll_ptr Char_t424;
  tll_ptr Char_t425; tll_ptr Char_t426; tll_ptr Char_t427; tll_ptr Char_t428;
  tll_ptr Char_t429; tll_ptr Char_t430; tll_ptr EmptyString_t431;
  tll_ptr String_t432; tll_ptr String_t433; tll_ptr String_t434;
  tll_ptr String_t435; tll_ptr String_t436; tll_ptr String_t437;
  tll_ptr String_t438; tll_ptr String_t439; tll_ptr String_t440;
  tll_ptr String_t441; tll_ptr String_t442; tll_ptr String_t443;
  tll_ptr String_t444; tll_ptr String_t445; tll_ptr String_t446;
  tll_ptr String_t447; tll_ptr String_t448; tll_ptr String_t449;
  tll_ptr String_t450; tll_ptr String_t451; tll_ptr String_t452;
  tll_ptr String_t453; tll_ptr String_t454; tll_ptr String_t455;
  tll_ptr String_t456; tll_ptr String_t457; tll_ptr String_t458;
  tll_ptr String_t459; tll_ptr String_t460; tll_ptr String_t461;
  tll_ptr __v28639; tll_ptr app_ret_t397; tll_ptr app_ret_t462;
  tll_ptr app_ret_t464; tll_ptr call_ret_t396; tll_ptr call_ret_t398;
  tll_ptr call_ret_t400; tll_ptr call_ret_t463; tll_ptr n_v28638;
  tll_ptr s_v28637; tll_ptr switch_ret_t399;
  call_ret_t396 = readline_i31(0);
  instr_app(&app_ret_t397, call_ret_t396, 0);
  instr_free_clo(call_ret_t396);
  s_v28637 = app_ret_t397;
  call_ret_t398 = nat_of_string_i40(s_v28637);
  switch(((tll_node)call_ret_t398)->tag) {
    case 16:
      n_v28638 = ((tll_node)call_ret_t398)->data[0];
      instr_free_struct(call_ret_t398);
      switch_ret_t399 = n_v28638;
      break;
    case 15:
      instr_free_struct(call_ret_t398);
      instr_struct(&Char_t401, 4, 1, (tll_ptr)112);
      instr_struct(&Char_t402, 4, 1, (tll_ptr)108);
      instr_struct(&Char_t403, 4, 1, (tll_ptr)101);
      instr_struct(&Char_t404, 4, 1, (tll_ptr)97);
      instr_struct(&Char_t405, 4, 1, (tll_ptr)115);
      instr_struct(&Char_t406, 4, 1, (tll_ptr)101);
      instr_struct(&Char_t407, 4, 1, (tll_ptr)32);
      instr_struct(&Char_t408, 4, 1, (tll_ptr)105);
      instr_struct(&Char_t409, 4, 1, (tll_ptr)110);
      instr_struct(&Char_t410, 4, 1, (tll_ptr)112);
      instr_struct(&Char_t411, 4, 1, (tll_ptr)117);
      instr_struct(&Char_t412, 4, 1, (tll_ptr)116);
      instr_struct(&Char_t413, 4, 1, (tll_ptr)32);
      instr_struct(&Char_t414, 4, 1, (tll_ptr)97);
      instr_struct(&Char_t415, 4, 1, (tll_ptr)32);
      instr_struct(&Char_t416, 4, 1, (tll_ptr)110);
      instr_struct(&Char_t417, 4, 1, (tll_ptr)97);
      instr_struct(&Char_t418, 4, 1, (tll_ptr)116);
      instr_struct(&Char_t419, 4, 1, (tll_ptr)117);
      instr_struct(&Char_t420, 4, 1, (tll_ptr)114);
      instr_struct(&Char_t421, 4, 1, (tll_ptr)97);
      instr_struct(&Char_t422, 4, 1, (tll_ptr)108);
      instr_struct(&Char_t423, 4, 1, (tll_ptr)32);
      instr_struct(&Char_t424, 4, 1, (tll_ptr)110);
      instr_struct(&Char_t425, 4, 1, (tll_ptr)117);
      instr_struct(&Char_t426, 4, 1, (tll_ptr)109);
      instr_struct(&Char_t427, 4, 1, (tll_ptr)98);
      instr_struct(&Char_t428, 4, 1, (tll_ptr)101);
      instr_struct(&Char_t429, 4, 1, (tll_ptr)114);
      instr_struct(&Char_t430, 4, 1, (tll_ptr)10);
      instr_struct(&EmptyString_t431, 5, 0);
      instr_struct(&String_t432, 6, 2, Char_t430, EmptyString_t431);
      instr_struct(&String_t433, 6, 2, Char_t429, String_t432);
      instr_struct(&String_t434, 6, 2, Char_t428, String_t433);
      instr_struct(&String_t435, 6, 2, Char_t427, String_t434);
      instr_struct(&String_t436, 6, 2, Char_t426, String_t435);
      instr_struct(&String_t437, 6, 2, Char_t425, String_t436);
      instr_struct(&String_t438, 6, 2, Char_t424, String_t437);
      instr_struct(&String_t439, 6, 2, Char_t423, String_t438);
      instr_struct(&String_t440, 6, 2, Char_t422, String_t439);
      instr_struct(&String_t441, 6, 2, Char_t421, String_t440);
      instr_struct(&String_t442, 6, 2, Char_t420, String_t441);
      instr_struct(&String_t443, 6, 2, Char_t419, String_t442);
      instr_struct(&String_t444, 6, 2, Char_t418, String_t443);
      instr_struct(&String_t445, 6, 2, Char_t417, String_t444);
      instr_struct(&String_t446, 6, 2, Char_t416, String_t445);
      instr_struct(&String_t447, 6, 2, Char_t415, String_t446);
      instr_struct(&String_t448, 6, 2, Char_t414, String_t447);
      instr_struct(&String_t449, 6, 2, Char_t413, String_t448);
      instr_struct(&String_t450, 6, 2, Char_t412, String_t449);
      instr_struct(&String_t451, 6, 2, Char_t411, String_t450);
      instr_struct(&String_t452, 6, 2, Char_t410, String_t451);
      instr_struct(&String_t453, 6, 2, Char_t409, String_t452);
      instr_struct(&String_t454, 6, 2, Char_t408, String_t453);
      instr_struct(&String_t455, 6, 2, Char_t407, String_t454);
      instr_struct(&String_t456, 6, 2, Char_t406, String_t455);
      instr_struct(&String_t457, 6, 2, Char_t405, String_t456);
      instr_struct(&String_t458, 6, 2, Char_t404, String_t457);
      instr_struct(&String_t459, 6, 2, Char_t403, String_t458);
      instr_struct(&String_t460, 6, 2, Char_t402, String_t459);
      instr_struct(&String_t461, 6, 2, Char_t401, String_t460);
      call_ret_t400 = print_i32(String_t461);
      instr_app(&app_ret_t462, call_ret_t400, 0);
      instr_free_clo(call_ret_t400);
      __v28639 = app_ret_t462;
      call_ret_t463 = read_nat_i47(0);
      instr_app(&app_ret_t464, call_ret_t463, 0);
      instr_free_clo(call_ret_t463);
      switch_ret_t399 = app_ret_t464;
      break;
  }
  return switch_ret_t399;
}

tll_ptr read_nat_i47(tll_ptr __v28632) {
  tll_ptr lam_clo_t466;
  instr_clo(&lam_clo_t466, &lam_fun_t465, 0);
  return lam_clo_t466;
}

tll_ptr lam_fun_t468(tll_ptr __v28640, tll_env env) {
  tll_ptr call_ret_t467;
  call_ret_t467 = read_nat_i47(__v28640);
  return call_ret_t467;
}

tll_ptr lam_fun_t700(tll_ptr __v28656, tll_env env) {
  tll_ptr Char_t479; tll_ptr Char_t480; tll_ptr Char_t481; tll_ptr Char_t482;
  tll_ptr Char_t483; tll_ptr Char_t484; tll_ptr Char_t485; tll_ptr Char_t486;
  tll_ptr Char_t487; tll_ptr Char_t503; tll_ptr Char_t504; tll_ptr Char_t505;
  tll_ptr Char_t506; tll_ptr Char_t507; tll_ptr Char_t508; tll_ptr Char_t509;
  tll_ptr Char_t510; tll_ptr Char_t511; tll_ptr Char_t512; tll_ptr Char_t513;
  tll_ptr Char_t514; tll_ptr Char_t515; tll_ptr Char_t516; tll_ptr Char_t517;
  tll_ptr Char_t518; tll_ptr Char_t519; tll_ptr Char_t520; tll_ptr Char_t521;
  tll_ptr Char_t522; tll_ptr Char_t523; tll_ptr Char_t524; tll_ptr Char_t525;
  tll_ptr Char_t526; tll_ptr Char_t527; tll_ptr Char_t528; tll_ptr Char_t529;
  tll_ptr Char_t530; tll_ptr Char_t531; tll_ptr Char_t532; tll_ptr Char_t533;
  tll_ptr Char_t568; tll_ptr Char_t569; tll_ptr Char_t570; tll_ptr Char_t571;
  tll_ptr Char_t572; tll_ptr Char_t573; tll_ptr Char_t574; tll_ptr Char_t575;
  tll_ptr Char_t576; tll_ptr Char_t577; tll_ptr Char_t578; tll_ptr Char_t579;
  tll_ptr Char_t580; tll_ptr Char_t602; tll_ptr Char_t603; tll_ptr Char_t604;
  tll_ptr Char_t605; tll_ptr Char_t606; tll_ptr Char_t607; tll_ptr Char_t608;
  tll_ptr Char_t609; tll_ptr Char_t610; tll_ptr Char_t611; tll_ptr Char_t612;
  tll_ptr Char_t613; tll_ptr Char_t614; tll_ptr Char_t615; tll_ptr Char_t616;
  tll_ptr Char_t617; tll_ptr Char_t618; tll_ptr Char_t619; tll_ptr Char_t620;
  tll_ptr Char_t621; tll_ptr Char_t622; tll_ptr Char_t623; tll_ptr Char_t624;
  tll_ptr Char_t625; tll_ptr Char_t626; tll_ptr Char_t627; tll_ptr Char_t628;
  tll_ptr Char_t629; tll_ptr Char_t630; tll_ptr Char_t631; tll_ptr Char_t632;
  tll_ptr Char_t633; tll_ptr Char_t669; tll_ptr Char_t670; tll_ptr Char_t671;
  tll_ptr Char_t672; tll_ptr Char_t673; tll_ptr Char_t674; tll_ptr Char_t675;
  tll_ptr Char_t676; tll_ptr Char_t677; tll_ptr Char_t678; tll_ptr Char_t679;
  tll_ptr Char_t680; tll_ptr Char_t681; tll_ptr EmptyString_t488;
  tll_ptr EmptyString_t534; tll_ptr EmptyString_t581;
  tll_ptr EmptyString_t634; tll_ptr EmptyString_t682; tll_ptr String_t489;
  tll_ptr String_t490; tll_ptr String_t491; tll_ptr String_t492;
  tll_ptr String_t493; tll_ptr String_t494; tll_ptr String_t495;
  tll_ptr String_t496; tll_ptr String_t497; tll_ptr String_t535;
  tll_ptr String_t536; tll_ptr String_t537; tll_ptr String_t538;
  tll_ptr String_t539; tll_ptr String_t540; tll_ptr String_t541;
  tll_ptr String_t542; tll_ptr String_t543; tll_ptr String_t544;
  tll_ptr String_t545; tll_ptr String_t546; tll_ptr String_t547;
  tll_ptr String_t548; tll_ptr String_t549; tll_ptr String_t550;
  tll_ptr String_t551; tll_ptr String_t552; tll_ptr String_t553;
  tll_ptr String_t554; tll_ptr String_t555; tll_ptr String_t556;
  tll_ptr String_t557; tll_ptr String_t558; tll_ptr String_t559;
  tll_ptr String_t560; tll_ptr String_t561; tll_ptr String_t562;
  tll_ptr String_t563; tll_ptr String_t564; tll_ptr String_t565;
  tll_ptr String_t582; tll_ptr String_t583; tll_ptr String_t584;
  tll_ptr String_t585; tll_ptr String_t586; tll_ptr String_t587;
  tll_ptr String_t588; tll_ptr String_t589; tll_ptr String_t590;
  tll_ptr String_t591; tll_ptr String_t592; tll_ptr String_t593;
  tll_ptr String_t594; tll_ptr String_t635; tll_ptr String_t636;
  tll_ptr String_t637; tll_ptr String_t638; tll_ptr String_t639;
  tll_ptr String_t640; tll_ptr String_t641; tll_ptr String_t642;
  tll_ptr String_t643; tll_ptr String_t644; tll_ptr String_t645;
  tll_ptr String_t646; tll_ptr String_t647; tll_ptr String_t648;
  tll_ptr String_t649; tll_ptr String_t650; tll_ptr String_t651;
  tll_ptr String_t652; tll_ptr String_t653; tll_ptr String_t654;
  tll_ptr String_t655; tll_ptr String_t656; tll_ptr String_t657;
  tll_ptr String_t658; tll_ptr String_t659; tll_ptr String_t660;
  tll_ptr String_t661; tll_ptr String_t662; tll_ptr String_t663;
  tll_ptr String_t664; tll_ptr String_t665; tll_ptr String_t666;
  tll_ptr String_t683; tll_ptr String_t684; tll_ptr String_t685;
  tll_ptr String_t686; tll_ptr String_t687; tll_ptr String_t688;
  tll_ptr String_t689; tll_ptr String_t690; tll_ptr String_t691;
  tll_ptr String_t692; tll_ptr String_t693; tll_ptr String_t694;
  tll_ptr String_t695; tll_ptr __v28669; tll_ptr __v28674; tll_ptr __v28675;
  tll_ptr __v28676; tll_ptr add_ret_t567; tll_ptr add_ret_t597;
  tll_ptr add_ret_t668; tll_ptr add_ret_t698; tll_ptr app_ret_t471;
  tll_ptr app_ret_t498; tll_ptr app_ret_t595; tll_ptr app_ret_t598;
  tll_ptr app_ret_t696; tll_ptr app_ret_t699; tll_ptr c_v28668;
  tll_ptr c_v28671; tll_ptr c_v28673; tll_ptr call_ret_t470;
  tll_ptr call_ret_t478; tll_ptr call_ret_t500; tll_ptr call_ret_t501;
  tll_ptr call_ret_t502; tll_ptr call_ret_t566; tll_ptr call_ret_t596;
  tll_ptr call_ret_t599; tll_ptr call_ret_t600; tll_ptr call_ret_t601;
  tll_ptr call_ret_t667; tll_ptr call_ret_t697; tll_ptr close_tmp_t499;
  tll_ptr guess_v28667; tll_ptr ord_v28670; tll_ptr pair_struct_t475;
  tll_ptr pf_v28672; tll_ptr recv_msg_t473; tll_ptr send_ch_t472;
  tll_ptr switch_ret_t474; tll_ptr switch_ret_t476; tll_ptr switch_ret_t477;
  call_ret_t470 = read_nat_i47(0);
  instr_app(&app_ret_t471, call_ret_t470, 0);
  instr_free_clo(call_ret_t470);
  guess_v28667 = app_ret_t471;
  instr_send(&send_ch_t472, env[0], guess_v28667);
  c_v28668 = send_ch_t472;
  instr_recv(&recv_msg_t473, c_v28668);
  __v28669 = recv_msg_t473;
  switch(((tll_node)__v28669)->tag) {
    case 0:
      ord_v28670 = ((tll_node)__v28669)->data[0];
      c_v28671 = ((tll_node)__v28669)->data[1];
      instr_free_struct(__v28669);
      instr_struct(&pair_struct_t475, 0, 2, 0, c_v28671);
      switch(((tll_node)pair_struct_t475)->tag) {
        case 0:
          pf_v28672 = ((tll_node)pair_struct_t475)->data[0];
          c_v28673 = ((tll_node)pair_struct_t475)->data[1];
          instr_free_struct(pair_struct_t475);
          switch(((tll_node)ord_v28670)->tag) {
            case 3:
              instr_struct(&Char_t479, 4, 1, (tll_ptr)89);
              instr_struct(&Char_t480, 4, 1, (tll_ptr)111);
              instr_struct(&Char_t481, 4, 1, (tll_ptr)117);
              instr_struct(&Char_t482, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t483, 4, 1, (tll_ptr)87);
              instr_struct(&Char_t484, 4, 1, (tll_ptr)105);
              instr_struct(&Char_t485, 4, 1, (tll_ptr)110);
              instr_struct(&Char_t486, 4, 1, (tll_ptr)33);
              instr_struct(&Char_t487, 4, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t488, 5, 0);
              instr_struct(&String_t489, 6, 2, Char_t487, EmptyString_t488);
              instr_struct(&String_t490, 6, 2, Char_t486, String_t489);
              instr_struct(&String_t491, 6, 2, Char_t485, String_t490);
              instr_struct(&String_t492, 6, 2, Char_t484, String_t491);
              instr_struct(&String_t493, 6, 2, Char_t483, String_t492);
              instr_struct(&String_t494, 6, 2, Char_t482, String_t493);
              instr_struct(&String_t495, 6, 2, Char_t481, String_t494);
              instr_struct(&String_t496, 6, 2, Char_t480, String_t495);
              instr_struct(&String_t497, 6, 2, Char_t479, String_t496);
              call_ret_t478 = print_i32(String_t497);
              instr_app(&app_ret_t498, call_ret_t478, 0);
              instr_free_clo(call_ret_t478);
              __v28674 = app_ret_t498;
              instr_close(&close_tmp_t499, c_v28673);
              switch_ret_t477 = close_tmp_t499;
              break;
            case 1:
              instr_struct(&Char_t503, 4, 1, (tll_ptr)84);
              instr_struct(&Char_t504, 4, 1, (tll_ptr)104);
              instr_struct(&Char_t505, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t506, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t507, 4, 1, (tll_ptr)97);
              instr_struct(&Char_t508, 4, 1, (tll_ptr)110);
              instr_struct(&Char_t509, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t510, 4, 1, (tll_ptr)119);
              instr_struct(&Char_t511, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t512, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t513, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t514, 4, 1, (tll_ptr)105);
              instr_struct(&Char_t515, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t516, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t517, 4, 1, (tll_ptr)108);
              instr_struct(&Char_t518, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t519, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t520, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t521, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t522, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t523, 4, 1, (tll_ptr)44);
              instr_struct(&Char_t524, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t525, 4, 1, (tll_ptr)121);
              instr_struct(&Char_t526, 4, 1, (tll_ptr)111);
              instr_struct(&Char_t527, 4, 1, (tll_ptr)117);
              instr_struct(&Char_t528, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t529, 4, 1, (tll_ptr)104);
              instr_struct(&Char_t530, 4, 1, (tll_ptr)97);
              instr_struct(&Char_t531, 4, 1, (tll_ptr)118);
              instr_struct(&Char_t532, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t533, 4, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t534, 5, 0);
              instr_struct(&String_t535, 6, 2, Char_t533, EmptyString_t534);
              instr_struct(&String_t536, 6, 2, Char_t532, String_t535);
              instr_struct(&String_t537, 6, 2, Char_t531, String_t536);
              instr_struct(&String_t538, 6, 2, Char_t530, String_t537);
              instr_struct(&String_t539, 6, 2, Char_t529, String_t538);
              instr_struct(&String_t540, 6, 2, Char_t528, String_t539);
              instr_struct(&String_t541, 6, 2, Char_t527, String_t540);
              instr_struct(&String_t542, 6, 2, Char_t526, String_t541);
              instr_struct(&String_t543, 6, 2, Char_t525, String_t542);
              instr_struct(&String_t544, 6, 2, Char_t524, String_t543);
              instr_struct(&String_t545, 6, 2, Char_t523, String_t544);
              instr_struct(&String_t546, 6, 2, Char_t522, String_t545);
              instr_struct(&String_t547, 6, 2, Char_t521, String_t546);
              instr_struct(&String_t548, 6, 2, Char_t520, String_t547);
              instr_struct(&String_t549, 6, 2, Char_t519, String_t548);
              instr_struct(&String_t550, 6, 2, Char_t518, String_t549);
              instr_struct(&String_t551, 6, 2, Char_t517, String_t550);
              instr_struct(&String_t552, 6, 2, Char_t516, String_t551);
              instr_struct(&String_t553, 6, 2, Char_t515, String_t552);
              instr_struct(&String_t554, 6, 2, Char_t514, String_t553);
              instr_struct(&String_t555, 6, 2, Char_t513, String_t554);
              instr_struct(&String_t556, 6, 2, Char_t512, String_t555);
              instr_struct(&String_t557, 6, 2, Char_t511, String_t556);
              instr_struct(&String_t558, 6, 2, Char_t510, String_t557);
              instr_struct(&String_t559, 6, 2, Char_t509, String_t558);
              instr_struct(&String_t560, 6, 2, Char_t508, String_t559);
              instr_struct(&String_t561, 6, 2, Char_t507, String_t560);
              instr_struct(&String_t562, 6, 2, Char_t506, String_t561);
              instr_struct(&String_t563, 6, 2, Char_t505, String_t562);
              instr_struct(&String_t564, 6, 2, Char_t504, String_t563);
              instr_struct(&String_t565, 6, 2, Char_t503, String_t564);
              add_ret_t567 = env[1] - 1;
              call_ret_t566 = string_of_nat_i37(add_ret_t567);
              call_ret_t502 = cats_i19(String_t565, call_ret_t566);
              instr_struct(&Char_t568, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t569, 4, 1, (tll_ptr)109);
              instr_struct(&Char_t570, 4, 1, (tll_ptr)111);
              instr_struct(&Char_t571, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t572, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t573, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t574, 4, 1, (tll_ptr)116);
              instr_struct(&Char_t575, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t576, 4, 1, (tll_ptr)105);
              instr_struct(&Char_t577, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t578, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t579, 4, 1, (tll_ptr)46);
              instr_struct(&Char_t580, 4, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t581, 5, 0);
              instr_struct(&String_t582, 6, 2, Char_t580, EmptyString_t581);
              instr_struct(&String_t583, 6, 2, Char_t579, String_t582);
              instr_struct(&String_t584, 6, 2, Char_t578, String_t583);
              instr_struct(&String_t585, 6, 2, Char_t577, String_t584);
              instr_struct(&String_t586, 6, 2, Char_t576, String_t585);
              instr_struct(&String_t587, 6, 2, Char_t575, String_t586);
              instr_struct(&String_t588, 6, 2, Char_t574, String_t587);
              instr_struct(&String_t589, 6, 2, Char_t573, String_t588);
              instr_struct(&String_t590, 6, 2, Char_t572, String_t589);
              instr_struct(&String_t591, 6, 2, Char_t571, String_t590);
              instr_struct(&String_t592, 6, 2, Char_t570, String_t591);
              instr_struct(&String_t593, 6, 2, Char_t569, String_t592);
              instr_struct(&String_t594, 6, 2, Char_t568, String_t593);
              call_ret_t501 = cats_i19(call_ret_t502, String_t594);
              call_ret_t500 = print_i32(call_ret_t501);
              instr_app(&app_ret_t595, call_ret_t500, 0);
              instr_free_clo(call_ret_t500);
              __v28675 = app_ret_t595;
              add_ret_t597 = env[1] - 1;
              call_ret_t596 = player_loop_i48(0, add_ret_t597, c_v28673);
              instr_app(&app_ret_t598, call_ret_t596, 0);
              instr_free_clo(call_ret_t596);
              switch_ret_t477 = app_ret_t598;
              break;
            case 2:
              instr_struct(&Char_t602, 4, 1, (tll_ptr)84);
              instr_struct(&Char_t603, 4, 1, (tll_ptr)104);
              instr_struct(&Char_t604, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t605, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t606, 4, 1, (tll_ptr)97);
              instr_struct(&Char_t607, 4, 1, (tll_ptr)110);
              instr_struct(&Char_t608, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t609, 4, 1, (tll_ptr)119);
              instr_struct(&Char_t610, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t611, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t612, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t613, 4, 1, (tll_ptr)105);
              instr_struct(&Char_t614, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t615, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t616, 4, 1, (tll_ptr)103);
              instr_struct(&Char_t617, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t618, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t619, 4, 1, (tll_ptr)97);
              instr_struct(&Char_t620, 4, 1, (tll_ptr)116);
              instr_struct(&Char_t621, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t622, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t623, 4, 1, (tll_ptr)44);
              instr_struct(&Char_t624, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t625, 4, 1, (tll_ptr)121);
              instr_struct(&Char_t626, 4, 1, (tll_ptr)111);
              instr_struct(&Char_t627, 4, 1, (tll_ptr)117);
              instr_struct(&Char_t628, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t629, 4, 1, (tll_ptr)104);
              instr_struct(&Char_t630, 4, 1, (tll_ptr)97);
              instr_struct(&Char_t631, 4, 1, (tll_ptr)118);
              instr_struct(&Char_t632, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t633, 4, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t634, 5, 0);
              instr_struct(&String_t635, 6, 2, Char_t633, EmptyString_t634);
              instr_struct(&String_t636, 6, 2, Char_t632, String_t635);
              instr_struct(&String_t637, 6, 2, Char_t631, String_t636);
              instr_struct(&String_t638, 6, 2, Char_t630, String_t637);
              instr_struct(&String_t639, 6, 2, Char_t629, String_t638);
              instr_struct(&String_t640, 6, 2, Char_t628, String_t639);
              instr_struct(&String_t641, 6, 2, Char_t627, String_t640);
              instr_struct(&String_t642, 6, 2, Char_t626, String_t641);
              instr_struct(&String_t643, 6, 2, Char_t625, String_t642);
              instr_struct(&String_t644, 6, 2, Char_t624, String_t643);
              instr_struct(&String_t645, 6, 2, Char_t623, String_t644);
              instr_struct(&String_t646, 6, 2, Char_t622, String_t645);
              instr_struct(&String_t647, 6, 2, Char_t621, String_t646);
              instr_struct(&String_t648, 6, 2, Char_t620, String_t647);
              instr_struct(&String_t649, 6, 2, Char_t619, String_t648);
              instr_struct(&String_t650, 6, 2, Char_t618, String_t649);
              instr_struct(&String_t651, 6, 2, Char_t617, String_t650);
              instr_struct(&String_t652, 6, 2, Char_t616, String_t651);
              instr_struct(&String_t653, 6, 2, Char_t615, String_t652);
              instr_struct(&String_t654, 6, 2, Char_t614, String_t653);
              instr_struct(&String_t655, 6, 2, Char_t613, String_t654);
              instr_struct(&String_t656, 6, 2, Char_t612, String_t655);
              instr_struct(&String_t657, 6, 2, Char_t611, String_t656);
              instr_struct(&String_t658, 6, 2, Char_t610, String_t657);
              instr_struct(&String_t659, 6, 2, Char_t609, String_t658);
              instr_struct(&String_t660, 6, 2, Char_t608, String_t659);
              instr_struct(&String_t661, 6, 2, Char_t607, String_t660);
              instr_struct(&String_t662, 6, 2, Char_t606, String_t661);
              instr_struct(&String_t663, 6, 2, Char_t605, String_t662);
              instr_struct(&String_t664, 6, 2, Char_t604, String_t663);
              instr_struct(&String_t665, 6, 2, Char_t603, String_t664);
              instr_struct(&String_t666, 6, 2, Char_t602, String_t665);
              add_ret_t668 = env[1] - 1;
              call_ret_t667 = string_of_nat_i37(add_ret_t668);
              call_ret_t601 = cats_i19(String_t666, call_ret_t667);
              instr_struct(&Char_t669, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t670, 4, 1, (tll_ptr)109);
              instr_struct(&Char_t671, 4, 1, (tll_ptr)111);
              instr_struct(&Char_t672, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t673, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t674, 4, 1, (tll_ptr)32);
              instr_struct(&Char_t675, 4, 1, (tll_ptr)116);
              instr_struct(&Char_t676, 4, 1, (tll_ptr)114);
              instr_struct(&Char_t677, 4, 1, (tll_ptr)105);
              instr_struct(&Char_t678, 4, 1, (tll_ptr)101);
              instr_struct(&Char_t679, 4, 1, (tll_ptr)115);
              instr_struct(&Char_t680, 4, 1, (tll_ptr)46);
              instr_struct(&Char_t681, 4, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t682, 5, 0);
              instr_struct(&String_t683, 6, 2, Char_t681, EmptyString_t682);
              instr_struct(&String_t684, 6, 2, Char_t680, String_t683);
              instr_struct(&String_t685, 6, 2, Char_t679, String_t684);
              instr_struct(&String_t686, 6, 2, Char_t678, String_t685);
              instr_struct(&String_t687, 6, 2, Char_t677, String_t686);
              instr_struct(&String_t688, 6, 2, Char_t676, String_t687);
              instr_struct(&String_t689, 6, 2, Char_t675, String_t688);
              instr_struct(&String_t690, 6, 2, Char_t674, String_t689);
              instr_struct(&String_t691, 6, 2, Char_t673, String_t690);
              instr_struct(&String_t692, 6, 2, Char_t672, String_t691);
              instr_struct(&String_t693, 6, 2, Char_t671, String_t692);
              instr_struct(&String_t694, 6, 2, Char_t670, String_t693);
              instr_struct(&String_t695, 6, 2, Char_t669, String_t694);
              call_ret_t600 = cats_i19(call_ret_t601, String_t695);
              call_ret_t599 = print_i32(call_ret_t600);
              instr_app(&app_ret_t696, call_ret_t599, 0);
              instr_free_clo(call_ret_t599);
              __v28676 = app_ret_t696;
              add_ret_t698 = env[1] - 1;
              call_ret_t697 = player_loop_i48(0, add_ret_t698, c_v28673);
              instr_app(&app_ret_t699, call_ret_t697, 0);
              instr_free_clo(call_ret_t697);
              switch_ret_t477 = app_ret_t699;
              break;
          }
          switch_ret_t476 = switch_ret_t477;
          break;
      }
      switch_ret_t474 = switch_ret_t476;
      break;
  }
  return switch_ret_t474;
}

tll_ptr lam_fun_t702(tll_ptr c_v28644, tll_env env) {
  tll_ptr lam_clo_t701;
  instr_clo(&lam_clo_t701, &lam_fun_t700, 2, c_v28644, env[0]);
  return lam_clo_t701;
}

tll_ptr lam_fun_t728(tll_ptr __v28680, tll_env env) {
  tll_ptr Char_t705; tll_ptr Char_t706; tll_ptr Char_t707; tll_ptr Char_t708;
  tll_ptr Char_t709; tll_ptr Char_t710; tll_ptr Char_t711; tll_ptr Char_t712;
  tll_ptr Char_t713; tll_ptr Char_t714; tll_ptr EmptyString_t715;
  tll_ptr String_t716; tll_ptr String_t717; tll_ptr String_t718;
  tll_ptr String_t719; tll_ptr String_t720; tll_ptr String_t721;
  tll_ptr String_t722; tll_ptr String_t723; tll_ptr String_t724;
  tll_ptr String_t725; tll_ptr __v28682; tll_ptr app_ret_t726;
  tll_ptr call_ret_t704; tll_ptr close_tmp_t727;
  instr_struct(&Char_t705, 4, 1, (tll_ptr)89);
  instr_struct(&Char_t706, 4, 1, (tll_ptr)111);
  instr_struct(&Char_t707, 4, 1, (tll_ptr)117);
  instr_struct(&Char_t708, 4, 1, (tll_ptr)32);
  instr_struct(&Char_t709, 4, 1, (tll_ptr)76);
  instr_struct(&Char_t710, 4, 1, (tll_ptr)111);
  instr_struct(&Char_t711, 4, 1, (tll_ptr)115);
  instr_struct(&Char_t712, 4, 1, (tll_ptr)101);
  instr_struct(&Char_t713, 4, 1, (tll_ptr)33);
  instr_struct(&Char_t714, 4, 1, (tll_ptr)10);
  instr_struct(&EmptyString_t715, 5, 0);
  instr_struct(&String_t716, 6, 2, Char_t714, EmptyString_t715);
  instr_struct(&String_t717, 6, 2, Char_t713, String_t716);
  instr_struct(&String_t718, 6, 2, Char_t712, String_t717);
  instr_struct(&String_t719, 6, 2, Char_t711, String_t718);
  instr_struct(&String_t720, 6, 2, Char_t710, String_t719);
  instr_struct(&String_t721, 6, 2, Char_t709, String_t720);
  instr_struct(&String_t722, 6, 2, Char_t708, String_t721);
  instr_struct(&String_t723, 6, 2, Char_t707, String_t722);
  instr_struct(&String_t724, 6, 2, Char_t706, String_t723);
  instr_struct(&String_t725, 6, 2, Char_t705, String_t724);
  call_ret_t704 = print_i32(String_t725);
  instr_app(&app_ret_t726, call_ret_t704, 0);
  instr_free_clo(call_ret_t704);
  __v28682 = app_ret_t726;
  instr_close(&close_tmp_t727, env[0]);
  return close_tmp_t727;
}

tll_ptr lam_fun_t730(tll_ptr c_v28677, tll_env env) {
  tll_ptr lam_clo_t729;
  instr_clo(&lam_clo_t729, &lam_fun_t728, 1, c_v28677);
  return lam_clo_t729;
}

tll_ptr player_loop_i48(tll_ptr ans_v28641, tll_ptr repeat_v28642, tll_ptr c_v28643) {
  tll_ptr app_ret_t733; tll_ptr ifte_ret_t732; tll_ptr lam_clo_t703;
  tll_ptr lam_clo_t731;
  if (repeat_v28642) {
    instr_clo(&lam_clo_t703, &lam_fun_t702, 1, repeat_v28642);
    ifte_ret_t732 = lam_clo_t703;
  }
  else {
    instr_clo(&lam_clo_t731, &lam_fun_t730, 0);
    ifte_ret_t732 = lam_clo_t731;
  }
  instr_app(&app_ret_t733, ifte_ret_t732, c_v28643);
  return app_ret_t733;
}

tll_ptr lam_fun_t735(tll_ptr c_v28688, tll_env env) {
  tll_ptr call_ret_t734;
  call_ret_t734 = player_loop_i48(env[1], env[0], c_v28688);
  return call_ret_t734;
}

tll_ptr lam_fun_t737(tll_ptr repeat_v28686, tll_env env) {
  tll_ptr lam_clo_t736;
  instr_clo(&lam_clo_t736, &lam_fun_t735, 2, repeat_v28686, env[0]);
  return lam_clo_t736;
}

tll_ptr lam_fun_t739(tll_ptr ans_v28683, tll_env env) {
  tll_ptr lam_clo_t738;
  instr_clo(&lam_clo_t738, &lam_fun_t737, 1, ans_v28683);
  return lam_clo_t738;
}

tll_ptr lam_fun_t877(tll_ptr __v28690, tll_env env) {
  tll_ptr Char_t758; tll_ptr Char_t759; tll_ptr Char_t760; tll_ptr Char_t761;
  tll_ptr Char_t762; tll_ptr Char_t763; tll_ptr Char_t764; tll_ptr Char_t765;
  tll_ptr Char_t766; tll_ptr Char_t767; tll_ptr Char_t768; tll_ptr Char_t769;
  tll_ptr Char_t770; tll_ptr Char_t771; tll_ptr Char_t772; tll_ptr Char_t773;
  tll_ptr Char_t774; tll_ptr Char_t775; tll_ptr Char_t776; tll_ptr Char_t777;
  tll_ptr Char_t778; tll_ptr Char_t779; tll_ptr Char_t780; tll_ptr Char_t781;
  tll_ptr Char_t782; tll_ptr Char_t783; tll_ptr Char_t784; tll_ptr Char_t785;
  tll_ptr Char_t816; tll_ptr Char_t817; tll_ptr Char_t818; tll_ptr Char_t819;
  tll_ptr Char_t820; tll_ptr Char_t828; tll_ptr Char_t829; tll_ptr Char_t837;
  tll_ptr Char_t838; tll_ptr Char_t839; tll_ptr Char_t840; tll_ptr Char_t841;
  tll_ptr Char_t842; tll_ptr Char_t843; tll_ptr Char_t844; tll_ptr Char_t845;
  tll_ptr Char_t857; tll_ptr Char_t858; tll_ptr Char_t859; tll_ptr Char_t860;
  tll_ptr Char_t861; tll_ptr Char_t862; tll_ptr Char_t863; tll_ptr Char_t864;
  tll_ptr EmptyString_t786; tll_ptr EmptyString_t821;
  tll_ptr EmptyString_t830; tll_ptr EmptyString_t846;
  tll_ptr EmptyString_t865; tll_ptr String_t787; tll_ptr String_t788;
  tll_ptr String_t789; tll_ptr String_t790; tll_ptr String_t791;
  tll_ptr String_t792; tll_ptr String_t793; tll_ptr String_t794;
  tll_ptr String_t795; tll_ptr String_t796; tll_ptr String_t797;
  tll_ptr String_t798; tll_ptr String_t799; tll_ptr String_t800;
  tll_ptr String_t801; tll_ptr String_t802; tll_ptr String_t803;
  tll_ptr String_t804; tll_ptr String_t805; tll_ptr String_t806;
  tll_ptr String_t807; tll_ptr String_t808; tll_ptr String_t809;
  tll_ptr String_t810; tll_ptr String_t811; tll_ptr String_t812;
  tll_ptr String_t813; tll_ptr String_t814; tll_ptr String_t822;
  tll_ptr String_t823; tll_ptr String_t824; tll_ptr String_t825;
  tll_ptr String_t826; tll_ptr String_t831; tll_ptr String_t832;
  tll_ptr String_t847; tll_ptr String_t848; tll_ptr String_t849;
  tll_ptr String_t850; tll_ptr String_t851; tll_ptr String_t852;
  tll_ptr String_t853; tll_ptr String_t854; tll_ptr String_t855;
  tll_ptr String_t866; tll_ptr String_t867; tll_ptr String_t868;
  tll_ptr String_t869; tll_ptr String_t870; tll_ptr String_t871;
  tll_ptr String_t872; tll_ptr String_t873; tll_ptr __v28708;
  tll_ptr __v28711; tll_ptr __v28720; tll_ptr __v28723; tll_ptr __v28724;
  tll_ptr ans_v28714; tll_ptr app_ret_t833; tll_ptr app_ret_t874;
  tll_ptr app_ret_t876; tll_ptr c_v28710; tll_ptr c_v28713; tll_ptr c_v28715;
  tll_ptr c_v28717; tll_ptr c_v28719; tll_ptr c_v28722;
  tll_ptr call_ret_t753; tll_ptr call_ret_t754; tll_ptr call_ret_t755;
  tll_ptr call_ret_t756; tll_ptr call_ret_t757; tll_ptr call_ret_t815;
  tll_ptr call_ret_t827; tll_ptr call_ret_t834; tll_ptr call_ret_t835;
  tll_ptr call_ret_t836; tll_ptr call_ret_t856; tll_ptr call_ret_t875;
  tll_ptr lower_v28709; tll_ptr pair_struct_t745; tll_ptr pair_struct_t747;
  tll_ptr pair_struct_t749; tll_ptr pf1_v28716; tll_ptr pf2_v28718;
  tll_ptr recv_msg_t741; tll_ptr recv_msg_t743; tll_ptr recv_msg_t751;
  tll_ptr repeat_v28721; tll_ptr switch_ret_t742; tll_ptr switch_ret_t744;
  tll_ptr switch_ret_t746; tll_ptr switch_ret_t748; tll_ptr switch_ret_t750;
  tll_ptr switch_ret_t752; tll_ptr upper_v28712;
  instr_recv(&recv_msg_t741, env[0]);
  __v28708 = recv_msg_t741;
  switch(((tll_node)__v28708)->tag) {
    case 0:
      lower_v28709 = ((tll_node)__v28708)->data[0];
      c_v28710 = ((tll_node)__v28708)->data[1];
      instr_free_struct(__v28708);
      instr_recv(&recv_msg_t743, c_v28710);
      __v28711 = recv_msg_t743;
      switch(((tll_node)__v28711)->tag) {
        case 0:
          upper_v28712 = ((tll_node)__v28711)->data[0];
          c_v28713 = ((tll_node)__v28711)->data[1];
          instr_free_struct(__v28711);
          instr_struct(&pair_struct_t745, 0, 2, 0, c_v28713);
          switch(((tll_node)pair_struct_t745)->tag) {
            case 0:
              ans_v28714 = ((tll_node)pair_struct_t745)->data[0];
              c_v28715 = ((tll_node)pair_struct_t745)->data[1];
              instr_free_struct(pair_struct_t745);
              instr_struct(&pair_struct_t747, 0, 2, 0, c_v28715);
              switch(((tll_node)pair_struct_t747)->tag) {
                case 0:
                  pf1_v28716 = ((tll_node)pair_struct_t747)->data[0];
                  c_v28717 = ((tll_node)pair_struct_t747)->data[1];
                  instr_free_struct(pair_struct_t747);
                  instr_struct(&pair_struct_t749, 0, 2, 0, c_v28717);
                  switch(((tll_node)pair_struct_t749)->tag) {
                    case 0:
                      pf2_v28718 = ((tll_node)pair_struct_t749)->data[0];
                      c_v28719 = ((tll_node)pair_struct_t749)->data[1];
                      instr_free_struct(pair_struct_t749);
                      instr_recv(&recv_msg_t751, c_v28719);
                      __v28720 = recv_msg_t751;
                      switch(((tll_node)__v28720)->tag) {
                        case 0:
                          repeat_v28721 = ((tll_node)__v28720)->data[0];
                          c_v28722 = ((tll_node)__v28720)->data[1];
                          instr_free_struct(__v28720);
                          instr_struct(&Char_t758, 4, 1, (tll_ptr)80);
                          instr_struct(&Char_t759, 4, 1, (tll_ptr)108);
                          instr_struct(&Char_t760, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t761, 4, 1, (tll_ptr)97);
                          instr_struct(&Char_t762, 4, 1, (tll_ptr)115);
                          instr_struct(&Char_t763, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t764, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t765, 4, 1, (tll_ptr)109);
                          instr_struct(&Char_t766, 4, 1, (tll_ptr)97);
                          instr_struct(&Char_t767, 4, 1, (tll_ptr)107);
                          instr_struct(&Char_t768, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t769, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t770, 4, 1, (tll_ptr)97);
                          instr_struct(&Char_t771, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t772, 4, 1, (tll_ptr)103);
                          instr_struct(&Char_t773, 4, 1, (tll_ptr)117);
                          instr_struct(&Char_t774, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t775, 4, 1, (tll_ptr)115);
                          instr_struct(&Char_t776, 4, 1, (tll_ptr)115);
                          instr_struct(&Char_t777, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t778, 4, 1, (tll_ptr)98);
                          instr_struct(&Char_t779, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t780, 4, 1, (tll_ptr)116);
                          instr_struct(&Char_t781, 4, 1, (tll_ptr)119);
                          instr_struct(&Char_t782, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t783, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t784, 4, 1, (tll_ptr)110);
                          instr_struct(&Char_t785, 4, 1, (tll_ptr)32);
                          instr_struct(&EmptyString_t786, 5, 0);
                          instr_struct(&String_t787, 6, 2,
                                       Char_t785, EmptyString_t786);
                          instr_struct(&String_t788, 6, 2,
                                       Char_t784, String_t787);
                          instr_struct(&String_t789, 6, 2,
                                       Char_t783, String_t788);
                          instr_struct(&String_t790, 6, 2,
                                       Char_t782, String_t789);
                          instr_struct(&String_t791, 6, 2,
                                       Char_t781, String_t790);
                          instr_struct(&String_t792, 6, 2,
                                       Char_t780, String_t791);
                          instr_struct(&String_t793, 6, 2,
                                       Char_t779, String_t792);
                          instr_struct(&String_t794, 6, 2,
                                       Char_t778, String_t793);
                          instr_struct(&String_t795, 6, 2,
                                       Char_t777, String_t794);
                          instr_struct(&String_t796, 6, 2,
                                       Char_t776, String_t795);
                          instr_struct(&String_t797, 6, 2,
                                       Char_t775, String_t796);
                          instr_struct(&String_t798, 6, 2,
                                       Char_t774, String_t797);
                          instr_struct(&String_t799, 6, 2,
                                       Char_t773, String_t798);
                          instr_struct(&String_t800, 6, 2,
                                       Char_t772, String_t799);
                          instr_struct(&String_t801, 6, 2,
                                       Char_t771, String_t800);
                          instr_struct(&String_t802, 6, 2,
                                       Char_t770, String_t801);
                          instr_struct(&String_t803, 6, 2,
                                       Char_t769, String_t802);
                          instr_struct(&String_t804, 6, 2,
                                       Char_t768, String_t803);
                          instr_struct(&String_t805, 6, 2,
                                       Char_t767, String_t804);
                          instr_struct(&String_t806, 6, 2,
                                       Char_t766, String_t805);
                          instr_struct(&String_t807, 6, 2,
                                       Char_t765, String_t806);
                          instr_struct(&String_t808, 6, 2,
                                       Char_t764, String_t807);
                          instr_struct(&String_t809, 6, 2,
                                       Char_t763, String_t808);
                          instr_struct(&String_t810, 6, 2,
                                       Char_t762, String_t809);
                          instr_struct(&String_t811, 6, 2,
                                       Char_t761, String_t810);
                          instr_struct(&String_t812, 6, 2,
                                       Char_t760, String_t811);
                          instr_struct(&String_t813, 6, 2,
                                       Char_t759, String_t812);
                          instr_struct(&String_t814, 6, 2,
                                       Char_t758, String_t813);
                          call_ret_t815 = string_of_nat_i37(lower_v28709);
                          call_ret_t757 = cats_i19(String_t814, call_ret_t815);
                          instr_struct(&Char_t816, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t817, 4, 1, (tll_ptr)97);
                          instr_struct(&Char_t818, 4, 1, (tll_ptr)110);
                          instr_struct(&Char_t819, 4, 1, (tll_ptr)100);
                          instr_struct(&Char_t820, 4, 1, (tll_ptr)32);
                          instr_struct(&EmptyString_t821, 5, 0);
                          instr_struct(&String_t822, 6, 2,
                                       Char_t820, EmptyString_t821);
                          instr_struct(&String_t823, 6, 2,
                                       Char_t819, String_t822);
                          instr_struct(&String_t824, 6, 2,
                                       Char_t818, String_t823);
                          instr_struct(&String_t825, 6, 2,
                                       Char_t817, String_t824);
                          instr_struct(&String_t826, 6, 2,
                                       Char_t816, String_t825);
                          call_ret_t756 = cats_i19(call_ret_t757, String_t826);
                          call_ret_t827 = string_of_nat_i37(upper_v28712);
                          call_ret_t755 = cats_i19(call_ret_t756,
                                                   call_ret_t827);
                          instr_struct(&Char_t828, 4, 1, (tll_ptr)46);
                          instr_struct(&Char_t829, 4, 1, (tll_ptr)10);
                          instr_struct(&EmptyString_t830, 5, 0);
                          instr_struct(&String_t831, 6, 2,
                                       Char_t829, EmptyString_t830);
                          instr_struct(&String_t832, 6, 2,
                                       Char_t828, String_t831);
                          call_ret_t754 = cats_i19(call_ret_t755, String_t832);
                          call_ret_t753 = print_i32(call_ret_t754);
                          instr_app(&app_ret_t833, call_ret_t753, 0);
                          instr_free_clo(call_ret_t753);
                          __v28723 = app_ret_t833;
                          instr_struct(&Char_t837, 4, 1, (tll_ptr)89);
                          instr_struct(&Char_t838, 4, 1, (tll_ptr)111);
                          instr_struct(&Char_t839, 4, 1, (tll_ptr)117);
                          instr_struct(&Char_t840, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t841, 4, 1, (tll_ptr)104);
                          instr_struct(&Char_t842, 4, 1, (tll_ptr)97);
                          instr_struct(&Char_t843, 4, 1, (tll_ptr)118);
                          instr_struct(&Char_t844, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t845, 4, 1, (tll_ptr)32);
                          instr_struct(&EmptyString_t846, 5, 0);
                          instr_struct(&String_t847, 6, 2,
                                       Char_t845, EmptyString_t846);
                          instr_struct(&String_t848, 6, 2,
                                       Char_t844, String_t847);
                          instr_struct(&String_t849, 6, 2,
                                       Char_t843, String_t848);
                          instr_struct(&String_t850, 6, 2,
                                       Char_t842, String_t849);
                          instr_struct(&String_t851, 6, 2,
                                       Char_t841, String_t850);
                          instr_struct(&String_t852, 6, 2,
                                       Char_t840, String_t851);
                          instr_struct(&String_t853, 6, 2,
                                       Char_t839, String_t852);
                          instr_struct(&String_t854, 6, 2,
                                       Char_t838, String_t853);
                          instr_struct(&String_t855, 6, 2,
                                       Char_t837, String_t854);
                          call_ret_t856 = string_of_nat_i37(repeat_v28721);
                          call_ret_t836 = cats_i19(String_t855, call_ret_t856);
                          instr_struct(&Char_t857, 4, 1, (tll_ptr)32);
                          instr_struct(&Char_t858, 4, 1, (tll_ptr)116);
                          instr_struct(&Char_t859, 4, 1, (tll_ptr)114);
                          instr_struct(&Char_t860, 4, 1, (tll_ptr)105);
                          instr_struct(&Char_t861, 4, 1, (tll_ptr)101);
                          instr_struct(&Char_t862, 4, 1, (tll_ptr)115);
                          instr_struct(&Char_t863, 4, 1, (tll_ptr)46);
                          instr_struct(&Char_t864, 4, 1, (tll_ptr)10);
                          instr_struct(&EmptyString_t865, 5, 0);
                          instr_struct(&String_t866, 6, 2,
                                       Char_t864, EmptyString_t865);
                          instr_struct(&String_t867, 6, 2,
                                       Char_t863, String_t866);
                          instr_struct(&String_t868, 6, 2,
                                       Char_t862, String_t867);
                          instr_struct(&String_t869, 6, 2,
                                       Char_t861, String_t868);
                          instr_struct(&String_t870, 6, 2,
                                       Char_t860, String_t869);
                          instr_struct(&String_t871, 6, 2,
                                       Char_t859, String_t870);
                          instr_struct(&String_t872, 6, 2,
                                       Char_t858, String_t871);
                          instr_struct(&String_t873, 6, 2,
                                       Char_t857, String_t872);
                          call_ret_t835 = cats_i19(call_ret_t836, String_t873);
                          call_ret_t834 = print_i32(call_ret_t835);
                          instr_app(&app_ret_t874, call_ret_t834, 0);
                          instr_free_clo(call_ret_t834);
                          __v28724 = app_ret_t874;
                          call_ret_t875 = player_loop_i48(0, repeat_v28721,
                                                          c_v28722);
                          instr_app(&app_ret_t876, call_ret_t875, 0);
                          instr_free_clo(call_ret_t875);
                          switch_ret_t752 = app_ret_t876;
                          break;
                      }
                      switch_ret_t750 = switch_ret_t752;
                      break;
                  }
                  switch_ret_t748 = switch_ret_t750;
                  break;
              }
              switch_ret_t746 = switch_ret_t748;
              break;
          }
          switch_ret_t744 = switch_ret_t746;
          break;
      }
      switch_ret_t742 = switch_ret_t744;
      break;
  }
  return switch_ret_t742;
}

tll_ptr player_i49(tll_ptr c_v28689) {
  tll_ptr lam_clo_t878;
  instr_clo(&lam_clo_t878, &lam_fun_t877, 1, c_v28689);
  return lam_clo_t878;
}

tll_ptr lam_fun_t880(tll_ptr c_v28725, tll_env env) {
  tll_ptr call_ret_t879;
  call_ret_t879 = player_i49(c_v28725);
  return call_ret_t879;
}

tll_ptr lam_fun_t893(tll_ptr __v28736, tll_env env) {
  tll_ptr __v28742; tll_ptr add_ret_t888; tll_ptr add_ret_t891;
  tll_ptr app_ret_t889; tll_ptr app_ret_t892; tll_ptr c_v28744;
  tll_ptr c_v28746; tll_ptr call_ret_t884; tll_ptr call_ret_t887;
  tll_ptr call_ret_t890; tll_ptr n_v28743; tll_ptr ord_v28745;
  tll_ptr recv_msg_t882; tll_ptr send_ch_t885; tll_ptr switch_ret_t883;
  tll_ptr switch_ret_t886;
  instr_recv(&recv_msg_t882, env[0]);
  __v28742 = recv_msg_t882;
  switch(((tll_node)__v28742)->tag) {
    case 0:
      n_v28743 = ((tll_node)__v28742)->data[0];
      c_v28744 = ((tll_node)__v28742)->data[1];
      instr_free_struct(__v28742);
      call_ret_t884 = comparen_i10(env[2], n_v28743);
      ord_v28745 = call_ret_t884;
      instr_send(&send_ch_t885, c_v28744, ord_v28745);
      c_v28746 = send_ch_t885;
      switch(((tll_node)ord_v28745)->tag) {
        case 3:
          switch_ret_t886 = 0;
          break;
        case 1:
          add_ret_t888 = env[1] - 1;
          call_ret_t887 = server_loop_i50(env[2], add_ret_t888, c_v28746);
          instr_app(&app_ret_t889, call_ret_t887, 0);
          switch_ret_t886 = app_ret_t889;
          break;
        case 2:
          add_ret_t891 = env[1] - 1;
          call_ret_t890 = server_loop_i50(env[2], add_ret_t891, c_v28746);
          instr_app(&app_ret_t892, call_ret_t890, 0);
          switch_ret_t886 = app_ret_t892;
          break;
      }
      switch_ret_t883 = switch_ret_t886;
      break;
  }
  return switch_ret_t883;
}

tll_ptr lam_fun_t895(tll_ptr c_v28729, tll_env env) {
  tll_ptr lam_clo_t894;
  instr_clo(&lam_clo_t894, &lam_fun_t893, 3, c_v28729, env[0], env[1]);
  return lam_clo_t894;
}

tll_ptr lam_fun_t897(tll_ptr __v28749, tll_env env) {
  
  
  return 0;
}

tll_ptr lam_fun_t899(tll_ptr c_v28747, tll_env env) {
  tll_ptr lam_clo_t898;
  instr_clo(&lam_clo_t898, &lam_fun_t897, 0);
  return lam_clo_t898;
}

tll_ptr server_loop_i50(tll_ptr ans_v28726, tll_ptr repeat_v28727, tll_ptr c_v28728) {
  tll_ptr app_ret_t902; tll_ptr ifte_ret_t901; tll_ptr lam_clo_t896;
  tll_ptr lam_clo_t900;
  if (repeat_v28727) {
    instr_clo(&lam_clo_t896, &lam_fun_t895, 2, repeat_v28727, ans_v28726);
    ifte_ret_t901 = lam_clo_t896;
  }
  else {
    instr_clo(&lam_clo_t900, &lam_fun_t899, 0);
    ifte_ret_t901 = lam_clo_t900;
  }
  instr_app(&app_ret_t902, ifte_ret_t901, c_v28728);
  return app_ret_t902;
}

tll_ptr lam_fun_t904(tll_ptr c_v28755, tll_env env) {
  tll_ptr call_ret_t903;
  call_ret_t903 = server_loop_i50(env[1], env[0], c_v28755);
  return call_ret_t903;
}

tll_ptr lam_fun_t906(tll_ptr repeat_v28753, tll_env env) {
  tll_ptr lam_clo_t905;
  instr_clo(&lam_clo_t905, &lam_fun_t904, 2, repeat_v28753, env[0]);
  return lam_clo_t905;
}

tll_ptr lam_fun_t908(tll_ptr ans_v28750, tll_env env) {
  tll_ptr lam_clo_t907;
  instr_clo(&lam_clo_t907, &lam_fun_t906, 1, ans_v28750);
  return lam_clo_t907;
}

tll_ptr lam_fun_t915(tll_ptr __v28757, tll_env env) {
  tll_ptr app_ret_t914; tll_ptr c_v28761; tll_ptr c_v28762; tll_ptr c_v28763;
  tll_ptr call_ret_t913; tll_ptr send_ch_t910; tll_ptr send_ch_t911;
  tll_ptr send_ch_t912;
  instr_send(&send_ch_t910, env[0], (tll_ptr)1);
  c_v28761 = send_ch_t910;
  instr_send(&send_ch_t911, c_v28761, (tll_ptr)128);
  c_v28762 = send_ch_t911;
  instr_send(&send_ch_t912, c_v28762, (tll_ptr)7);
  c_v28763 = send_ch_t912;
  call_ret_t913 = server_loop_i50((tll_ptr)71, (tll_ptr)7, c_v28763);
  instr_app(&app_ret_t914, call_ret_t913, 0);
  instr_free_clo(call_ret_t913);
  return app_ret_t914;
}

tll_ptr server_i51(tll_ptr c_v28756) {
  tll_ptr lam_clo_t916;
  instr_clo(&lam_clo_t916, &lam_fun_t915, 1, c_v28756);
  return lam_clo_t916;
}

tll_ptr lam_fun_t918(tll_ptr c_v28764, tll_env env) {
  tll_ptr call_ret_t917;
  call_ret_t917 = server_i51(c_v28764);
  return call_ret_t917;
}

tll_ptr fork_fun_t922(tll_env env) {
  tll_ptr app_ret_t921; tll_ptr call_ret_t920; tll_ptr fork_ret_t924;
  call_ret_t920 = server_i51(env[0]);
  instr_app(&app_ret_t921, call_ret_t920, 0);
  instr_free_clo(call_ret_t920);
  fork_ret_t924 = app_ret_t921;
  instr_free_thread(env);
  return fork_ret_t924;
}

tll_ptr fork_fun_t930(tll_env env) {
  tll_ptr __v28774; tll_ptr __v28777; tll_ptr app_ret_t928;
  tll_ptr c0_v28776; tll_ptr c0_v28778; tll_ptr c_v28775;
  tll_ptr call_ret_t927; tll_ptr fork_ret_t932; tll_ptr recv_msg_t925;
  tll_ptr send_ch_t929; tll_ptr switch_ret_t926;
  instr_recv(&recv_msg_t925, env[0]);
  __v28774 = recv_msg_t925;
  switch(((tll_node)__v28774)->tag) {
    case 0:
      c_v28775 = ((tll_node)__v28774)->data[0];
      c0_v28776 = ((tll_node)__v28774)->data[1];
      instr_free_struct(__v28774);
      call_ret_t927 = player_i49(c_v28775);
      instr_app(&app_ret_t928, call_ret_t927, 0);
      instr_free_clo(call_ret_t927);
      __v28777 = app_ret_t928;
      instr_send(&send_ch_t929, c0_v28776, 0);
      c0_v28778 = send_ch_t929;
      switch_ret_t926 = 0;
      break;
  }
  fork_ret_t932 = switch_ret_t926;
  instr_free_thread(env);
  return fork_ret_t932;
}

int main() {
  instr_init();
  tll_ptr Char_t265; tll_ptr Char_t268; tll_ptr Char_t271; tll_ptr Char_t274;
  tll_ptr Char_t277; tll_ptr Char_t280; tll_ptr Char_t283; tll_ptr Char_t286;
  tll_ptr Char_t289; tll_ptr Char_t292; tll_ptr EmptyString_t266;
  tll_ptr EmptyString_t269; tll_ptr EmptyString_t272;
  tll_ptr EmptyString_t275; tll_ptr EmptyString_t278;
  tll_ptr EmptyString_t281; tll_ptr EmptyString_t284;
  tll_ptr EmptyString_t287; tll_ptr EmptyString_t290;
  tll_ptr EmptyString_t293; tll_ptr String_t267; tll_ptr String_t270;
  tll_ptr String_t273; tll_ptr String_t276; tll_ptr String_t279;
  tll_ptr String_t282; tll_ptr String_t285; tll_ptr String_t288;
  tll_ptr String_t291; tll_ptr String_t294; tll_ptr __v28780;
  tll_ptr __v28781; tll_ptr c0_v28767; tll_ptr c0_v28779; tll_ptr c0_v28782;
  tll_ptr c_v28765; tll_ptr close_tmp_t936; tll_ptr consUU_t296;
  tll_ptr consUU_t297; tll_ptr consUU_t298; tll_ptr consUU_t299;
  tll_ptr consUU_t300; tll_ptr consUU_t301; tll_ptr consUU_t302;
  tll_ptr consUU_t303; tll_ptr consUU_t304; tll_ptr consUU_t305;
  tll_ptr fork_ch_t923; tll_ptr fork_ch_t931; tll_ptr lam_clo_t104;
  tll_ptr lam_clo_t110; tll_ptr lam_clo_t118; tll_ptr lam_clo_t12;
  tll_ptr lam_clo_t126; tll_ptr lam_clo_t134; tll_ptr lam_clo_t140;
  tll_ptr lam_clo_t151; tll_ptr lam_clo_t16; tll_ptr lam_clo_t167;
  tll_ptr lam_clo_t180; tll_ptr lam_clo_t193; tll_ptr lam_clo_t206;
  tll_ptr lam_clo_t216; tll_ptr lam_clo_t226; tll_ptr lam_clo_t236;
  tll_ptr lam_clo_t246; tll_ptr lam_clo_t255; tll_ptr lam_clo_t264;
  tll_ptr lam_clo_t28; tll_ptr lam_clo_t319; tll_ptr lam_clo_t324;
  tll_ptr lam_clo_t334; tll_ptr lam_clo_t34; tll_ptr lam_clo_t378;
  tll_ptr lam_clo_t391; tll_ptr lam_clo_t395; tll_ptr lam_clo_t40;
  tll_ptr lam_clo_t46; tll_ptr lam_clo_t469; tll_ptr lam_clo_t52;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t6; tll_ptr lam_clo_t72;
  tll_ptr lam_clo_t740; tll_ptr lam_clo_t77; tll_ptr lam_clo_t83;
  tll_ptr lam_clo_t881; tll_ptr lam_clo_t909; tll_ptr lam_clo_t919;
  tll_ptr lam_clo_t92; tll_ptr lam_clo_t98; tll_ptr nilUU_t295;
  tll_ptr recv_msg_t934; tll_ptr send_ch_t933; tll_ptr switch_ret_t935;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i61 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i62 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i63 = lam_clo_t16;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  comparebclo_i64 = lam_clo_t28;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 0);
  ltenclo_i65 = lam_clo_t34;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 0);
  gtenclo_i66 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  ltnclo_i67 = lam_clo_t46;
  instr_clo(&lam_clo_t52, &lam_fun_t51, 0);
  gtnclo_i68 = lam_clo_t52;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  eqnclo_i69 = lam_clo_t58;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  comparenclo_i70 = lam_clo_t72;
  instr_clo(&lam_clo_t77, &lam_fun_t76, 0);
  predclo_i71 = lam_clo_t77;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i72 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i73 = lam_clo_t92;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  mulnclo_i74 = lam_clo_t98;
  instr_clo(&lam_clo_t104, &lam_fun_t103, 0);
  divnclo_i75 = lam_clo_t104;
  instr_clo(&lam_clo_t110, &lam_fun_t109, 0);
  modnclo_i76 = lam_clo_t110;
  instr_clo(&lam_clo_t118, &lam_fun_t117, 0);
  eqcclo_i77 = lam_clo_t118;
  instr_clo(&lam_clo_t126, &lam_fun_t125, 0);
  comparecclo_i78 = lam_clo_t126;
  instr_clo(&lam_clo_t134, &lam_fun_t133, 0);
  catsclo_i79 = lam_clo_t134;
  instr_clo(&lam_clo_t140, &lam_fun_t139, 0);
  strlenclo_i80 = lam_clo_t140;
  instr_clo(&lam_clo_t151, &lam_fun_t150, 0);
  eqsclo_i81 = lam_clo_t151;
  instr_clo(&lam_clo_t167, &lam_fun_t166, 0);
  comparesclo_i82 = lam_clo_t167;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 0);
  lenUUclo_i83 = lam_clo_t180;
  instr_clo(&lam_clo_t193, &lam_fun_t192, 0);
  lenULclo_i84 = lam_clo_t193;
  instr_clo(&lam_clo_t206, &lam_fun_t205, 0);
  lenLLclo_i85 = lam_clo_t206;
  instr_clo(&lam_clo_t216, &lam_fun_t215, 0);
  appendUUclo_i86 = lam_clo_t216;
  instr_clo(&lam_clo_t226, &lam_fun_t225, 0);
  appendULclo_i87 = lam_clo_t226;
  instr_clo(&lam_clo_t236, &lam_fun_t235, 0);
  appendLLclo_i88 = lam_clo_t236;
  instr_clo(&lam_clo_t246, &lam_fun_t245, 0);
  readlineclo_i89 = lam_clo_t246;
  instr_clo(&lam_clo_t255, &lam_fun_t254, 0);
  printclo_i90 = lam_clo_t255;
  instr_clo(&lam_clo_t264, &lam_fun_t263, 0);
  prerrclo_i91 = lam_clo_t264;
  instr_struct(&Char_t265, 4, 1, (tll_ptr)48);
  instr_struct(&EmptyString_t266, 5, 0);
  instr_struct(&String_t267, 6, 2, Char_t265, EmptyString_t266);
  instr_struct(&Char_t268, 4, 1, (tll_ptr)49);
  instr_struct(&EmptyString_t269, 5, 0);
  instr_struct(&String_t270, 6, 2, Char_t268, EmptyString_t269);
  instr_struct(&Char_t271, 4, 1, (tll_ptr)50);
  instr_struct(&EmptyString_t272, 5, 0);
  instr_struct(&String_t273, 6, 2, Char_t271, EmptyString_t272);
  instr_struct(&Char_t274, 4, 1, (tll_ptr)51);
  instr_struct(&EmptyString_t275, 5, 0);
  instr_struct(&String_t276, 6, 2, Char_t274, EmptyString_t275);
  instr_struct(&Char_t277, 4, 1, (tll_ptr)52);
  instr_struct(&EmptyString_t278, 5, 0);
  instr_struct(&String_t279, 6, 2, Char_t277, EmptyString_t278);
  instr_struct(&Char_t280, 4, 1, (tll_ptr)53);
  instr_struct(&EmptyString_t281, 5, 0);
  instr_struct(&String_t282, 6, 2, Char_t280, EmptyString_t281);
  instr_struct(&Char_t283, 4, 1, (tll_ptr)54);
  instr_struct(&EmptyString_t284, 5, 0);
  instr_struct(&String_t285, 6, 2, Char_t283, EmptyString_t284);
  instr_struct(&Char_t286, 4, 1, (tll_ptr)55);
  instr_struct(&EmptyString_t287, 5, 0);
  instr_struct(&String_t288, 6, 2, Char_t286, EmptyString_t287);
  instr_struct(&Char_t289, 4, 1, (tll_ptr)56);
  instr_struct(&EmptyString_t290, 5, 0);
  instr_struct(&String_t291, 6, 2, Char_t289, EmptyString_t290);
  instr_struct(&Char_t292, 4, 1, (tll_ptr)57);
  instr_struct(&EmptyString_t293, 5, 0);
  instr_struct(&String_t294, 6, 2, Char_t292, EmptyString_t293);
  instr_struct(&nilUU_t295, 25, 0);
  instr_struct(&consUU_t296, 26, 2, String_t294, nilUU_t295);
  instr_struct(&consUU_t297, 26, 2, String_t291, consUU_t296);
  instr_struct(&consUU_t298, 26, 2, String_t288, consUU_t297);
  instr_struct(&consUU_t299, 26, 2, String_t285, consUU_t298);
  instr_struct(&consUU_t300, 26, 2, String_t282, consUU_t299);
  instr_struct(&consUU_t301, 26, 2, String_t279, consUU_t300);
  instr_struct(&consUU_t302, 26, 2, String_t276, consUU_t301);
  instr_struct(&consUU_t303, 26, 2, String_t273, consUU_t302);
  instr_struct(&consUU_t304, 26, 2, String_t270, consUU_t303);
  instr_struct(&consUU_t305, 26, 2, String_t267, consUU_t304);
  digits_i34 = consUU_t305;
  instr_clo(&lam_clo_t319, &lam_fun_t318, 0);
  get_atclo_i92 = lam_clo_t319;
  instr_clo(&lam_clo_t324, &lam_fun_t323, 0);
  string_of_digitclo_i93 = lam_clo_t324;
  instr_clo(&lam_clo_t334, &lam_fun_t333, 0);
  string_of_natclo_i94 = lam_clo_t334;
  instr_clo(&lam_clo_t378, &lam_fun_t377, 0);
  digit_of_charclo_i95 = lam_clo_t378;
  instr_clo(&lam_clo_t391, &lam_fun_t390, 0);
  nat_of_string_loopclo_i96 = lam_clo_t391;
  instr_clo(&lam_clo_t395, &lam_fun_t394, 0);
  nat_of_stringclo_i97 = lam_clo_t395;
  instr_clo(&lam_clo_t469, &lam_fun_t468, 0);
  read_natclo_i98 = lam_clo_t469;
  instr_clo(&lam_clo_t740, &lam_fun_t739, 0);
  player_loopclo_i99 = lam_clo_t740;
  instr_clo(&lam_clo_t881, &lam_fun_t880, 0);
  playerclo_i100 = lam_clo_t881;
  instr_clo(&lam_clo_t909, &lam_fun_t908, 0);
  server_loopclo_i101 = lam_clo_t909;
  instr_clo(&lam_clo_t919, &lam_fun_t918, 0);
  serverclo_i102 = lam_clo_t919;
  instr_fork(&fork_ch_t923, &fork_fun_t922, 0);
  c_v28765 = fork_ch_t923;
  instr_fork(&fork_ch_t931, &fork_fun_t930, 0);
  c0_v28767 = fork_ch_t931;
  instr_send(&send_ch_t933, c0_v28767, c_v28765);
  c0_v28779 = send_ch_t933;
  instr_recv(&recv_msg_t934, c0_v28779);
  __v28780 = recv_msg_t934;
  switch(((tll_node)__v28780)->tag) {
    case 0:
      __v28781 = ((tll_node)__v28780)->data[0];
      c0_v28782 = ((tll_node)__v28780)->data[1];
      instr_free_struct(__v28780);
      instr_close(&close_tmp_t936, c0_v28782);
      switch_ret_t935 = close_tmp_t936;
      break;
  }
  return 0;
}

