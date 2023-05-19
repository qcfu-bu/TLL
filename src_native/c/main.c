#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v88471, tll_ptr b2_v88472);
tll_ptr orb_i2(tll_ptr b1_v88476, tll_ptr b2_v88477);
tll_ptr notb_i3(tll_ptr b_v88481);
tll_ptr compareb_i4(tll_ptr b1_v88483, tll_ptr b2_v88484);
tll_ptr lten_i5(tll_ptr x_v88488, tll_ptr y_v88489);
tll_ptr ltn_i6(tll_ptr x_v88493, tll_ptr y_v88494);
tll_ptr gten_i7(tll_ptr x_v88498, tll_ptr y_v88499);
tll_ptr gtn_i8(tll_ptr x_v88503, tll_ptr y_v88504);
tll_ptr eqn_i9(tll_ptr x_v88508, tll_ptr y_v88509);
tll_ptr comparen_i10(tll_ptr n1_v88513, tll_ptr n2_v88514);
tll_ptr pred_i11(tll_ptr x_v88518);
tll_ptr addn_i12(tll_ptr x_v88520, tll_ptr y_v88521);
tll_ptr subn_i13(tll_ptr x_v88525, tll_ptr y_v88526);
tll_ptr muln_i14(tll_ptr x_v88530, tll_ptr y_v88531);
tll_ptr divn_i15(tll_ptr x_v88535, tll_ptr y_v88536);
tll_ptr modn_i16(tll_ptr x_v88540, tll_ptr y_v88541);
tll_ptr eqc_i17(tll_ptr c1_v88545, tll_ptr c2_v88546);
tll_ptr comparec_i18(tll_ptr c1_v88552, tll_ptr c2_v88553);
tll_ptr cats_i19(tll_ptr s1_v88559, tll_ptr s2_v88560);
tll_ptr strlen_i20(tll_ptr s_v88566);
tll_ptr eqs_i21(tll_ptr s1_v88570, tll_ptr s2_v88571);
tll_ptr compares_i22(tll_ptr s1_v88581, tll_ptr s2_v88582);
tll_ptr and_thenUUU_i59(tll_ptr A_v88592, tll_ptr B_v88593, tll_ptr opt_v88594, tll_ptr f_v88595);
tll_ptr and_thenUUL_i58(tll_ptr A_v88607, tll_ptr B_v88608, tll_ptr opt_v88609, tll_ptr f_v88610);
tll_ptr and_thenULU_i57(tll_ptr A_v88622, tll_ptr B_v88623, tll_ptr opt_v88624, tll_ptr f_v88625);
tll_ptr and_thenULL_i56(tll_ptr A_v88637, tll_ptr B_v88638, tll_ptr opt_v88639, tll_ptr f_v88640);
tll_ptr and_thenLUL_i54(tll_ptr A_v88652, tll_ptr B_v88653, tll_ptr opt_v88654, tll_ptr f_v88655);
tll_ptr and_thenLLL_i52(tll_ptr A_v88667, tll_ptr B_v88668, tll_ptr opt_v88669, tll_ptr f_v88670);
tll_ptr lenUU_i67(tll_ptr A_v88682, tll_ptr xs_v88683);
tll_ptr lenUL_i66(tll_ptr A_v88691, tll_ptr xs_v88692);
tll_ptr lenLL_i64(tll_ptr A_v88700, tll_ptr xs_v88701);
tll_ptr appendUU_i71(tll_ptr A_v88709, tll_ptr xs_v88710, tll_ptr ys_v88711);
tll_ptr appendUL_i70(tll_ptr A_v88720, tll_ptr xs_v88721, tll_ptr ys_v88722);
tll_ptr appendLL_i68(tll_ptr A_v88731, tll_ptr xs_v88732, tll_ptr ys_v88733);
tll_ptr readline_i33(tll_ptr __v88742);
tll_ptr print_i34(tll_ptr s_v88757);
tll_ptr prerr_i35(tll_ptr s_v88768);
tll_ptr get_at_i37(tll_ptr A_v88779, tll_ptr n_v88780, tll_ptr xs_v88781, tll_ptr a_v88782);
tll_ptr string_of_digit_i38(tll_ptr n_v88797);
tll_ptr string_of_nat_i39(tll_ptr n_v88799);
tll_ptr digit_of_char_i40(tll_ptr c_v88803);
tll_ptr nat_of_string_loop_i41(tll_ptr s_v88805, tll_ptr acc_v88806);
tll_ptr nat_of_string_i42(tll_ptr s_v88813);
tll_ptr splitU_i73(tll_ptr zs_v88815);
tll_ptr splitL_i72(tll_ptr zs_v88824);
tll_ptr mergeU_i75(tll_ptr xs_v88833, tll_ptr ys_v88834);
tll_ptr mergeL_i74(tll_ptr xs_v88842, tll_ptr ys_v88843);
tll_ptr msortU_i77(tll_ptr zs_v88851);
tll_ptr msortL_i76(tll_ptr zs_v88860);
tll_ptr cmsort_workerU_i81(tll_ptr n_v88869, tll_ptr zs_v88870, tll_ptr c_v88871);
tll_ptr cmsort_workerL_i80(tll_ptr n_v88932, tll_ptr zs_v88933, tll_ptr c_v88934);
tll_ptr cmsortU_i83(tll_ptr zs_v88995);
tll_ptr cmsortL_i82(tll_ptr zs_v89010);
tll_ptr mkListU_i85(tll_ptr n_v89025);
tll_ptr mkListL_i84(tll_ptr n_v89027);
tll_ptr free_i50(tll_ptr A_v89029, tll_ptr ls_v89030);

tll_ptr addnclo_i97;
tll_ptr and_thenLLLclo_i113;
tll_ptr and_thenLULclo_i112;
tll_ptr and_thenULLclo_i111;
tll_ptr and_thenULUclo_i110;
tll_ptr and_thenUULclo_i109;
tll_ptr and_thenUUUclo_i108;
tll_ptr andbclo_i86;
tll_ptr appendLLclo_i119;
tll_ptr appendULclo_i118;
tll_ptr appendUUclo_i117;
tll_ptr catsclo_i104;
tll_ptr cmsortLclo_i138;
tll_ptr cmsortUclo_i137;
tll_ptr cmsort_workerLclo_i136;
tll_ptr cmsort_workerUclo_i135;
tll_ptr comparebclo_i89;
tll_ptr comparecclo_i103;
tll_ptr comparenclo_i95;
tll_ptr comparesclo_i107;
tll_ptr digit_of_charclo_i126;
tll_ptr digits_i36;
tll_ptr divnclo_i100;
tll_ptr eqcclo_i102;
tll_ptr eqnclo_i94;
tll_ptr eqsclo_i106;
tll_ptr freeclo_i141;
tll_ptr get_atclo_i123;
tll_ptr gtenclo_i92;
tll_ptr gtnclo_i93;
tll_ptr lenLLclo_i116;
tll_ptr lenULclo_i115;
tll_ptr lenUUclo_i114;
tll_ptr ltenclo_i90;
tll_ptr ltnclo_i91;
tll_ptr mergeLclo_i132;
tll_ptr mergeUclo_i131;
tll_ptr mkListLclo_i140;
tll_ptr mkListUclo_i139;
tll_ptr modnclo_i101;
tll_ptr msortLclo_i134;
tll_ptr msortUclo_i133;
tll_ptr mulnclo_i99;
tll_ptr nat_of_string_loopclo_i127;
tll_ptr nat_of_stringclo_i128;
tll_ptr notbclo_i88;
tll_ptr orbclo_i87;
tll_ptr predclo_i96;
tll_ptr prerrclo_i122;
tll_ptr printclo_i121;
tll_ptr readlineclo_i120;
tll_ptr splitLclo_i130;
tll_ptr splitUclo_i129;
tll_ptr string_of_digitclo_i124;
tll_ptr string_of_natclo_i125;
tll_ptr strlenclo_i105;
tll_ptr subnclo_i98;

tll_ptr andb_i1(tll_ptr b1_v88471, tll_ptr b2_v88472) {
  tll_ptr ifte_ret_t1;
  if (b1_v88471) {
    ifte_ret_t1 = b2_v88472;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v88475, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v88475);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v88473, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v88473);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v88476, tll_ptr b2_v88477) {
  tll_ptr ifte_ret_t7;
  if (b1_v88476) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v88477;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v88480, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v88480);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v88478, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v88478);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v88481) {
  tll_ptr ifte_ret_t13;
  if (b_v88481) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v88482, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v88482);
  return call_ret_t14;
}

tll_ptr compareb_i4(tll_ptr b1_v88483, tll_ptr b2_v88484) {
  tll_ptr EQ_t17; tll_ptr EQ_t21; tll_ptr GT_t18; tll_ptr LT_t20;
  tll_ptr ifte_ret_t19; tll_ptr ifte_ret_t22; tll_ptr ifte_ret_t23;
  if (b1_v88483) {
    if (b2_v88484) {
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
    if (b2_v88484) {
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

tll_ptr lam_fun_t25(tll_ptr b2_v88487, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = compareb_i4(env[0], b2_v88487);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr b1_v88485, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, b1_v88485);
  return lam_clo_t26;
}

tll_ptr lten_i5(tll_ptr x_v88488, tll_ptr y_v88489) {
  tll_ptr lten_ret_t29;
  instr_lten(&lten_ret_t29, x_v88488, y_v88489);
  return lten_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v88492, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = lten_i5(env[0], y_v88492);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v88490, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v88490);
  return lam_clo_t32;
}

tll_ptr ltn_i6(tll_ptr x_v88493, tll_ptr y_v88494) {
  tll_ptr ltn_ret_t35;
  instr_ltn(&ltn_ret_t35, x_v88493, y_v88494);
  return ltn_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v88497, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = ltn_i6(env[0], y_v88497);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v88495, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v88495);
  return lam_clo_t38;
}

tll_ptr gten_i7(tll_ptr x_v88498, tll_ptr y_v88499) {
  tll_ptr gten_ret_t41;
  instr_gten(&gten_ret_t41, x_v88498, y_v88499);
  return gten_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v88502, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = gten_i7(env[0], y_v88502);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v88500, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v88500);
  return lam_clo_t44;
}

tll_ptr gtn_i8(tll_ptr x_v88503, tll_ptr y_v88504) {
  tll_ptr gtn_ret_t47;
  instr_gtn(&gtn_ret_t47, x_v88503, y_v88504);
  return gtn_ret_t47;
}

tll_ptr lam_fun_t49(tll_ptr y_v88507, tll_env env) {
  tll_ptr call_ret_t48;
  call_ret_t48 = gtn_i8(env[0], y_v88507);
  return call_ret_t48;
}

tll_ptr lam_fun_t51(tll_ptr x_v88505, tll_env env) {
  tll_ptr lam_clo_t50;
  instr_clo(&lam_clo_t50, &lam_fun_t49, 1, x_v88505);
  return lam_clo_t50;
}

tll_ptr eqn_i9(tll_ptr x_v88508, tll_ptr y_v88509) {
  tll_ptr eqn_ret_t53;
  instr_eqn(&eqn_ret_t53, x_v88508, y_v88509);
  return eqn_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v88512, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = eqn_i9(env[0], y_v88512);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v88510, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v88510);
  return lam_clo_t56;
}

tll_ptr comparen_i10(tll_ptr n1_v88513, tll_ptr n2_v88514) {
  tll_ptr EQ_t65; tll_ptr GT_t62; tll_ptr LT_t64; tll_ptr add_ret_t60;
  tll_ptr add_ret_t61; tll_ptr call_ret_t59; tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t66; tll_ptr ifte_ret_t67;
  if (n1_v88513) {
    if (n2_v88514) {
      add_ret_t60 = n1_v88513 - 1;
      add_ret_t61 = n2_v88514 - 1;
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
    if (n2_v88514) {
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

tll_ptr lam_fun_t69(tll_ptr n2_v88517, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = comparen_i10(env[0], n2_v88517);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr n1_v88515, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, n1_v88515);
  return lam_clo_t70;
}

tll_ptr pred_i11(tll_ptr x_v88518) {
  tll_ptr add_ret_t73; tll_ptr ifte_ret_t74;
  if (x_v88518) {
    add_ret_t73 = x_v88518 - 1;
    ifte_ret_t74 = add_ret_t73;
  }
  else {
    ifte_ret_t74 = (tll_ptr)0;
  }
  return ifte_ret_t74;
}

tll_ptr lam_fun_t76(tll_ptr x_v88519, tll_env env) {
  tll_ptr call_ret_t75;
  call_ret_t75 = pred_i11(x_v88519);
  return call_ret_t75;
}

tll_ptr addn_i12(tll_ptr x_v88520, tll_ptr y_v88521) {
  tll_ptr addn_ret_t78;
  instr_addn(&addn_ret_t78, x_v88520, y_v88521);
  return addn_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v88524, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i12(env[0], y_v88524);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v88522, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v88522);
  return lam_clo_t81;
}

tll_ptr subn_i13(tll_ptr x_v88525, tll_ptr y_v88526) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v88526) {
    call_ret_t85 = pred_i11(x_v88525);
    add_ret_t86 = y_v88526 - 1;
    call_ret_t84 = subn_i13(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v88525;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v88529, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i13(env[0], y_v88529);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v88527, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v88527);
  return lam_clo_t90;
}

tll_ptr muln_i14(tll_ptr x_v88530, tll_ptr y_v88531) {
  tll_ptr muln_ret_t93;
  instr_muln(&muln_ret_t93, x_v88530, y_v88531);
  return muln_ret_t93;
}

tll_ptr lam_fun_t95(tll_ptr y_v88534, tll_env env) {
  tll_ptr call_ret_t94;
  call_ret_t94 = muln_i14(env[0], y_v88534);
  return call_ret_t94;
}

tll_ptr lam_fun_t97(tll_ptr x_v88532, tll_env env) {
  tll_ptr lam_clo_t96;
  instr_clo(&lam_clo_t96, &lam_fun_t95, 1, x_v88532);
  return lam_clo_t96;
}

tll_ptr divn_i15(tll_ptr x_v88535, tll_ptr y_v88536) {
  tll_ptr divn_ret_t99;
  instr_divn(&divn_ret_t99, x_v88535, y_v88536);
  return divn_ret_t99;
}

tll_ptr lam_fun_t101(tll_ptr y_v88539, tll_env env) {
  tll_ptr call_ret_t100;
  call_ret_t100 = divn_i15(env[0], y_v88539);
  return call_ret_t100;
}

tll_ptr lam_fun_t103(tll_ptr x_v88537, tll_env env) {
  tll_ptr lam_clo_t102;
  instr_clo(&lam_clo_t102, &lam_fun_t101, 1, x_v88537);
  return lam_clo_t102;
}

tll_ptr modn_i16(tll_ptr x_v88540, tll_ptr y_v88541) {
  tll_ptr modn_ret_t105;
  instr_modn(&modn_ret_t105, x_v88540, y_v88541);
  return modn_ret_t105;
}

tll_ptr lam_fun_t107(tll_ptr y_v88544, tll_env env) {
  tll_ptr call_ret_t106;
  call_ret_t106 = modn_i16(env[0], y_v88544);
  return call_ret_t106;
}

tll_ptr lam_fun_t109(tll_ptr x_v88542, tll_env env) {
  tll_ptr lam_clo_t108;
  instr_clo(&lam_clo_t108, &lam_fun_t107, 1, x_v88542);
  return lam_clo_t108;
}

tll_ptr eqc_i17(tll_ptr c1_v88545, tll_ptr c2_v88546) {
  tll_ptr call_ret_t113; tll_ptr n1_v88547; tll_ptr n2_v88548;
  tll_ptr switch_ret_t111; tll_ptr switch_ret_t112;
  switch(((tll_node)c1_v88545)->tag) {
    case 5:
      n1_v88547 = ((tll_node)c1_v88545)->data[0];
      switch(((tll_node)c2_v88546)->tag) {
        case 5:
          n2_v88548 = ((tll_node)c2_v88546)->data[0];
          call_ret_t113 = eqn_i9(n1_v88547, n2_v88548);
          switch_ret_t112 = call_ret_t113;
          break;
      }
      switch_ret_t111 = switch_ret_t112;
      break;
  }
  return switch_ret_t111;
}

tll_ptr lam_fun_t115(tll_ptr c2_v88551, tll_env env) {
  tll_ptr call_ret_t114;
  call_ret_t114 = eqc_i17(env[0], c2_v88551);
  return call_ret_t114;
}

tll_ptr lam_fun_t117(tll_ptr c1_v88549, tll_env env) {
  tll_ptr lam_clo_t116;
  instr_clo(&lam_clo_t116, &lam_fun_t115, 1, c1_v88549);
  return lam_clo_t116;
}

tll_ptr comparec_i18(tll_ptr c1_v88552, tll_ptr c2_v88553) {
  tll_ptr call_ret_t121; tll_ptr n1_v88554; tll_ptr n2_v88555;
  tll_ptr switch_ret_t119; tll_ptr switch_ret_t120;
  switch(((tll_node)c1_v88552)->tag) {
    case 5:
      n1_v88554 = ((tll_node)c1_v88552)->data[0];
      switch(((tll_node)c2_v88553)->tag) {
        case 5:
          n2_v88555 = ((tll_node)c2_v88553)->data[0];
          call_ret_t121 = comparen_i10(n1_v88554, n2_v88555);
          switch_ret_t120 = call_ret_t121;
          break;
      }
      switch_ret_t119 = switch_ret_t120;
      break;
  }
  return switch_ret_t119;
}

tll_ptr lam_fun_t123(tll_ptr c2_v88558, tll_env env) {
  tll_ptr call_ret_t122;
  call_ret_t122 = comparec_i18(env[0], c2_v88558);
  return call_ret_t122;
}

tll_ptr lam_fun_t125(tll_ptr c1_v88556, tll_env env) {
  tll_ptr lam_clo_t124;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 1, c1_v88556);
  return lam_clo_t124;
}

tll_ptr cats_i19(tll_ptr s1_v88559, tll_ptr s2_v88560) {
  tll_ptr String_t129; tll_ptr c_v88561; tll_ptr call_ret_t128;
  tll_ptr s1_v88562; tll_ptr switch_ret_t127;
  switch(((tll_node)s1_v88559)->tag) {
    case 6:
      switch_ret_t127 = s2_v88560;
      break;
    case 7:
      c_v88561 = ((tll_node)s1_v88559)->data[0];
      s1_v88562 = ((tll_node)s1_v88559)->data[1];
      call_ret_t128 = cats_i19(s1_v88562, s2_v88560);
      instr_struct(&String_t129, 7, 2, c_v88561, call_ret_t128);
      switch_ret_t127 = String_t129;
      break;
  }
  return switch_ret_t127;
}

tll_ptr lam_fun_t131(tll_ptr s2_v88565, tll_env env) {
  tll_ptr call_ret_t130;
  call_ret_t130 = cats_i19(env[0], s2_v88565);
  return call_ret_t130;
}

tll_ptr lam_fun_t133(tll_ptr s1_v88563, tll_env env) {
  tll_ptr lam_clo_t132;
  instr_clo(&lam_clo_t132, &lam_fun_t131, 1, s1_v88563);
  return lam_clo_t132;
}

tll_ptr strlen_i20(tll_ptr s_v88566) {
  tll_ptr __v88567; tll_ptr add_ret_t137; tll_ptr call_ret_t136;
  tll_ptr s_v88568; tll_ptr switch_ret_t135;
  switch(((tll_node)s_v88566)->tag) {
    case 6:
      switch_ret_t135 = (tll_ptr)0;
      break;
    case 7:
      __v88567 = ((tll_node)s_v88566)->data[0];
      s_v88568 = ((tll_node)s_v88566)->data[1];
      call_ret_t136 = strlen_i20(s_v88568);
      add_ret_t137 = call_ret_t136 + 1;
      switch_ret_t135 = add_ret_t137;
      break;
  }
  return switch_ret_t135;
}

tll_ptr lam_fun_t139(tll_ptr s_v88569, tll_env env) {
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i20(s_v88569);
  return call_ret_t138;
}

tll_ptr eqs_i21(tll_ptr s1_v88570, tll_ptr s2_v88571) {
  tll_ptr __v88572; tll_ptr __v88573; tll_ptr c1_v88574; tll_ptr c2_v88576;
  tll_ptr call_ret_t144; tll_ptr call_ret_t145; tll_ptr call_ret_t146;
  tll_ptr s1_v88575; tll_ptr s2_v88577; tll_ptr switch_ret_t141;
  tll_ptr switch_ret_t142; tll_ptr switch_ret_t143;
  switch(((tll_node)s1_v88570)->tag) {
    case 6:
      switch(((tll_node)s2_v88571)->tag) {
        case 6:
          switch_ret_t142 = (tll_ptr)1;
          break;
        case 7:
          __v88572 = ((tll_node)s2_v88571)->data[0];
          __v88573 = ((tll_node)s2_v88571)->data[1];
          switch_ret_t142 = (tll_ptr)0;
          break;
      }
      switch_ret_t141 = switch_ret_t142;
      break;
    case 7:
      c1_v88574 = ((tll_node)s1_v88570)->data[0];
      s1_v88575 = ((tll_node)s1_v88570)->data[1];
      switch(((tll_node)s2_v88571)->tag) {
        case 6:
          switch_ret_t143 = (tll_ptr)0;
          break;
        case 7:
          c2_v88576 = ((tll_node)s2_v88571)->data[0];
          s2_v88577 = ((tll_node)s2_v88571)->data[1];
          call_ret_t145 = eqc_i17(c1_v88574, c2_v88576);
          call_ret_t146 = eqs_i21(s1_v88575, s2_v88577);
          call_ret_t144 = andb_i1(call_ret_t145, call_ret_t146);
          switch_ret_t143 = call_ret_t144;
          break;
      }
      switch_ret_t141 = switch_ret_t143;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t148(tll_ptr s2_v88580, tll_env env) {
  tll_ptr call_ret_t147;
  call_ret_t147 = eqs_i21(env[0], s2_v88580);
  return call_ret_t147;
}

tll_ptr lam_fun_t150(tll_ptr s1_v88578, tll_env env) {
  tll_ptr lam_clo_t149;
  instr_clo(&lam_clo_t149, &lam_fun_t148, 1, s1_v88578);
  return lam_clo_t149;
}

tll_ptr compares_i22(tll_ptr s1_v88581, tll_ptr s2_v88582) {
  tll_ptr EQ_t154; tll_ptr GT_t157; tll_ptr GT_t162; tll_ptr LT_t155;
  tll_ptr LT_t161; tll_ptr __v88583; tll_ptr __v88584; tll_ptr c1_v88585;
  tll_ptr c2_v88587; tll_ptr call_ret_t158; tll_ptr call_ret_t160;
  tll_ptr s1_v88586; tll_ptr s2_v88588; tll_ptr switch_ret_t152;
  tll_ptr switch_ret_t153; tll_ptr switch_ret_t156; tll_ptr switch_ret_t159;
  switch(((tll_node)s1_v88581)->tag) {
    case 6:
      switch(((tll_node)s2_v88582)->tag) {
        case 6:
          instr_struct(&EQ_t154, 3, 0);
          switch_ret_t153 = EQ_t154;
          break;
        case 7:
          __v88583 = ((tll_node)s2_v88582)->data[0];
          __v88584 = ((tll_node)s2_v88582)->data[1];
          instr_struct(&LT_t155, 1, 0);
          switch_ret_t153 = LT_t155;
          break;
      }
      switch_ret_t152 = switch_ret_t153;
      break;
    case 7:
      c1_v88585 = ((tll_node)s1_v88581)->data[0];
      s1_v88586 = ((tll_node)s1_v88581)->data[1];
      switch(((tll_node)s2_v88582)->tag) {
        case 6:
          instr_struct(&GT_t157, 2, 0);
          switch_ret_t156 = GT_t157;
          break;
        case 7:
          c2_v88587 = ((tll_node)s2_v88582)->data[0];
          s2_v88588 = ((tll_node)s2_v88582)->data[1];
          call_ret_t158 = comparec_i18(c1_v88585, c2_v88587);
          switch(((tll_node)call_ret_t158)->tag) {
            case 3:
              call_ret_t160 = compares_i22(s1_v88586, s2_v88588);
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

tll_ptr lam_fun_t164(tll_ptr s2_v88591, tll_env env) {
  tll_ptr call_ret_t163;
  call_ret_t163 = compares_i22(env[0], s2_v88591);
  return call_ret_t163;
}

tll_ptr lam_fun_t166(tll_ptr s1_v88589, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, s1_v88589);
  return lam_clo_t165;
}

tll_ptr and_thenUUU_i59(tll_ptr A_v88592, tll_ptr B_v88593, tll_ptr opt_v88594, tll_ptr f_v88595) {
  tll_ptr NoneUU_t169; tll_ptr app_ret_t170; tll_ptr switch_ret_t168;
  tll_ptr x_v88596;
  switch(((tll_node)opt_v88594)->tag) {
    case 19:
      instr_struct(&NoneUU_t169, 19, 0);
      switch_ret_t168 = NoneUU_t169;
      break;
    case 20:
      x_v88596 = ((tll_node)opt_v88594)->data[0];
      instr_app(&app_ret_t170, f_v88595, x_v88596);
      switch_ret_t168 = app_ret_t170;
      break;
  }
  return switch_ret_t168;
}

tll_ptr lam_fun_t172(tll_ptr f_v88606, tll_env env) {
  tll_ptr call_ret_t171;
  call_ret_t171 = and_thenUUU_i59(env[2], env[1], env[0], f_v88606);
  return call_ret_t171;
}

tll_ptr lam_fun_t174(tll_ptr opt_v88604, tll_env env) {
  tll_ptr lam_clo_t173;
  instr_clo(&lam_clo_t173, &lam_fun_t172, 3, opt_v88604, env[0], env[1]);
  return lam_clo_t173;
}

tll_ptr lam_fun_t176(tll_ptr B_v88601, tll_env env) {
  tll_ptr lam_clo_t175;
  instr_clo(&lam_clo_t175, &lam_fun_t174, 2, B_v88601, env[0]);
  return lam_clo_t175;
}

tll_ptr lam_fun_t178(tll_ptr A_v88597, tll_env env) {
  tll_ptr lam_clo_t177;
  instr_clo(&lam_clo_t177, &lam_fun_t176, 1, A_v88597);
  return lam_clo_t177;
}

tll_ptr and_thenUUL_i58(tll_ptr A_v88607, tll_ptr B_v88608, tll_ptr opt_v88609, tll_ptr f_v88610) {
  tll_ptr NoneUL_t181; tll_ptr app_ret_t182; tll_ptr switch_ret_t180;
  tll_ptr x_v88611;
  switch(((tll_node)opt_v88609)->tag) {
    case 17:
      instr_free_struct(opt_v88609);
      instr_struct(&NoneUL_t181, 17, 0);
      switch_ret_t180 = NoneUL_t181;
      break;
    case 18:
      x_v88611 = ((tll_node)opt_v88609)->data[0];
      instr_free_struct(opt_v88609);
      instr_app(&app_ret_t182, f_v88610, x_v88611);
      switch_ret_t180 = app_ret_t182;
      break;
  }
  return switch_ret_t180;
}

tll_ptr lam_fun_t184(tll_ptr f_v88621, tll_env env) {
  tll_ptr call_ret_t183;
  call_ret_t183 = and_thenUUL_i58(env[2], env[1], env[0], f_v88621);
  return call_ret_t183;
}

tll_ptr lam_fun_t186(tll_ptr opt_v88619, tll_env env) {
  tll_ptr lam_clo_t185;
  instr_clo(&lam_clo_t185, &lam_fun_t184, 3, opt_v88619, env[0], env[1]);
  return lam_clo_t185;
}

tll_ptr lam_fun_t188(tll_ptr B_v88616, tll_env env) {
  tll_ptr lam_clo_t187;
  instr_clo(&lam_clo_t187, &lam_fun_t186, 2, B_v88616, env[0]);
  return lam_clo_t187;
}

tll_ptr lam_fun_t190(tll_ptr A_v88612, tll_env env) {
  tll_ptr lam_clo_t189;
  instr_clo(&lam_clo_t189, &lam_fun_t188, 1, A_v88612);
  return lam_clo_t189;
}

tll_ptr and_thenULU_i57(tll_ptr A_v88622, tll_ptr B_v88623, tll_ptr opt_v88624, tll_ptr f_v88625) {
  tll_ptr NoneLU_t193; tll_ptr app_ret_t194; tll_ptr switch_ret_t192;
  tll_ptr x_v88626;
  switch(((tll_node)opt_v88624)->tag) {
    case 19:
      instr_struct(&NoneLU_t193, 15, 0);
      switch_ret_t192 = NoneLU_t193;
      break;
    case 20:
      x_v88626 = ((tll_node)opt_v88624)->data[0];
      instr_app(&app_ret_t194, f_v88625, x_v88626);
      switch_ret_t192 = app_ret_t194;
      break;
  }
  return switch_ret_t192;
}

tll_ptr lam_fun_t196(tll_ptr f_v88636, tll_env env) {
  tll_ptr call_ret_t195;
  call_ret_t195 = and_thenULU_i57(env[2], env[1], env[0], f_v88636);
  return call_ret_t195;
}

tll_ptr lam_fun_t198(tll_ptr opt_v88634, tll_env env) {
  tll_ptr lam_clo_t197;
  instr_clo(&lam_clo_t197, &lam_fun_t196, 3, opt_v88634, env[0], env[1]);
  return lam_clo_t197;
}

tll_ptr lam_fun_t200(tll_ptr B_v88631, tll_env env) {
  tll_ptr lam_clo_t199;
  instr_clo(&lam_clo_t199, &lam_fun_t198, 2, B_v88631, env[0]);
  return lam_clo_t199;
}

tll_ptr lam_fun_t202(tll_ptr A_v88627, tll_env env) {
  tll_ptr lam_clo_t201;
  instr_clo(&lam_clo_t201, &lam_fun_t200, 1, A_v88627);
  return lam_clo_t201;
}

tll_ptr and_thenULL_i56(tll_ptr A_v88637, tll_ptr B_v88638, tll_ptr opt_v88639, tll_ptr f_v88640) {
  tll_ptr NoneLL_t205; tll_ptr app_ret_t206; tll_ptr switch_ret_t204;
  tll_ptr x_v88641;
  switch(((tll_node)opt_v88639)->tag) {
    case 17:
      instr_free_struct(opt_v88639);
      instr_struct(&NoneLL_t205, 13, 0);
      switch_ret_t204 = NoneLL_t205;
      break;
    case 18:
      x_v88641 = ((tll_node)opt_v88639)->data[0];
      instr_free_struct(opt_v88639);
      instr_app(&app_ret_t206, f_v88640, x_v88641);
      switch_ret_t204 = app_ret_t206;
      break;
  }
  return switch_ret_t204;
}

tll_ptr lam_fun_t208(tll_ptr f_v88651, tll_env env) {
  tll_ptr call_ret_t207;
  call_ret_t207 = and_thenULL_i56(env[2], env[1], env[0], f_v88651);
  return call_ret_t207;
}

tll_ptr lam_fun_t210(tll_ptr opt_v88649, tll_env env) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 3, opt_v88649, env[0], env[1]);
  return lam_clo_t209;
}

tll_ptr lam_fun_t212(tll_ptr B_v88646, tll_env env) {
  tll_ptr lam_clo_t211;
  instr_clo(&lam_clo_t211, &lam_fun_t210, 2, B_v88646, env[0]);
  return lam_clo_t211;
}

tll_ptr lam_fun_t214(tll_ptr A_v88642, tll_env env) {
  tll_ptr lam_clo_t213;
  instr_clo(&lam_clo_t213, &lam_fun_t212, 1, A_v88642);
  return lam_clo_t213;
}

tll_ptr and_thenLUL_i54(tll_ptr A_v88652, tll_ptr B_v88653, tll_ptr opt_v88654, tll_ptr f_v88655) {
  tll_ptr NoneUL_t217; tll_ptr app_ret_t218; tll_ptr switch_ret_t216;
  tll_ptr x_v88656;
  switch(((tll_node)opt_v88654)->tag) {
    case 13:
      instr_free_struct(opt_v88654);
      instr_struct(&NoneUL_t217, 17, 0);
      switch_ret_t216 = NoneUL_t217;
      break;
    case 14:
      x_v88656 = ((tll_node)opt_v88654)->data[0];
      instr_free_struct(opt_v88654);
      instr_app(&app_ret_t218, f_v88655, x_v88656);
      switch_ret_t216 = app_ret_t218;
      break;
  }
  return switch_ret_t216;
}

tll_ptr lam_fun_t220(tll_ptr f_v88666, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = and_thenLUL_i54(env[2], env[1], env[0], f_v88666);
  return call_ret_t219;
}

tll_ptr lam_fun_t222(tll_ptr opt_v88664, tll_env env) {
  tll_ptr lam_clo_t221;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 3, opt_v88664, env[0], env[1]);
  return lam_clo_t221;
}

tll_ptr lam_fun_t224(tll_ptr B_v88661, tll_env env) {
  tll_ptr lam_clo_t223;
  instr_clo(&lam_clo_t223, &lam_fun_t222, 2, B_v88661, env[0]);
  return lam_clo_t223;
}

tll_ptr lam_fun_t226(tll_ptr A_v88657, tll_env env) {
  tll_ptr lam_clo_t225;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 1, A_v88657);
  return lam_clo_t225;
}

tll_ptr and_thenLLL_i52(tll_ptr A_v88667, tll_ptr B_v88668, tll_ptr opt_v88669, tll_ptr f_v88670) {
  tll_ptr NoneLL_t229; tll_ptr app_ret_t230; tll_ptr switch_ret_t228;
  tll_ptr x_v88671;
  switch(((tll_node)opt_v88669)->tag) {
    case 13:
      instr_free_struct(opt_v88669);
      instr_struct(&NoneLL_t229, 13, 0);
      switch_ret_t228 = NoneLL_t229;
      break;
    case 14:
      x_v88671 = ((tll_node)opt_v88669)->data[0];
      instr_free_struct(opt_v88669);
      instr_app(&app_ret_t230, f_v88670, x_v88671);
      switch_ret_t228 = app_ret_t230;
      break;
  }
  return switch_ret_t228;
}

tll_ptr lam_fun_t232(tll_ptr f_v88681, tll_env env) {
  tll_ptr call_ret_t231;
  call_ret_t231 = and_thenLLL_i52(env[2], env[1], env[0], f_v88681);
  return call_ret_t231;
}

tll_ptr lam_fun_t234(tll_ptr opt_v88679, tll_env env) {
  tll_ptr lam_clo_t233;
  instr_clo(&lam_clo_t233, &lam_fun_t232, 3, opt_v88679, env[0], env[1]);
  return lam_clo_t233;
}

tll_ptr lam_fun_t236(tll_ptr B_v88676, tll_env env) {
  tll_ptr lam_clo_t235;
  instr_clo(&lam_clo_t235, &lam_fun_t234, 2, B_v88676, env[0]);
  return lam_clo_t235;
}

tll_ptr lam_fun_t238(tll_ptr A_v88672, tll_env env) {
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, A_v88672);
  return lam_clo_t237;
}

tll_ptr lenUU_i67(tll_ptr A_v88682, tll_ptr xs_v88683) {
  tll_ptr add_ret_t245; tll_ptr call_ret_t243; tll_ptr consUU_t246;
  tll_ptr n_v88686; tll_ptr nilUU_t241; tll_ptr pair_struct_t242;
  tll_ptr pair_struct_t247; tll_ptr switch_ret_t240; tll_ptr switch_ret_t244;
  tll_ptr x_v88684; tll_ptr xs_v88685; tll_ptr xs_v88687;
  switch(((tll_node)xs_v88683)->tag) {
    case 27:
      instr_struct(&nilUU_t241, 27, 0);
      instr_struct(&pair_struct_t242, 0, 2, (tll_ptr)0, nilUU_t241);
      switch_ret_t240 = pair_struct_t242;
      break;
    case 28:
      x_v88684 = ((tll_node)xs_v88683)->data[0];
      xs_v88685 = ((tll_node)xs_v88683)->data[1];
      call_ret_t243 = lenUU_i67(0, xs_v88685);
      switch(((tll_node)call_ret_t243)->tag) {
        case 0:
          n_v88686 = ((tll_node)call_ret_t243)->data[0];
          xs_v88687 = ((tll_node)call_ret_t243)->data[1];
          instr_free_struct(call_ret_t243);
          add_ret_t245 = n_v88686 + 1;
          instr_struct(&consUU_t246, 28, 2, x_v88684, xs_v88687);
          instr_struct(&pair_struct_t247, 0, 2, add_ret_t245, consUU_t246);
          switch_ret_t244 = pair_struct_t247;
          break;
      }
      switch_ret_t240 = switch_ret_t244;
      break;
  }
  return switch_ret_t240;
}

tll_ptr lam_fun_t249(tll_ptr xs_v88690, tll_env env) {
  tll_ptr call_ret_t248;
  call_ret_t248 = lenUU_i67(env[0], xs_v88690);
  return call_ret_t248;
}

tll_ptr lam_fun_t251(tll_ptr A_v88688, tll_env env) {
  tll_ptr lam_clo_t250;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 1, A_v88688);
  return lam_clo_t250;
}

tll_ptr lenUL_i66(tll_ptr A_v88691, tll_ptr xs_v88692) {
  tll_ptr add_ret_t258; tll_ptr call_ret_t256; tll_ptr consUL_t259;
  tll_ptr n_v88695; tll_ptr nilUL_t254; tll_ptr pair_struct_t255;
  tll_ptr pair_struct_t260; tll_ptr switch_ret_t253; tll_ptr switch_ret_t257;
  tll_ptr x_v88693; tll_ptr xs_v88694; tll_ptr xs_v88696;
  switch(((tll_node)xs_v88692)->tag) {
    case 25:
      instr_free_struct(xs_v88692);
      instr_struct(&nilUL_t254, 25, 0);
      instr_struct(&pair_struct_t255, 0, 2, (tll_ptr)0, nilUL_t254);
      switch_ret_t253 = pair_struct_t255;
      break;
    case 26:
      x_v88693 = ((tll_node)xs_v88692)->data[0];
      xs_v88694 = ((tll_node)xs_v88692)->data[1];
      instr_free_struct(xs_v88692);
      call_ret_t256 = lenUL_i66(0, xs_v88694);
      switch(((tll_node)call_ret_t256)->tag) {
        case 0:
          n_v88695 = ((tll_node)call_ret_t256)->data[0];
          xs_v88696 = ((tll_node)call_ret_t256)->data[1];
          instr_free_struct(call_ret_t256);
          add_ret_t258 = n_v88695 + 1;
          instr_struct(&consUL_t259, 26, 2, x_v88693, xs_v88696);
          instr_struct(&pair_struct_t260, 0, 2, add_ret_t258, consUL_t259);
          switch_ret_t257 = pair_struct_t260;
          break;
      }
      switch_ret_t253 = switch_ret_t257;
      break;
  }
  return switch_ret_t253;
}

tll_ptr lam_fun_t262(tll_ptr xs_v88699, tll_env env) {
  tll_ptr call_ret_t261;
  call_ret_t261 = lenUL_i66(env[0], xs_v88699);
  return call_ret_t261;
}

tll_ptr lam_fun_t264(tll_ptr A_v88697, tll_env env) {
  tll_ptr lam_clo_t263;
  instr_clo(&lam_clo_t263, &lam_fun_t262, 1, A_v88697);
  return lam_clo_t263;
}

tll_ptr lenLL_i64(tll_ptr A_v88700, tll_ptr xs_v88701) {
  tll_ptr add_ret_t271; tll_ptr call_ret_t269; tll_ptr consLL_t272;
  tll_ptr n_v88704; tll_ptr nilLL_t267; tll_ptr pair_struct_t268;
  tll_ptr pair_struct_t273; tll_ptr switch_ret_t266; tll_ptr switch_ret_t270;
  tll_ptr x_v88702; tll_ptr xs_v88703; tll_ptr xs_v88705;
  switch(((tll_node)xs_v88701)->tag) {
    case 21:
      instr_free_struct(xs_v88701);
      instr_struct(&nilLL_t267, 21, 0);
      instr_struct(&pair_struct_t268, 0, 2, (tll_ptr)0, nilLL_t267);
      switch_ret_t266 = pair_struct_t268;
      break;
    case 22:
      x_v88702 = ((tll_node)xs_v88701)->data[0];
      xs_v88703 = ((tll_node)xs_v88701)->data[1];
      instr_free_struct(xs_v88701);
      call_ret_t269 = lenLL_i64(0, xs_v88703);
      switch(((tll_node)call_ret_t269)->tag) {
        case 0:
          n_v88704 = ((tll_node)call_ret_t269)->data[0];
          xs_v88705 = ((tll_node)call_ret_t269)->data[1];
          instr_free_struct(call_ret_t269);
          add_ret_t271 = n_v88704 + 1;
          instr_struct(&consLL_t272, 22, 2, x_v88702, xs_v88705);
          instr_struct(&pair_struct_t273, 0, 2, add_ret_t271, consLL_t272);
          switch_ret_t270 = pair_struct_t273;
          break;
      }
      switch_ret_t266 = switch_ret_t270;
      break;
  }
  return switch_ret_t266;
}

tll_ptr lam_fun_t275(tll_ptr xs_v88708, tll_env env) {
  tll_ptr call_ret_t274;
  call_ret_t274 = lenLL_i64(env[0], xs_v88708);
  return call_ret_t274;
}

tll_ptr lam_fun_t277(tll_ptr A_v88706, tll_env env) {
  tll_ptr lam_clo_t276;
  instr_clo(&lam_clo_t276, &lam_fun_t275, 1, A_v88706);
  return lam_clo_t276;
}

tll_ptr appendUU_i71(tll_ptr A_v88709, tll_ptr xs_v88710, tll_ptr ys_v88711) {
  tll_ptr call_ret_t280; tll_ptr consUU_t281; tll_ptr switch_ret_t279;
  tll_ptr x_v88712; tll_ptr xs_v88713;
  switch(((tll_node)xs_v88710)->tag) {
    case 27:
      switch_ret_t279 = ys_v88711;
      break;
    case 28:
      x_v88712 = ((tll_node)xs_v88710)->data[0];
      xs_v88713 = ((tll_node)xs_v88710)->data[1];
      call_ret_t280 = appendUU_i71(0, xs_v88713, ys_v88711);
      instr_struct(&consUU_t281, 28, 2, x_v88712, call_ret_t280);
      switch_ret_t279 = consUU_t281;
      break;
  }
  return switch_ret_t279;
}

tll_ptr lam_fun_t283(tll_ptr ys_v88719, tll_env env) {
  tll_ptr call_ret_t282;
  call_ret_t282 = appendUU_i71(env[1], env[0], ys_v88719);
  return call_ret_t282;
}

tll_ptr lam_fun_t285(tll_ptr xs_v88717, tll_env env) {
  tll_ptr lam_clo_t284;
  instr_clo(&lam_clo_t284, &lam_fun_t283, 2, xs_v88717, env[0]);
  return lam_clo_t284;
}

tll_ptr lam_fun_t287(tll_ptr A_v88714, tll_env env) {
  tll_ptr lam_clo_t286;
  instr_clo(&lam_clo_t286, &lam_fun_t285, 1, A_v88714);
  return lam_clo_t286;
}

tll_ptr appendUL_i70(tll_ptr A_v88720, tll_ptr xs_v88721, tll_ptr ys_v88722) {
  tll_ptr call_ret_t290; tll_ptr consUL_t291; tll_ptr switch_ret_t289;
  tll_ptr x_v88723; tll_ptr xs_v88724;
  switch(((tll_node)xs_v88721)->tag) {
    case 25:
      instr_free_struct(xs_v88721);
      switch_ret_t289 = ys_v88722;
      break;
    case 26:
      x_v88723 = ((tll_node)xs_v88721)->data[0];
      xs_v88724 = ((tll_node)xs_v88721)->data[1];
      instr_free_struct(xs_v88721);
      call_ret_t290 = appendUL_i70(0, xs_v88724, ys_v88722);
      instr_struct(&consUL_t291, 26, 2, x_v88723, call_ret_t290);
      switch_ret_t289 = consUL_t291;
      break;
  }
  return switch_ret_t289;
}

tll_ptr lam_fun_t293(tll_ptr ys_v88730, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = appendUL_i70(env[1], env[0], ys_v88730);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v88728, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 2, xs_v88728, env[0]);
  return lam_clo_t294;
}

tll_ptr lam_fun_t297(tll_ptr A_v88725, tll_env env) {
  tll_ptr lam_clo_t296;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 1, A_v88725);
  return lam_clo_t296;
}

tll_ptr appendLL_i68(tll_ptr A_v88731, tll_ptr xs_v88732, tll_ptr ys_v88733) {
  tll_ptr call_ret_t300; tll_ptr consLL_t301; tll_ptr switch_ret_t299;
  tll_ptr x_v88734; tll_ptr xs_v88735;
  switch(((tll_node)xs_v88732)->tag) {
    case 21:
      instr_free_struct(xs_v88732);
      switch_ret_t299 = ys_v88733;
      break;
    case 22:
      x_v88734 = ((tll_node)xs_v88732)->data[0];
      xs_v88735 = ((tll_node)xs_v88732)->data[1];
      instr_free_struct(xs_v88732);
      call_ret_t300 = appendLL_i68(0, xs_v88735, ys_v88733);
      instr_struct(&consLL_t301, 22, 2, x_v88734, call_ret_t300);
      switch_ret_t299 = consLL_t301;
      break;
  }
  return switch_ret_t299;
}

tll_ptr lam_fun_t303(tll_ptr ys_v88741, tll_env env) {
  tll_ptr call_ret_t302;
  call_ret_t302 = appendLL_i68(env[1], env[0], ys_v88741);
  return call_ret_t302;
}

tll_ptr lam_fun_t305(tll_ptr xs_v88739, tll_env env) {
  tll_ptr lam_clo_t304;
  instr_clo(&lam_clo_t304, &lam_fun_t303, 2, xs_v88739, env[0]);
  return lam_clo_t304;
}

tll_ptr lam_fun_t307(tll_ptr A_v88736, tll_env env) {
  tll_ptr lam_clo_t306;
  instr_clo(&lam_clo_t306, &lam_fun_t305, 1, A_v88736);
  return lam_clo_t306;
}

tll_ptr lam_fun_t314(tll_ptr __v88743, tll_env env) {
  tll_ptr __v88752; tll_ptr ch_v88750; tll_ptr ch_v88751; tll_ptr ch_v88754;
  tll_ptr ch_v88755; tll_ptr prim_ch_t309; tll_ptr recv_msg_t311;
  tll_ptr s_v88753; tll_ptr send_ch_t310; tll_ptr send_ch_t313;
  tll_ptr switch_ret_t312;
  instr_open(&prim_ch_t309, &proc_stdin);
  ch_v88750 = prim_ch_t309;
  instr_send(&send_ch_t310, ch_v88750, (tll_ptr)1);
  ch_v88751 = send_ch_t310;
  instr_recv(&recv_msg_t311, ch_v88751);
  __v88752 = recv_msg_t311;
  switch(((tll_node)__v88752)->tag) {
    case 0:
      s_v88753 = ((tll_node)__v88752)->data[0];
      ch_v88754 = ((tll_node)__v88752)->data[1];
      instr_free_struct(__v88752);
      instr_send(&send_ch_t313, ch_v88754, (tll_ptr)0);
      ch_v88755 = send_ch_t313;
      switch_ret_t312 = s_v88753;
      break;
  }
  return switch_ret_t312;
}

tll_ptr readline_i33(tll_ptr __v88742) {
  tll_ptr lam_clo_t315;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 0);
  return lam_clo_t315;
}

tll_ptr lam_fun_t317(tll_ptr __v88756, tll_env env) {
  tll_ptr call_ret_t316;
  call_ret_t316 = readline_i33(__v88756);
  return call_ret_t316;
}

tll_ptr lam_fun_t323(tll_ptr __v88758, tll_env env) {
  tll_ptr ch_v88763; tll_ptr ch_v88764; tll_ptr ch_v88765; tll_ptr ch_v88766;
  tll_ptr prim_ch_t319; tll_ptr send_ch_t320; tll_ptr send_ch_t321;
  tll_ptr send_ch_t322;
  instr_open(&prim_ch_t319, &proc_stdout);
  ch_v88763 = prim_ch_t319;
  instr_send(&send_ch_t320, ch_v88763, (tll_ptr)1);
  ch_v88764 = send_ch_t320;
  instr_send(&send_ch_t321, ch_v88764, env[0]);
  ch_v88765 = send_ch_t321;
  instr_send(&send_ch_t322, ch_v88765, (tll_ptr)0);
  ch_v88766 = send_ch_t322;
  return 0;
}

tll_ptr print_i34(tll_ptr s_v88757) {
  tll_ptr lam_clo_t324;
  instr_clo(&lam_clo_t324, &lam_fun_t323, 1, s_v88757);
  return lam_clo_t324;
}

tll_ptr lam_fun_t326(tll_ptr s_v88767, tll_env env) {
  tll_ptr call_ret_t325;
  call_ret_t325 = print_i34(s_v88767);
  return call_ret_t325;
}

tll_ptr lam_fun_t332(tll_ptr __v88769, tll_env env) {
  tll_ptr ch_v88774; tll_ptr ch_v88775; tll_ptr ch_v88776; tll_ptr ch_v88777;
  tll_ptr prim_ch_t328; tll_ptr send_ch_t329; tll_ptr send_ch_t330;
  tll_ptr send_ch_t331;
  instr_open(&prim_ch_t328, &proc_stderr);
  ch_v88774 = prim_ch_t328;
  instr_send(&send_ch_t329, ch_v88774, (tll_ptr)1);
  ch_v88775 = send_ch_t329;
  instr_send(&send_ch_t330, ch_v88775, env[0]);
  ch_v88776 = send_ch_t330;
  instr_send(&send_ch_t331, ch_v88776, (tll_ptr)0);
  ch_v88777 = send_ch_t331;
  return 0;
}

tll_ptr prerr_i35(tll_ptr s_v88768) {
  tll_ptr lam_clo_t333;
  instr_clo(&lam_clo_t333, &lam_fun_t332, 1, s_v88768);
  return lam_clo_t333;
}

tll_ptr lam_fun_t335(tll_ptr s_v88778, tll_env env) {
  tll_ptr call_ret_t334;
  call_ret_t334 = prerr_i35(s_v88778);
  return call_ret_t334;
}

tll_ptr get_at_i37(tll_ptr A_v88779, tll_ptr n_v88780, tll_ptr xs_v88781, tll_ptr a_v88782) {
  tll_ptr __v88783; tll_ptr __v88786; tll_ptr add_ret_t380;
  tll_ptr call_ret_t379; tll_ptr ifte_ret_t382; tll_ptr switch_ret_t378;
  tll_ptr switch_ret_t381; tll_ptr x_v88785; tll_ptr xs_v88784;
  if (n_v88780) {
    switch(((tll_node)xs_v88781)->tag) {
      case 27:
        switch_ret_t378 = a_v88782;
        break;
      case 28:
        __v88783 = ((tll_node)xs_v88781)->data[0];
        xs_v88784 = ((tll_node)xs_v88781)->data[1];
        add_ret_t380 = n_v88780 - 1;
        call_ret_t379 = get_at_i37(0, add_ret_t380, xs_v88784, a_v88782);
        switch_ret_t378 = call_ret_t379;
        break;
    }
    ifte_ret_t382 = switch_ret_t378;
  }
  else {
    switch(((tll_node)xs_v88781)->tag) {
      case 27:
        switch_ret_t381 = a_v88782;
        break;
      case 28:
        x_v88785 = ((tll_node)xs_v88781)->data[0];
        __v88786 = ((tll_node)xs_v88781)->data[1];
        switch_ret_t381 = x_v88785;
        break;
    }
    ifte_ret_t382 = switch_ret_t381;
  }
  return ifte_ret_t382;
}

tll_ptr lam_fun_t384(tll_ptr a_v88796, tll_env env) {
  tll_ptr call_ret_t383;
  call_ret_t383 = get_at_i37(env[2], env[1], env[0], a_v88796);
  return call_ret_t383;
}

tll_ptr lam_fun_t386(tll_ptr xs_v88794, tll_env env) {
  tll_ptr lam_clo_t385;
  instr_clo(&lam_clo_t385, &lam_fun_t384, 3, xs_v88794, env[0], env[1]);
  return lam_clo_t385;
}

tll_ptr lam_fun_t388(tll_ptr n_v88791, tll_env env) {
  tll_ptr lam_clo_t387;
  instr_clo(&lam_clo_t387, &lam_fun_t386, 2, n_v88791, env[0]);
  return lam_clo_t387;
}

tll_ptr lam_fun_t390(tll_ptr A_v88787, tll_env env) {
  tll_ptr lam_clo_t389;
  instr_clo(&lam_clo_t389, &lam_fun_t388, 1, A_v88787);
  return lam_clo_t389;
}

tll_ptr string_of_digit_i38(tll_ptr n_v88797) {
  tll_ptr EmptyString_t393; tll_ptr call_ret_t392;
  instr_struct(&EmptyString_t393, 6, 0);
  call_ret_t392 = get_at_i37(0, n_v88797, digits_i36, EmptyString_t393);
  return call_ret_t392;
}

tll_ptr lam_fun_t395(tll_ptr n_v88798, tll_env env) {
  tll_ptr call_ret_t394;
  call_ret_t394 = string_of_digit_i38(n_v88798);
  return call_ret_t394;
}

tll_ptr string_of_nat_i39(tll_ptr n_v88799) {
  tll_ptr call_ret_t397; tll_ptr call_ret_t398; tll_ptr call_ret_t399;
  tll_ptr call_ret_t400; tll_ptr call_ret_t401; tll_ptr call_ret_t402;
  tll_ptr ifte_ret_t403; tll_ptr n_v88801; tll_ptr s_v88800;
  call_ret_t398 = modn_i16(n_v88799, (tll_ptr)10);
  call_ret_t397 = string_of_digit_i38(call_ret_t398);
  s_v88800 = call_ret_t397;
  call_ret_t399 = divn_i15(n_v88799, (tll_ptr)10);
  n_v88801 = call_ret_t399;
  call_ret_t400 = ltn_i6((tll_ptr)0, n_v88801);
  if (call_ret_t400) {
    call_ret_t402 = string_of_nat_i39(n_v88801);
    call_ret_t401 = cats_i19(call_ret_t402, s_v88800);
    ifte_ret_t403 = call_ret_t401;
  }
  else {
    ifte_ret_t403 = s_v88800;
  }
  return ifte_ret_t403;
}

tll_ptr lam_fun_t405(tll_ptr n_v88802, tll_env env) {
  tll_ptr call_ret_t404;
  call_ret_t404 = string_of_nat_i39(n_v88802);
  return call_ret_t404;
}

tll_ptr digit_of_char_i40(tll_ptr c_v88803) {
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
  call_ret_t407 = eqc_i17(c_v88803, Char_t408);
  if (call_ret_t407) {
    instr_struct(&SomeUL_t409, 18, 1, (tll_ptr)0);
    ifte_ret_t447 = SomeUL_t409;
  }
  else {
    instr_struct(&Char_t411, 5, 1, (tll_ptr)49);
    call_ret_t410 = eqc_i17(c_v88803, Char_t411);
    if (call_ret_t410) {
      instr_struct(&SomeUL_t412, 18, 1, (tll_ptr)1);
      ifte_ret_t446 = SomeUL_t412;
    }
    else {
      instr_struct(&Char_t414, 5, 1, (tll_ptr)50);
      call_ret_t413 = eqc_i17(c_v88803, Char_t414);
      if (call_ret_t413) {
        instr_struct(&SomeUL_t415, 18, 1, (tll_ptr)2);
        ifte_ret_t445 = SomeUL_t415;
      }
      else {
        instr_struct(&Char_t417, 5, 1, (tll_ptr)51);
        call_ret_t416 = eqc_i17(c_v88803, Char_t417);
        if (call_ret_t416) {
          instr_struct(&SomeUL_t418, 18, 1, (tll_ptr)3);
          ifte_ret_t444 = SomeUL_t418;
        }
        else {
          instr_struct(&Char_t420, 5, 1, (tll_ptr)52);
          call_ret_t419 = eqc_i17(c_v88803, Char_t420);
          if (call_ret_t419) {
            instr_struct(&SomeUL_t421, 18, 1, (tll_ptr)4);
            ifte_ret_t443 = SomeUL_t421;
          }
          else {
            instr_struct(&Char_t423, 5, 1, (tll_ptr)53);
            call_ret_t422 = eqc_i17(c_v88803, Char_t423);
            if (call_ret_t422) {
              instr_struct(&SomeUL_t424, 18, 1, (tll_ptr)5);
              ifte_ret_t442 = SomeUL_t424;
            }
            else {
              instr_struct(&Char_t426, 5, 1, (tll_ptr)54);
              call_ret_t425 = eqc_i17(c_v88803, Char_t426);
              if (call_ret_t425) {
                instr_struct(&SomeUL_t427, 18, 1, (tll_ptr)6);
                ifte_ret_t441 = SomeUL_t427;
              }
              else {
                instr_struct(&Char_t429, 5, 1, (tll_ptr)55);
                call_ret_t428 = eqc_i17(c_v88803, Char_t429);
                if (call_ret_t428) {
                  instr_struct(&SomeUL_t430, 18, 1, (tll_ptr)7);
                  ifte_ret_t440 = SomeUL_t430;
                }
                else {
                  instr_struct(&Char_t432, 5, 1, (tll_ptr)56);
                  call_ret_t431 = eqc_i17(c_v88803, Char_t432);
                  if (call_ret_t431) {
                    instr_struct(&SomeUL_t433, 18, 1, (tll_ptr)8);
                    ifte_ret_t439 = SomeUL_t433;
                  }
                  else {
                    instr_struct(&Char_t435, 5, 1, (tll_ptr)57);
                    call_ret_t434 = eqc_i17(c_v88803, Char_t435);
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

tll_ptr lam_fun_t449(tll_ptr c_v88804, tll_env env) {
  tll_ptr call_ret_t448;
  call_ret_t448 = digit_of_char_i40(c_v88804);
  return call_ret_t448;
}

tll_ptr nat_of_string_loop_i41(tll_ptr s_v88805, tll_ptr acc_v88806) {
  tll_ptr NoneUL_t455; tll_ptr SomeUL_t452; tll_ptr c_v88807;
  tll_ptr call_ret_t453; tll_ptr call_ret_t456; tll_ptr call_ret_t457;
  tll_ptr call_ret_t458; tll_ptr n_v88809; tll_ptr s_v88808;
  tll_ptr switch_ret_t451; tll_ptr switch_ret_t454;
  switch(((tll_node)s_v88805)->tag) {
    case 6:
      instr_struct(&SomeUL_t452, 18, 1, acc_v88806);
      switch_ret_t451 = SomeUL_t452;
      break;
    case 7:
      c_v88807 = ((tll_node)s_v88805)->data[0];
      s_v88808 = ((tll_node)s_v88805)->data[1];
      call_ret_t453 = digit_of_char_i40(c_v88807);
      switch(((tll_node)call_ret_t453)->tag) {
        case 17:
          instr_free_struct(call_ret_t453);
          instr_struct(&NoneUL_t455, 17, 0);
          switch_ret_t454 = NoneUL_t455;
          break;
        case 18:
          n_v88809 = ((tll_node)call_ret_t453)->data[0];
          instr_free_struct(call_ret_t453);
          call_ret_t458 = muln_i14(acc_v88806, (tll_ptr)10);
          call_ret_t457 = addn_i12(call_ret_t458, n_v88809);
          call_ret_t456 = nat_of_string_loop_i41(s_v88808, call_ret_t457);
          switch_ret_t454 = call_ret_t456;
          break;
      }
      switch_ret_t451 = switch_ret_t454;
      break;
  }
  return switch_ret_t451;
}

tll_ptr lam_fun_t460(tll_ptr acc_v88812, tll_env env) {
  tll_ptr call_ret_t459;
  call_ret_t459 = nat_of_string_loop_i41(env[0], acc_v88812);
  return call_ret_t459;
}

tll_ptr lam_fun_t462(tll_ptr s_v88810, tll_env env) {
  tll_ptr lam_clo_t461;
  instr_clo(&lam_clo_t461, &lam_fun_t460, 1, s_v88810);
  return lam_clo_t461;
}

tll_ptr nat_of_string_i42(tll_ptr s_v88813) {
  tll_ptr call_ret_t464;
  call_ret_t464 = nat_of_string_loop_i41(s_v88813, (tll_ptr)0);
  return call_ret_t464;
}

tll_ptr lam_fun_t466(tll_ptr s_v88814, tll_env env) {
  tll_ptr call_ret_t465;
  call_ret_t465 = nat_of_string_i42(s_v88814);
  return call_ret_t465;
}

tll_ptr splitU_i73(tll_ptr zs_v88815) {
  tll_ptr __v88820; tll_ptr call_ret_t477; tll_ptr consUU_t474;
  tll_ptr consUU_t479; tll_ptr consUU_t480; tll_ptr nilUU_t469;
  tll_ptr nilUU_t470; tll_ptr nilUU_t473; tll_ptr nilUU_t475;
  tll_ptr pair_struct_t471; tll_ptr pair_struct_t476;
  tll_ptr pair_struct_t481; tll_ptr switch_ret_t468; tll_ptr switch_ret_t472;
  tll_ptr switch_ret_t478; tll_ptr x_v88816; tll_ptr xs_v88821;
  tll_ptr y_v88818; tll_ptr ys_v88822; tll_ptr zs_v88817; tll_ptr zs_v88819;
  switch(((tll_node)zs_v88815)->tag) {
    case 27:
      instr_struct(&nilUU_t469, 27, 0);
      instr_struct(&nilUU_t470, 27, 0);
      instr_struct(&pair_struct_t471, 0, 2, nilUU_t469, nilUU_t470);
      switch_ret_t468 = pair_struct_t471;
      break;
    case 28:
      x_v88816 = ((tll_node)zs_v88815)->data[0];
      zs_v88817 = ((tll_node)zs_v88815)->data[1];
      switch(((tll_node)zs_v88817)->tag) {
        case 27:
          instr_struct(&nilUU_t473, 27, 0);
          instr_struct(&consUU_t474, 28, 2, x_v88816, nilUU_t473);
          instr_struct(&nilUU_t475, 27, 0);
          instr_struct(&pair_struct_t476, 0, 2, consUU_t474, nilUU_t475);
          switch_ret_t472 = pair_struct_t476;
          break;
        case 28:
          y_v88818 = ((tll_node)zs_v88817)->data[0];
          zs_v88819 = ((tll_node)zs_v88817)->data[1];
          call_ret_t477 = splitU_i73(zs_v88819);
          __v88820 = call_ret_t477;
          switch(((tll_node)__v88820)->tag) {
            case 0:
              xs_v88821 = ((tll_node)__v88820)->data[0];
              ys_v88822 = ((tll_node)__v88820)->data[1];
              instr_free_struct(__v88820);
              instr_struct(&consUU_t479, 28, 2, x_v88816, xs_v88821);
              instr_struct(&consUU_t480, 28, 2, y_v88818, ys_v88822);
              instr_struct(&pair_struct_t481, 0, 2, consUU_t479, consUU_t480);
              switch_ret_t478 = pair_struct_t481;
              break;
          }
          switch_ret_t472 = switch_ret_t478;
          break;
      }
      switch_ret_t468 = switch_ret_t472;
      break;
  }
  return switch_ret_t468;
}

tll_ptr lam_fun_t483(tll_ptr zs_v88823, tll_env env) {
  tll_ptr call_ret_t482;
  call_ret_t482 = splitU_i73(zs_v88823);
  return call_ret_t482;
}

tll_ptr splitL_i72(tll_ptr zs_v88824) {
  tll_ptr __v88829; tll_ptr call_ret_t494; tll_ptr consUL_t491;
  tll_ptr consUL_t496; tll_ptr consUL_t497; tll_ptr nilUL_t486;
  tll_ptr nilUL_t487; tll_ptr nilUL_t490; tll_ptr nilUL_t492;
  tll_ptr pair_struct_t488; tll_ptr pair_struct_t493;
  tll_ptr pair_struct_t498; tll_ptr switch_ret_t485; tll_ptr switch_ret_t489;
  tll_ptr switch_ret_t495; tll_ptr x_v88825; tll_ptr xs_v88830;
  tll_ptr y_v88827; tll_ptr ys_v88831; tll_ptr zs_v88826; tll_ptr zs_v88828;
  switch(((tll_node)zs_v88824)->tag) {
    case 25:
      instr_free_struct(zs_v88824);
      instr_struct(&nilUL_t486, 25, 0);
      instr_struct(&nilUL_t487, 25, 0);
      instr_struct(&pair_struct_t488, 0, 2, nilUL_t486, nilUL_t487);
      switch_ret_t485 = pair_struct_t488;
      break;
    case 26:
      x_v88825 = ((tll_node)zs_v88824)->data[0];
      zs_v88826 = ((tll_node)zs_v88824)->data[1];
      instr_free_struct(zs_v88824);
      switch(((tll_node)zs_v88826)->tag) {
        case 25:
          instr_free_struct(zs_v88826);
          instr_struct(&nilUL_t490, 25, 0);
          instr_struct(&consUL_t491, 26, 2, x_v88825, nilUL_t490);
          instr_struct(&nilUL_t492, 25, 0);
          instr_struct(&pair_struct_t493, 0, 2, consUL_t491, nilUL_t492);
          switch_ret_t489 = pair_struct_t493;
          break;
        case 26:
          y_v88827 = ((tll_node)zs_v88826)->data[0];
          zs_v88828 = ((tll_node)zs_v88826)->data[1];
          instr_free_struct(zs_v88826);
          call_ret_t494 = splitL_i72(zs_v88828);
          __v88829 = call_ret_t494;
          switch(((tll_node)__v88829)->tag) {
            case 0:
              xs_v88830 = ((tll_node)__v88829)->data[0];
              ys_v88831 = ((tll_node)__v88829)->data[1];
              instr_free_struct(__v88829);
              instr_struct(&consUL_t496, 26, 2, x_v88825, xs_v88830);
              instr_struct(&consUL_t497, 26, 2, y_v88827, ys_v88831);
              instr_struct(&pair_struct_t498, 0, 2, consUL_t496, consUL_t497);
              switch_ret_t495 = pair_struct_t498;
              break;
          }
          switch_ret_t489 = switch_ret_t495;
          break;
      }
      switch_ret_t485 = switch_ret_t489;
      break;
  }
  return switch_ret_t485;
}

tll_ptr lam_fun_t500(tll_ptr zs_v88832, tll_env env) {
  tll_ptr call_ret_t499;
  call_ret_t499 = splitL_i72(zs_v88832);
  return call_ret_t499;
}

tll_ptr mergeU_i75(tll_ptr xs_v88833, tll_ptr ys_v88834) {
  tll_ptr call_ret_t505; tll_ptr call_ret_t506; tll_ptr call_ret_t509;
  tll_ptr consUU_t504; tll_ptr consUU_t507; tll_ptr consUU_t508;
  tll_ptr consUU_t510; tll_ptr consUU_t511; tll_ptr ifte_ret_t512;
  tll_ptr switch_ret_t502; tll_ptr switch_ret_t503; tll_ptr x_v88835;
  tll_ptr xs0_v88836; tll_ptr y_v88837; tll_ptr ys0_v88838;
  switch(((tll_node)xs_v88833)->tag) {
    case 27:
      switch_ret_t502 = ys_v88834;
      break;
    case 28:
      x_v88835 = ((tll_node)xs_v88833)->data[0];
      xs0_v88836 = ((tll_node)xs_v88833)->data[1];
      switch(((tll_node)ys_v88834)->tag) {
        case 27:
          instr_struct(&consUU_t504, 28, 2, x_v88835, xs0_v88836);
          switch_ret_t503 = consUU_t504;
          break;
        case 28:
          y_v88837 = ((tll_node)ys_v88834)->data[0];
          ys0_v88838 = ((tll_node)ys_v88834)->data[1];
          call_ret_t505 = lten_i5(x_v88835, y_v88837);
          if (call_ret_t505) {
            instr_struct(&consUU_t507, 28, 2, y_v88837, ys0_v88838);
            call_ret_t506 = mergeU_i75(xs0_v88836, consUU_t507);
            instr_struct(&consUU_t508, 28, 2, x_v88835, call_ret_t506);
            ifte_ret_t512 = consUU_t508;
          }
          else {
            instr_struct(&consUU_t510, 28, 2, x_v88835, xs0_v88836);
            call_ret_t509 = mergeU_i75(consUU_t510, ys0_v88838);
            instr_struct(&consUU_t511, 28, 2, y_v88837, call_ret_t509);
            ifte_ret_t512 = consUU_t511;
          }
          switch_ret_t503 = ifte_ret_t512;
          break;
      }
      switch_ret_t502 = switch_ret_t503;
      break;
  }
  return switch_ret_t502;
}

tll_ptr lam_fun_t514(tll_ptr ys_v88841, tll_env env) {
  tll_ptr call_ret_t513;
  call_ret_t513 = mergeU_i75(env[0], ys_v88841);
  return call_ret_t513;
}

tll_ptr lam_fun_t516(tll_ptr xs_v88839, tll_env env) {
  tll_ptr lam_clo_t515;
  instr_clo(&lam_clo_t515, &lam_fun_t514, 1, xs_v88839);
  return lam_clo_t515;
}

tll_ptr mergeL_i74(tll_ptr xs_v88842, tll_ptr ys_v88843) {
  tll_ptr call_ret_t521; tll_ptr call_ret_t522; tll_ptr call_ret_t525;
  tll_ptr consUL_t520; tll_ptr consUL_t523; tll_ptr consUL_t524;
  tll_ptr consUL_t526; tll_ptr consUL_t527; tll_ptr ifte_ret_t528;
  tll_ptr switch_ret_t518; tll_ptr switch_ret_t519; tll_ptr x_v88844;
  tll_ptr xs0_v88845; tll_ptr y_v88846; tll_ptr ys0_v88847;
  switch(((tll_node)xs_v88842)->tag) {
    case 25:
      instr_free_struct(xs_v88842);
      switch_ret_t518 = ys_v88843;
      break;
    case 26:
      x_v88844 = ((tll_node)xs_v88842)->data[0];
      xs0_v88845 = ((tll_node)xs_v88842)->data[1];
      instr_free_struct(xs_v88842);
      switch(((tll_node)ys_v88843)->tag) {
        case 25:
          instr_free_struct(ys_v88843);
          instr_struct(&consUL_t520, 26, 2, x_v88844, xs0_v88845);
          switch_ret_t519 = consUL_t520;
          break;
        case 26:
          y_v88846 = ((tll_node)ys_v88843)->data[0];
          ys0_v88847 = ((tll_node)ys_v88843)->data[1];
          instr_free_struct(ys_v88843);
          call_ret_t521 = lten_i5(x_v88844, y_v88846);
          if (call_ret_t521) {
            instr_struct(&consUL_t523, 26, 2, y_v88846, ys0_v88847);
            call_ret_t522 = mergeL_i74(xs0_v88845, consUL_t523);
            instr_struct(&consUL_t524, 26, 2, x_v88844, call_ret_t522);
            ifte_ret_t528 = consUL_t524;
          }
          else {
            instr_struct(&consUL_t526, 26, 2, x_v88844, xs0_v88845);
            call_ret_t525 = mergeL_i74(consUL_t526, ys0_v88847);
            instr_struct(&consUL_t527, 26, 2, y_v88846, call_ret_t525);
            ifte_ret_t528 = consUL_t527;
          }
          switch_ret_t519 = ifte_ret_t528;
          break;
      }
      switch_ret_t518 = switch_ret_t519;
      break;
  }
  return switch_ret_t518;
}

tll_ptr lam_fun_t530(tll_ptr ys_v88850, tll_env env) {
  tll_ptr call_ret_t529;
  call_ret_t529 = mergeL_i74(env[0], ys_v88850);
  return call_ret_t529;
}

tll_ptr lam_fun_t532(tll_ptr xs_v88848, tll_env env) {
  tll_ptr lam_clo_t531;
  instr_clo(&lam_clo_t531, &lam_fun_t530, 1, xs_v88848);
  return lam_clo_t531;
}

tll_ptr msortU_i77(tll_ptr zs_v88851) {
  tll_ptr __v88856; tll_ptr call_ret_t539; tll_ptr call_ret_t543;
  tll_ptr call_ret_t544; tll_ptr call_ret_t545; tll_ptr consUU_t538;
  tll_ptr consUU_t540; tll_ptr consUU_t541; tll_ptr nilUU_t535;
  tll_ptr nilUU_t537; tll_ptr switch_ret_t534; tll_ptr switch_ret_t536;
  tll_ptr switch_ret_t542; tll_ptr x_v88852; tll_ptr xs_v88857;
  tll_ptr y_v88854; tll_ptr ys_v88858; tll_ptr zs_v88853; tll_ptr zs_v88855;
  switch(((tll_node)zs_v88851)->tag) {
    case 27:
      instr_struct(&nilUU_t535, 27, 0);
      switch_ret_t534 = nilUU_t535;
      break;
    case 28:
      x_v88852 = ((tll_node)zs_v88851)->data[0];
      zs_v88853 = ((tll_node)zs_v88851)->data[1];
      switch(((tll_node)zs_v88853)->tag) {
        case 27:
          instr_struct(&nilUU_t537, 27, 0);
          instr_struct(&consUU_t538, 28, 2, x_v88852, nilUU_t537);
          switch_ret_t536 = consUU_t538;
          break;
        case 28:
          y_v88854 = ((tll_node)zs_v88853)->data[0];
          zs_v88855 = ((tll_node)zs_v88853)->data[1];
          instr_struct(&consUU_t540, 28, 2, y_v88854, zs_v88855);
          instr_struct(&consUU_t541, 28, 2, x_v88852, consUU_t540);
          call_ret_t539 = splitU_i73(consUU_t541);
          __v88856 = call_ret_t539;
          switch(((tll_node)__v88856)->tag) {
            case 0:
              xs_v88857 = ((tll_node)__v88856)->data[0];
              ys_v88858 = ((tll_node)__v88856)->data[1];
              instr_free_struct(__v88856);
              call_ret_t544 = msortU_i77(xs_v88857);
              call_ret_t545 = msortU_i77(ys_v88858);
              call_ret_t543 = mergeU_i75(call_ret_t544, call_ret_t545);
              switch_ret_t542 = call_ret_t543;
              break;
          }
          switch_ret_t536 = switch_ret_t542;
          break;
      }
      switch_ret_t534 = switch_ret_t536;
      break;
  }
  return switch_ret_t534;
}

tll_ptr lam_fun_t547(tll_ptr zs_v88859, tll_env env) {
  tll_ptr call_ret_t546;
  call_ret_t546 = msortU_i77(zs_v88859);
  return call_ret_t546;
}

tll_ptr msortL_i76(tll_ptr zs_v88860) {
  tll_ptr __v88865; tll_ptr call_ret_t554; tll_ptr call_ret_t558;
  tll_ptr call_ret_t559; tll_ptr call_ret_t560; tll_ptr consUL_t553;
  tll_ptr consUL_t555; tll_ptr consUL_t556; tll_ptr nilUL_t550;
  tll_ptr nilUL_t552; tll_ptr switch_ret_t549; tll_ptr switch_ret_t551;
  tll_ptr switch_ret_t557; tll_ptr x_v88861; tll_ptr xs_v88866;
  tll_ptr y_v88863; tll_ptr ys_v88867; tll_ptr zs_v88862; tll_ptr zs_v88864;
  switch(((tll_node)zs_v88860)->tag) {
    case 25:
      instr_free_struct(zs_v88860);
      instr_struct(&nilUL_t550, 25, 0);
      switch_ret_t549 = nilUL_t550;
      break;
    case 26:
      x_v88861 = ((tll_node)zs_v88860)->data[0];
      zs_v88862 = ((tll_node)zs_v88860)->data[1];
      instr_free_struct(zs_v88860);
      switch(((tll_node)zs_v88862)->tag) {
        case 25:
          instr_free_struct(zs_v88862);
          instr_struct(&nilUL_t552, 25, 0);
          instr_struct(&consUL_t553, 26, 2, x_v88861, nilUL_t552);
          switch_ret_t551 = consUL_t553;
          break;
        case 26:
          y_v88863 = ((tll_node)zs_v88862)->data[0];
          zs_v88864 = ((tll_node)zs_v88862)->data[1];
          instr_free_struct(zs_v88862);
          instr_struct(&consUL_t555, 26, 2, y_v88863, zs_v88864);
          instr_struct(&consUL_t556, 26, 2, x_v88861, consUL_t555);
          call_ret_t554 = splitL_i72(consUL_t556);
          __v88865 = call_ret_t554;
          switch(((tll_node)__v88865)->tag) {
            case 0:
              xs_v88866 = ((tll_node)__v88865)->data[0];
              ys_v88867 = ((tll_node)__v88865)->data[1];
              instr_free_struct(__v88865);
              call_ret_t559 = msortL_i76(xs_v88866);
              call_ret_t560 = msortL_i76(ys_v88867);
              call_ret_t558 = mergeL_i74(call_ret_t559, call_ret_t560);
              switch_ret_t557 = call_ret_t558;
              break;
          }
          switch_ret_t551 = switch_ret_t557;
          break;
      }
      switch_ret_t549 = switch_ret_t551;
      break;
  }
  return switch_ret_t549;
}

tll_ptr lam_fun_t562(tll_ptr zs_v88868, tll_env env) {
  tll_ptr call_ret_t561;
  call_ret_t561 = msortL_i76(zs_v88868);
  return call_ret_t561;
}

tll_ptr lam_fun_t568(tll_ptr __v88872, tll_env env) {
  tll_ptr UniqU_t567; tll_ptr c_v88874; tll_ptr nilUU_t566;
  tll_ptr send_ch_t565;
  instr_struct(&nilUU_t566, 27, 0);
  instr_struct(&UniqU_t567, 30, 2, nilUU_t566, 0);
  instr_send(&send_ch_t565, env[0], UniqU_t567);
  c_v88874 = send_ch_t565;
  return 0;
}

tll_ptr lam_fun_t575(tll_ptr __v88877, tll_env env) {
  tll_ptr UniqU_t574; tll_ptr c_v88879; tll_ptr consUU_t573;
  tll_ptr nilUU_t572; tll_ptr send_ch_t571;
  instr_struct(&nilUU_t572, 27, 0);
  instr_struct(&consUU_t573, 28, 2, env[0], nilUU_t572);
  instr_struct(&UniqU_t574, 30, 2, consUU_t573, 0);
  instr_send(&send_ch_t571, env[1], UniqU_t574);
  c_v88879 = send_ch_t571;
  return 0;
}

tll_ptr fork_fun_t584(tll_env env) {
  tll_ptr add_ret_t582; tll_ptr app_ret_t583; tll_ptr call_ret_t581;
  tll_ptr fork_ret_t586;
  add_ret_t582 = env[2] - 1;
  call_ret_t581 = cmsort_workerU_i81(add_ret_t582, env[1], env[0]);
  instr_app(&app_ret_t583, call_ret_t581, 0);
  instr_free_clo(call_ret_t581);
  fork_ret_t586 = app_ret_t583;
  instr_free_thread(env);
  return fork_ret_t586;
}

tll_ptr fork_fun_t590(tll_env env) {
  tll_ptr add_ret_t588; tll_ptr app_ret_t589; tll_ptr call_ret_t587;
  tll_ptr fork_ret_t592;
  add_ret_t588 = env[2] - 1;
  call_ret_t587 = cmsort_workerU_i81(add_ret_t588, env[1], env[0]);
  instr_app(&app_ret_t589, call_ret_t587, 0);
  instr_free_clo(call_ret_t587);
  fork_ret_t592 = app_ret_t589;
  instr_free_thread(env);
  return fork_ret_t592;
}

tll_ptr lam_fun_t604(tll_ptr __v88884, tll_env env) {
  tll_ptr UniqU_t601; tll_ptr __v88907; tll_ptr __v88910; tll_ptr __v88919;
  tll_ptr __v88920; tll_ptr c_v88918; tll_ptr call_ret_t599;
  tll_ptr close_tmp_t602; tll_ptr close_tmp_t603; tll_ptr fork_ch_t585;
  tll_ptr fork_ch_t591; tll_ptr msg1_v88908; tll_ptr msg2_v88911;
  tll_ptr pf1_v88914; tll_ptr pf2_v88916; tll_ptr r1_v88903;
  tll_ptr r1_v88909; tll_ptr r2_v88905; tll_ptr r2_v88912;
  tll_ptr recv_msg_t593; tll_ptr recv_msg_t595; tll_ptr send_ch_t600;
  tll_ptr switch_ret_t594; tll_ptr switch_ret_t596; tll_ptr switch_ret_t597;
  tll_ptr switch_ret_t598; tll_ptr xs1_v88913; tll_ptr xs2_v88915;
  tll_ptr zs_v88917;
  instr_fork(&fork_ch_t585, &fork_fun_t584, 2, env[1], env[3]);
  r1_v88903 = fork_ch_t585;
  instr_fork(&fork_ch_t591, &fork_fun_t590, 2, env[0], env[3]);
  r2_v88905 = fork_ch_t591;
  instr_recv(&recv_msg_t593, r1_v88903);
  __v88907 = recv_msg_t593;
  switch(((tll_node)__v88907)->tag) {
    case 0:
      msg1_v88908 = ((tll_node)__v88907)->data[0];
      r1_v88909 = ((tll_node)__v88907)->data[1];
      instr_free_struct(__v88907);
      instr_recv(&recv_msg_t595, r2_v88905);
      __v88910 = recv_msg_t595;
      switch(((tll_node)__v88910)->tag) {
        case 0:
          msg2_v88911 = ((tll_node)__v88910)->data[0];
          r2_v88912 = ((tll_node)__v88910)->data[1];
          instr_free_struct(__v88910);
          switch(((tll_node)msg1_v88908)->tag) {
            case 30:
              xs1_v88913 = ((tll_node)msg1_v88908)->data[0];
              pf1_v88914 = ((tll_node)msg1_v88908)->data[1];
              switch(((tll_node)msg2_v88911)->tag) {
                case 30:
                  xs2_v88915 = ((tll_node)msg2_v88911)->data[0];
                  pf2_v88916 = ((tll_node)msg2_v88911)->data[1];
                  call_ret_t599 = mergeU_i75(xs1_v88913, xs2_v88915);
                  zs_v88917 = call_ret_t599;
                  instr_struct(&UniqU_t601, 30, 2, zs_v88917, 0);
                  instr_send(&send_ch_t600, env[2], UniqU_t601);
                  c_v88918 = send_ch_t600;
                  instr_close(&close_tmp_t602, r1_v88909);
                  __v88919 = close_tmp_t602;
                  instr_close(&close_tmp_t603, r2_v88912);
                  __v88920 = close_tmp_t603;
                  switch_ret_t598 = 0;
                  break;
              }
              switch_ret_t597 = switch_ret_t598;
              break;
          }
          switch_ret_t596 = switch_ret_t597;
          break;
      }
      switch_ret_t594 = switch_ret_t596;
      break;
  }
  return switch_ret_t594;
}

tll_ptr lam_fun_t609(tll_ptr __v88921, tll_env env) {
  tll_ptr UniqU_t607; tll_ptr c_v88924; tll_ptr call_ret_t606;
  tll_ptr send_ch_t608; tll_ptr x_v88925;
  call_ret_t606 = msortU_i77(env[1]);
  instr_struct(&UniqU_t607, 30, 2, call_ret_t606, 0);
  x_v88925 = UniqU_t607;
  instr_send(&send_ch_t608, env[0], x_v88925);
  c_v88924 = send_ch_t608;
  return 0;
}

tll_ptr cmsort_workerU_i81(tll_ptr n_v88869, tll_ptr zs_v88870, tll_ptr c_v88871) {
  tll_ptr call_ret_t577; tll_ptr consUU_t578; tll_ptr consUU_t579;
  tll_ptr ifte_ret_t611; tll_ptr lam_clo_t569; tll_ptr lam_clo_t576;
  tll_ptr lam_clo_t605; tll_ptr lam_clo_t610; tll_ptr switch_ret_t564;
  tll_ptr switch_ret_t570; tll_ptr switch_ret_t580; tll_ptr xs0_v88882;
  tll_ptr ys0_v88883; tll_ptr z0_v88875; tll_ptr z1_v88880;
  tll_ptr zs0_v88876; tll_ptr zs1_v88881;
  if (n_v88869) {
    switch(((tll_node)zs_v88870)->tag) {
      case 27:
        instr_clo(&lam_clo_t569, &lam_fun_t568, 1, c_v88871);
        switch_ret_t564 = lam_clo_t569;
        break;
      case 28:
        z0_v88875 = ((tll_node)zs_v88870)->data[0];
        zs0_v88876 = ((tll_node)zs_v88870)->data[1];
        switch(((tll_node)zs0_v88876)->tag) {
          case 27:
            instr_clo(&lam_clo_t576, &lam_fun_t575, 2, z0_v88875, c_v88871);
            switch_ret_t570 = lam_clo_t576;
            break;
          case 28:
            z1_v88880 = ((tll_node)zs0_v88876)->data[0];
            zs1_v88881 = ((tll_node)zs0_v88876)->data[1];
            instr_struct(&consUU_t578, 28, 2, z1_v88880, zs1_v88881);
            instr_struct(&consUU_t579, 28, 2, z0_v88875, consUU_t578);
            call_ret_t577 = splitU_i73(consUU_t579);
            switch(((tll_node)call_ret_t577)->tag) {
              case 0:
                xs0_v88882 = ((tll_node)call_ret_t577)->data[0];
                ys0_v88883 = ((tll_node)call_ret_t577)->data[1];
                instr_free_struct(call_ret_t577);
                instr_clo(&lam_clo_t605, &lam_fun_t604, 4,
                          ys0_v88883, xs0_v88882, c_v88871, n_v88869);
                switch_ret_t580 = lam_clo_t605;
                break;
            }
            switch_ret_t570 = switch_ret_t580;
            break;
        }
        switch_ret_t564 = switch_ret_t570;
        break;
    }
    ifte_ret_t611 = switch_ret_t564;
  }
  else {
    instr_clo(&lam_clo_t610, &lam_fun_t609, 2, c_v88871, zs_v88870);
    ifte_ret_t611 = lam_clo_t610;
  }
  return ifte_ret_t611;
}

tll_ptr lam_fun_t613(tll_ptr c_v88931, tll_env env) {
  tll_ptr call_ret_t612;
  call_ret_t612 = cmsort_workerU_i81(env[1], env[0], c_v88931);
  return call_ret_t612;
}

tll_ptr lam_fun_t615(tll_ptr zs_v88929, tll_env env) {
  tll_ptr lam_clo_t614;
  instr_clo(&lam_clo_t614, &lam_fun_t613, 2, zs_v88929, env[0]);
  return lam_clo_t614;
}

tll_ptr lam_fun_t617(tll_ptr n_v88926, tll_env env) {
  tll_ptr lam_clo_t616;
  instr_clo(&lam_clo_t616, &lam_fun_t615, 1, n_v88926);
  return lam_clo_t616;
}

tll_ptr lam_fun_t623(tll_ptr __v88935, tll_env env) {
  tll_ptr UniqL_t622; tll_ptr c_v88937; tll_ptr nilUL_t621;
  tll_ptr send_ch_t620;
  instr_struct(&nilUL_t621, 25, 0);
  instr_struct(&UniqL_t622, 29, 2, nilUL_t621, 0);
  instr_send(&send_ch_t620, env[0], UniqL_t622);
  c_v88937 = send_ch_t620;
  return 0;
}

tll_ptr lam_fun_t630(tll_ptr __v88940, tll_env env) {
  tll_ptr UniqL_t629; tll_ptr c_v88942; tll_ptr consUL_t628;
  tll_ptr nilUL_t627; tll_ptr send_ch_t626;
  instr_struct(&nilUL_t627, 25, 0);
  instr_struct(&consUL_t628, 26, 2, env[0], nilUL_t627);
  instr_struct(&UniqL_t629, 29, 2, consUL_t628, 0);
  instr_send(&send_ch_t626, env[1], UniqL_t629);
  c_v88942 = send_ch_t626;
  return 0;
}

tll_ptr fork_fun_t639(tll_env env) {
  tll_ptr add_ret_t637; tll_ptr app_ret_t638; tll_ptr call_ret_t636;
  tll_ptr fork_ret_t641;
  add_ret_t637 = env[2] - 1;
  call_ret_t636 = cmsort_workerL_i80(add_ret_t637, env[1], env[0]);
  instr_app(&app_ret_t638, call_ret_t636, 0);
  instr_free_clo(call_ret_t636);
  fork_ret_t641 = app_ret_t638;
  instr_free_thread(env);
  return fork_ret_t641;
}

tll_ptr fork_fun_t645(tll_env env) {
  tll_ptr add_ret_t643; tll_ptr app_ret_t644; tll_ptr call_ret_t642;
  tll_ptr fork_ret_t647;
  add_ret_t643 = env[2] - 1;
  call_ret_t642 = cmsort_workerL_i80(add_ret_t643, env[1], env[0]);
  instr_app(&app_ret_t644, call_ret_t642, 0);
  instr_free_clo(call_ret_t642);
  fork_ret_t647 = app_ret_t644;
  instr_free_thread(env);
  return fork_ret_t647;
}

tll_ptr lam_fun_t659(tll_ptr __v88947, tll_env env) {
  tll_ptr UniqL_t656; tll_ptr __v88970; tll_ptr __v88973; tll_ptr __v88982;
  tll_ptr __v88983; tll_ptr c_v88981; tll_ptr call_ret_t654;
  tll_ptr close_tmp_t657; tll_ptr close_tmp_t658; tll_ptr fork_ch_t640;
  tll_ptr fork_ch_t646; tll_ptr msg1_v88971; tll_ptr msg2_v88974;
  tll_ptr pf1_v88977; tll_ptr pf2_v88979; tll_ptr r1_v88966;
  tll_ptr r1_v88972; tll_ptr r2_v88968; tll_ptr r2_v88975;
  tll_ptr recv_msg_t648; tll_ptr recv_msg_t650; tll_ptr send_ch_t655;
  tll_ptr switch_ret_t649; tll_ptr switch_ret_t651; tll_ptr switch_ret_t652;
  tll_ptr switch_ret_t653; tll_ptr xs1_v88976; tll_ptr xs2_v88978;
  tll_ptr zs_v88980;
  instr_fork(&fork_ch_t640, &fork_fun_t639, 2, env[1], env[3]);
  r1_v88966 = fork_ch_t640;
  instr_fork(&fork_ch_t646, &fork_fun_t645, 2, env[0], env[3]);
  r2_v88968 = fork_ch_t646;
  instr_recv(&recv_msg_t648, r1_v88966);
  __v88970 = recv_msg_t648;
  switch(((tll_node)__v88970)->tag) {
    case 0:
      msg1_v88971 = ((tll_node)__v88970)->data[0];
      r1_v88972 = ((tll_node)__v88970)->data[1];
      instr_free_struct(__v88970);
      instr_recv(&recv_msg_t650, r2_v88968);
      __v88973 = recv_msg_t650;
      switch(((tll_node)__v88973)->tag) {
        case 0:
          msg2_v88974 = ((tll_node)__v88973)->data[0];
          r2_v88975 = ((tll_node)__v88973)->data[1];
          instr_free_struct(__v88973);
          switch(((tll_node)msg1_v88971)->tag) {
            case 29:
              xs1_v88976 = ((tll_node)msg1_v88971)->data[0];
              pf1_v88977 = ((tll_node)msg1_v88971)->data[1];
              instr_free_struct(msg1_v88971);
              switch(((tll_node)msg2_v88974)->tag) {
                case 29:
                  xs2_v88978 = ((tll_node)msg2_v88974)->data[0];
                  pf2_v88979 = ((tll_node)msg2_v88974)->data[1];
                  instr_free_struct(msg2_v88974);
                  call_ret_t654 = mergeL_i74(xs1_v88976, xs2_v88978);
                  zs_v88980 = call_ret_t654;
                  instr_struct(&UniqL_t656, 29, 2, zs_v88980, 0);
                  instr_send(&send_ch_t655, env[2], UniqL_t656);
                  c_v88981 = send_ch_t655;
                  instr_close(&close_tmp_t657, r1_v88972);
                  __v88982 = close_tmp_t657;
                  instr_close(&close_tmp_t658, r2_v88975);
                  __v88983 = close_tmp_t658;
                  switch_ret_t653 = 0;
                  break;
              }
              switch_ret_t652 = switch_ret_t653;
              break;
          }
          switch_ret_t651 = switch_ret_t652;
          break;
      }
      switch_ret_t649 = switch_ret_t651;
      break;
  }
  return switch_ret_t649;
}

tll_ptr lam_fun_t664(tll_ptr __v88984, tll_env env) {
  tll_ptr UniqL_t662; tll_ptr c_v88987; tll_ptr call_ret_t661;
  tll_ptr send_ch_t663; tll_ptr x_v88988;
  call_ret_t661 = msortL_i76(env[1]);
  instr_struct(&UniqL_t662, 29, 2, call_ret_t661, 0);
  x_v88988 = UniqL_t662;
  instr_send(&send_ch_t663, env[0], x_v88988);
  c_v88987 = send_ch_t663;
  return 0;
}

tll_ptr cmsort_workerL_i80(tll_ptr n_v88932, tll_ptr zs_v88933, tll_ptr c_v88934) {
  tll_ptr call_ret_t632; tll_ptr consUL_t633; tll_ptr consUL_t634;
  tll_ptr ifte_ret_t666; tll_ptr lam_clo_t624; tll_ptr lam_clo_t631;
  tll_ptr lam_clo_t660; tll_ptr lam_clo_t665; tll_ptr switch_ret_t619;
  tll_ptr switch_ret_t625; tll_ptr switch_ret_t635; tll_ptr xs0_v88945;
  tll_ptr ys0_v88946; tll_ptr z0_v88938; tll_ptr z1_v88943;
  tll_ptr zs0_v88939; tll_ptr zs1_v88944;
  if (n_v88932) {
    switch(((tll_node)zs_v88933)->tag) {
      case 25:
        instr_free_struct(zs_v88933);
        instr_clo(&lam_clo_t624, &lam_fun_t623, 1, c_v88934);
        switch_ret_t619 = lam_clo_t624;
        break;
      case 26:
        z0_v88938 = ((tll_node)zs_v88933)->data[0];
        zs0_v88939 = ((tll_node)zs_v88933)->data[1];
        instr_free_struct(zs_v88933);
        switch(((tll_node)zs0_v88939)->tag) {
          case 25:
            instr_free_struct(zs0_v88939);
            instr_clo(&lam_clo_t631, &lam_fun_t630, 2, z0_v88938, c_v88934);
            switch_ret_t625 = lam_clo_t631;
            break;
          case 26:
            z1_v88943 = ((tll_node)zs0_v88939)->data[0];
            zs1_v88944 = ((tll_node)zs0_v88939)->data[1];
            instr_free_struct(zs0_v88939);
            instr_struct(&consUL_t633, 26, 2, z1_v88943, zs1_v88944);
            instr_struct(&consUL_t634, 26, 2, z0_v88938, consUL_t633);
            call_ret_t632 = splitL_i72(consUL_t634);
            switch(((tll_node)call_ret_t632)->tag) {
              case 0:
                xs0_v88945 = ((tll_node)call_ret_t632)->data[0];
                ys0_v88946 = ((tll_node)call_ret_t632)->data[1];
                instr_free_struct(call_ret_t632);
                instr_clo(&lam_clo_t660, &lam_fun_t659, 4,
                          ys0_v88946, xs0_v88945, c_v88934, n_v88932);
                switch_ret_t635 = lam_clo_t660;
                break;
            }
            switch_ret_t625 = switch_ret_t635;
            break;
        }
        switch_ret_t619 = switch_ret_t625;
        break;
    }
    ifte_ret_t666 = switch_ret_t619;
  }
  else {
    instr_clo(&lam_clo_t665, &lam_fun_t664, 2, c_v88934, zs_v88933);
    ifte_ret_t666 = lam_clo_t665;
  }
  return ifte_ret_t666;
}

tll_ptr lam_fun_t668(tll_ptr c_v88994, tll_env env) {
  tll_ptr call_ret_t667;
  call_ret_t667 = cmsort_workerL_i80(env[1], env[0], c_v88994);
  return call_ret_t667;
}

tll_ptr lam_fun_t670(tll_ptr zs_v88992, tll_env env) {
  tll_ptr lam_clo_t669;
  instr_clo(&lam_clo_t669, &lam_fun_t668, 2, zs_v88992, env[0]);
  return lam_clo_t669;
}

tll_ptr lam_fun_t672(tll_ptr n_v88989, tll_env env) {
  tll_ptr lam_clo_t671;
  instr_clo(&lam_clo_t671, &lam_fun_t670, 1, n_v88989);
  return lam_clo_t671;
}

tll_ptr fork_fun_t676(tll_env env) {
  tll_ptr app_ret_t675; tll_ptr call_ret_t674; tll_ptr fork_ret_t678;
  call_ret_t674 = cmsort_workerU_i81((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t675, call_ret_t674, 0);
  instr_free_clo(call_ret_t674);
  fork_ret_t678 = app_ret_t675;
  instr_free_thread(env);
  return fork_ret_t678;
}

tll_ptr lam_fun_t682(tll_ptr __v88996, tll_env env) {
  tll_ptr __v89005; tll_ptr __v89008; tll_ptr c_v89003; tll_ptr c_v89007;
  tll_ptr close_tmp_t681; tll_ptr fork_ch_t677; tll_ptr msg_v89006;
  tll_ptr recv_msg_t679; tll_ptr switch_ret_t680;
  instr_fork(&fork_ch_t677, &fork_fun_t676, 1, env[0]);
  c_v89003 = fork_ch_t677;
  instr_recv(&recv_msg_t679, c_v89003);
  __v89005 = recv_msg_t679;
  switch(((tll_node)__v89005)->tag) {
    case 0:
      msg_v89006 = ((tll_node)__v89005)->data[0];
      c_v89007 = ((tll_node)__v89005)->data[1];
      instr_free_struct(__v89005);
      instr_close(&close_tmp_t681, c_v89007);
      __v89008 = close_tmp_t681;
      switch_ret_t680 = msg_v89006;
      break;
  }
  return switch_ret_t680;
}

tll_ptr cmsortU_i83(tll_ptr zs_v88995) {
  tll_ptr lam_clo_t683;
  instr_clo(&lam_clo_t683, &lam_fun_t682, 1, zs_v88995);
  return lam_clo_t683;
}

tll_ptr lam_fun_t685(tll_ptr zs_v89009, tll_env env) {
  tll_ptr call_ret_t684;
  call_ret_t684 = cmsortU_i83(zs_v89009);
  return call_ret_t684;
}

tll_ptr fork_fun_t689(tll_env env) {
  tll_ptr app_ret_t688; tll_ptr call_ret_t687; tll_ptr fork_ret_t691;
  call_ret_t687 = cmsort_workerL_i80((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t688, call_ret_t687, 0);
  instr_free_clo(call_ret_t687);
  fork_ret_t691 = app_ret_t688;
  instr_free_thread(env);
  return fork_ret_t691;
}

tll_ptr lam_fun_t695(tll_ptr __v89011, tll_env env) {
  tll_ptr __v89020; tll_ptr __v89023; tll_ptr c_v89018; tll_ptr c_v89022;
  tll_ptr close_tmp_t694; tll_ptr fork_ch_t690; tll_ptr msg_v89021;
  tll_ptr recv_msg_t692; tll_ptr switch_ret_t693;
  instr_fork(&fork_ch_t690, &fork_fun_t689, 1, env[0]);
  c_v89018 = fork_ch_t690;
  instr_recv(&recv_msg_t692, c_v89018);
  __v89020 = recv_msg_t692;
  switch(((tll_node)__v89020)->tag) {
    case 0:
      msg_v89021 = ((tll_node)__v89020)->data[0];
      c_v89022 = ((tll_node)__v89020)->data[1];
      instr_free_struct(__v89020);
      instr_close(&close_tmp_t694, c_v89022);
      __v89023 = close_tmp_t694;
      switch_ret_t693 = msg_v89021;
      break;
  }
  return switch_ret_t693;
}

tll_ptr cmsortL_i82(tll_ptr zs_v89010) {
  tll_ptr lam_clo_t696;
  instr_clo(&lam_clo_t696, &lam_fun_t695, 1, zs_v89010);
  return lam_clo_t696;
}

tll_ptr lam_fun_t698(tll_ptr zs_v89024, tll_env env) {
  tll_ptr call_ret_t697;
  call_ret_t697 = cmsortL_i82(zs_v89024);
  return call_ret_t697;
}

tll_ptr mkListU_i85(tll_ptr n_v89025) {
  tll_ptr add_ret_t701; tll_ptr call_ret_t700; tll_ptr consUU_t702;
  tll_ptr ifte_ret_t704; tll_ptr nilUU_t703;
  if (n_v89025) {
    add_ret_t701 = n_v89025 - 1;
    call_ret_t700 = mkListU_i85(add_ret_t701);
    instr_struct(&consUU_t702, 28, 2, n_v89025, call_ret_t700);
    ifte_ret_t704 = consUU_t702;
  }
  else {
    instr_struct(&nilUU_t703, 27, 0);
    ifte_ret_t704 = nilUU_t703;
  }
  return ifte_ret_t704;
}

tll_ptr lam_fun_t706(tll_ptr n_v89026, tll_env env) {
  tll_ptr call_ret_t705;
  call_ret_t705 = mkListU_i85(n_v89026);
  return call_ret_t705;
}

tll_ptr mkListL_i84(tll_ptr n_v89027) {
  tll_ptr add_ret_t709; tll_ptr call_ret_t708; tll_ptr consUL_t710;
  tll_ptr ifte_ret_t712; tll_ptr nilUL_t711;
  if (n_v89027) {
    add_ret_t709 = n_v89027 - 1;
    call_ret_t708 = mkListL_i84(add_ret_t709);
    instr_struct(&consUL_t710, 26, 2, n_v89027, call_ret_t708);
    ifte_ret_t712 = consUL_t710;
  }
  else {
    instr_struct(&nilUL_t711, 25, 0);
    ifte_ret_t712 = nilUL_t711;
  }
  return ifte_ret_t712;
}

tll_ptr lam_fun_t714(tll_ptr n_v89028, tll_env env) {
  tll_ptr call_ret_t713;
  call_ret_t713 = mkListL_i84(n_v89028);
  return call_ret_t713;
}

tll_ptr free_i50(tll_ptr A_v89029, tll_ptr ls_v89030) {
  tll_ptr __v89031; tll_ptr call_ret_t717; tll_ptr ls_v89032;
  tll_ptr switch_ret_t716;
  switch(((tll_node)ls_v89030)->tag) {
    case 25:
      instr_free_struct(ls_v89030);
      switch_ret_t716 = 0;
      break;
    case 26:
      __v89031 = ((tll_node)ls_v89030)->data[0];
      ls_v89032 = ((tll_node)ls_v89030)->data[1];
      instr_free_struct(ls_v89030);
      call_ret_t717 = free_i50(0, ls_v89032);
      switch_ret_t716 = call_ret_t717;
      break;
  }
  return switch_ret_t716;
}

tll_ptr lam_fun_t719(tll_ptr ls_v89035, tll_env env) {
  tll_ptr call_ret_t718;
  call_ret_t718 = free_i50(env[0], ls_v89035);
  return call_ret_t718;
}

tll_ptr lam_fun_t721(tll_ptr A_v89033, tll_env env) {
  tll_ptr lam_clo_t720;
  instr_clo(&lam_clo_t720, &lam_fun_t719, 1, A_v89033);
  return lam_clo_t720;
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
  tll_ptr String_t363; tll_ptr String_t366; tll_ptr __v89039;
  tll_ptr __v89040; tll_ptr app_ret_t725; tll_ptr call_ret_t723;
  tll_ptr call_ret_t724; tll_ptr call_ret_t727; tll_ptr consUU_t368;
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
  tll_ptr lam_clo_t463; tll_ptr lam_clo_t467; tll_ptr lam_clo_t484;
  tll_ptr lam_clo_t501; tll_ptr lam_clo_t517; tll_ptr lam_clo_t52;
  tll_ptr lam_clo_t533; tll_ptr lam_clo_t548; tll_ptr lam_clo_t563;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t6; tll_ptr lam_clo_t618;
  tll_ptr lam_clo_t673; tll_ptr lam_clo_t686; tll_ptr lam_clo_t699;
  tll_ptr lam_clo_t707; tll_ptr lam_clo_t715; tll_ptr lam_clo_t72;
  tll_ptr lam_clo_t722; tll_ptr lam_clo_t77; tll_ptr lam_clo_t83;
  tll_ptr lam_clo_t92; tll_ptr lam_clo_t98; tll_ptr msg_v89037;
  tll_ptr nilUU_t367; tll_ptr sorted_v89038; tll_ptr switch_ret_t726;
  tll_ptr test_v89036;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i86 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i87 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i88 = lam_clo_t16;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  comparebclo_i89 = lam_clo_t28;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 0);
  ltenclo_i90 = lam_clo_t34;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 0);
  ltnclo_i91 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  gtenclo_i92 = lam_clo_t46;
  instr_clo(&lam_clo_t52, &lam_fun_t51, 0);
  gtnclo_i93 = lam_clo_t52;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  eqnclo_i94 = lam_clo_t58;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  comparenclo_i95 = lam_clo_t72;
  instr_clo(&lam_clo_t77, &lam_fun_t76, 0);
  predclo_i96 = lam_clo_t77;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i97 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i98 = lam_clo_t92;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  mulnclo_i99 = lam_clo_t98;
  instr_clo(&lam_clo_t104, &lam_fun_t103, 0);
  divnclo_i100 = lam_clo_t104;
  instr_clo(&lam_clo_t110, &lam_fun_t109, 0);
  modnclo_i101 = lam_clo_t110;
  instr_clo(&lam_clo_t118, &lam_fun_t117, 0);
  eqcclo_i102 = lam_clo_t118;
  instr_clo(&lam_clo_t126, &lam_fun_t125, 0);
  comparecclo_i103 = lam_clo_t126;
  instr_clo(&lam_clo_t134, &lam_fun_t133, 0);
  catsclo_i104 = lam_clo_t134;
  instr_clo(&lam_clo_t140, &lam_fun_t139, 0);
  strlenclo_i105 = lam_clo_t140;
  instr_clo(&lam_clo_t151, &lam_fun_t150, 0);
  eqsclo_i106 = lam_clo_t151;
  instr_clo(&lam_clo_t167, &lam_fun_t166, 0);
  comparesclo_i107 = lam_clo_t167;
  instr_clo(&lam_clo_t179, &lam_fun_t178, 0);
  and_thenUUUclo_i108 = lam_clo_t179;
  instr_clo(&lam_clo_t191, &lam_fun_t190, 0);
  and_thenUULclo_i109 = lam_clo_t191;
  instr_clo(&lam_clo_t203, &lam_fun_t202, 0);
  and_thenULUclo_i110 = lam_clo_t203;
  instr_clo(&lam_clo_t215, &lam_fun_t214, 0);
  and_thenULLclo_i111 = lam_clo_t215;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 0);
  and_thenLULclo_i112 = lam_clo_t227;
  instr_clo(&lam_clo_t239, &lam_fun_t238, 0);
  and_thenLLLclo_i113 = lam_clo_t239;
  instr_clo(&lam_clo_t252, &lam_fun_t251, 0);
  lenUUclo_i114 = lam_clo_t252;
  instr_clo(&lam_clo_t265, &lam_fun_t264, 0);
  lenULclo_i115 = lam_clo_t265;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 0);
  lenLLclo_i116 = lam_clo_t278;
  instr_clo(&lam_clo_t288, &lam_fun_t287, 0);
  appendUUclo_i117 = lam_clo_t288;
  instr_clo(&lam_clo_t298, &lam_fun_t297, 0);
  appendULclo_i118 = lam_clo_t298;
  instr_clo(&lam_clo_t308, &lam_fun_t307, 0);
  appendLLclo_i119 = lam_clo_t308;
  instr_clo(&lam_clo_t318, &lam_fun_t317, 0);
  readlineclo_i120 = lam_clo_t318;
  instr_clo(&lam_clo_t327, &lam_fun_t326, 0);
  printclo_i121 = lam_clo_t327;
  instr_clo(&lam_clo_t336, &lam_fun_t335, 0);
  prerrclo_i122 = lam_clo_t336;
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
  get_atclo_i123 = lam_clo_t391;
  instr_clo(&lam_clo_t396, &lam_fun_t395, 0);
  string_of_digitclo_i124 = lam_clo_t396;
  instr_clo(&lam_clo_t406, &lam_fun_t405, 0);
  string_of_natclo_i125 = lam_clo_t406;
  instr_clo(&lam_clo_t450, &lam_fun_t449, 0);
  digit_of_charclo_i126 = lam_clo_t450;
  instr_clo(&lam_clo_t463, &lam_fun_t462, 0);
  nat_of_string_loopclo_i127 = lam_clo_t463;
  instr_clo(&lam_clo_t467, &lam_fun_t466, 0);
  nat_of_stringclo_i128 = lam_clo_t467;
  instr_clo(&lam_clo_t484, &lam_fun_t483, 0);
  splitUclo_i129 = lam_clo_t484;
  instr_clo(&lam_clo_t501, &lam_fun_t500, 0);
  splitLclo_i130 = lam_clo_t501;
  instr_clo(&lam_clo_t517, &lam_fun_t516, 0);
  mergeUclo_i131 = lam_clo_t517;
  instr_clo(&lam_clo_t533, &lam_fun_t532, 0);
  mergeLclo_i132 = lam_clo_t533;
  instr_clo(&lam_clo_t548, &lam_fun_t547, 0);
  msortUclo_i133 = lam_clo_t548;
  instr_clo(&lam_clo_t563, &lam_fun_t562, 0);
  msortLclo_i134 = lam_clo_t563;
  instr_clo(&lam_clo_t618, &lam_fun_t617, 0);
  cmsort_workerUclo_i135 = lam_clo_t618;
  instr_clo(&lam_clo_t673, &lam_fun_t672, 0);
  cmsort_workerLclo_i136 = lam_clo_t673;
  instr_clo(&lam_clo_t686, &lam_fun_t685, 0);
  cmsortUclo_i137 = lam_clo_t686;
  instr_clo(&lam_clo_t699, &lam_fun_t698, 0);
  cmsortLclo_i138 = lam_clo_t699;
  instr_clo(&lam_clo_t707, &lam_fun_t706, 0);
  mkListUclo_i139 = lam_clo_t707;
  instr_clo(&lam_clo_t715, &lam_fun_t714, 0);
  mkListLclo_i140 = lam_clo_t715;
  instr_clo(&lam_clo_t722, &lam_fun_t721, 0);
  freeclo_i141 = lam_clo_t722;
  call_ret_t723 = mkListL_i84((tll_ptr)2000000);
  test_v89036 = call_ret_t723;
  call_ret_t724 = cmsortL_i82(test_v89036);
  instr_app(&app_ret_t725, call_ret_t724, 0);
  instr_free_clo(call_ret_t724);
  msg_v89037 = app_ret_t725;
  switch(((tll_node)msg_v89037)->tag) {
    case 29:
      sorted_v89038 = ((tll_node)msg_v89037)->data[0];
      __v89039 = ((tll_node)msg_v89037)->data[1];
      instr_free_struct(msg_v89037);
      call_ret_t727 = free_i50(0, sorted_v89038);
      __v89040 = call_ret_t727;
      switch_ret_t726 = 0;
      break;
  }
  return 0;
}

