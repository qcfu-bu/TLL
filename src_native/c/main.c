#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v904656, tll_ptr b2_v904657);
tll_ptr orb_i2(tll_ptr b1_v904661, tll_ptr b2_v904662);
tll_ptr notb_i3(tll_ptr b_v904666);
tll_ptr compareb_i4(tll_ptr b1_v904668, tll_ptr b2_v904669);
tll_ptr lten_i5(tll_ptr x_v904673, tll_ptr y_v904674);
tll_ptr ltn_i6(tll_ptr x_v904678, tll_ptr y_v904679);
tll_ptr gten_i7(tll_ptr x_v904683, tll_ptr y_v904684);
tll_ptr gtn_i8(tll_ptr x_v904688, tll_ptr y_v904689);
tll_ptr eqn_i9(tll_ptr x_v904693, tll_ptr y_v904694);
tll_ptr comparen_i10(tll_ptr n1_v904698, tll_ptr n2_v904699);
tll_ptr pred_i11(tll_ptr x_v904703);
tll_ptr addn_i12(tll_ptr x_v904705, tll_ptr y_v904706);
tll_ptr subn_i13(tll_ptr x_v904710, tll_ptr y_v904711);
tll_ptr muln_i14(tll_ptr x_v904715, tll_ptr y_v904716);
tll_ptr divn_i15(tll_ptr x_v904720, tll_ptr y_v904721);
tll_ptr modn_i16(tll_ptr x_v904725, tll_ptr y_v904726);
tll_ptr eqc_i17(tll_ptr c1_v904730, tll_ptr c2_v904731);
tll_ptr comparec_i18(tll_ptr c1_v904737, tll_ptr c2_v904738);
tll_ptr cats_i19(tll_ptr s1_v904744, tll_ptr s2_v904745);
tll_ptr strlen_i20(tll_ptr s_v904751);
tll_ptr eqs_i21(tll_ptr s1_v904755, tll_ptr s2_v904756);
tll_ptr compares_i22(tll_ptr s1_v904766, tll_ptr s2_v904767);
tll_ptr and_thenUUU_i78(tll_ptr A_v904777, tll_ptr B_v904778, tll_ptr opt_v904779, tll_ptr f_v904780);
tll_ptr and_thenUUL_i77(tll_ptr A_v904792, tll_ptr B_v904793, tll_ptr opt_v904794, tll_ptr f_v904795);
tll_ptr and_thenULU_i76(tll_ptr A_v904807, tll_ptr B_v904808, tll_ptr opt_v904809, tll_ptr f_v904810);
tll_ptr and_thenULL_i75(tll_ptr A_v904822, tll_ptr B_v904823, tll_ptr opt_v904824, tll_ptr f_v904825);
tll_ptr and_thenLUL_i73(tll_ptr A_v904837, tll_ptr B_v904838, tll_ptr opt_v904839, tll_ptr f_v904840);
tll_ptr and_thenLLL_i71(tll_ptr A_v904852, tll_ptr B_v904853, tll_ptr opt_v904854, tll_ptr f_v904855);
tll_ptr lenUU_i86(tll_ptr A_v904867, tll_ptr xs_v904868);
tll_ptr lenUL_i85(tll_ptr A_v904876, tll_ptr xs_v904877);
tll_ptr lenLL_i83(tll_ptr A_v904885, tll_ptr xs_v904886);
tll_ptr appendUU_i90(tll_ptr A_v904894, tll_ptr xs_v904895, tll_ptr ys_v904896);
tll_ptr appendUL_i89(tll_ptr A_v904905, tll_ptr xs_v904906, tll_ptr ys_v904907);
tll_ptr appendLL_i87(tll_ptr A_v904916, tll_ptr xs_v904917, tll_ptr ys_v904918);
tll_ptr readline_i33(tll_ptr __v904927);
tll_ptr print_i34(tll_ptr s_v904942);
tll_ptr prerr_i35(tll_ptr s_v904953);
tll_ptr get_at_i37(tll_ptr A_v904964, tll_ptr n_v904965, tll_ptr xs_v904966, tll_ptr a_v904967);
tll_ptr string_of_digit_i38(tll_ptr n_v904982);
tll_ptr string_of_nat_i39(tll_ptr n_v904984);
tll_ptr digit_of_char_i40(tll_ptr c_v904988);
tll_ptr nat_of_string_loop_i41(tll_ptr s_v904990, tll_ptr acc_v904991);
tll_ptr nat_of_string_i42(tll_ptr s_v904998);
tll_ptr contains_i51(tll_ptr c_v905000, tll_ptr s_v905001);
tll_ptr string_diff_i52(tll_ptr ans_v905007, tll_ptr s1_v905008, tll_ptr s2_v905009);
tll_ptr word_diff_i54(tll_ptr ans_v905040, tll_ptr guess_v905041);
tll_ptr eqw_i55(tll_ptr w1_v905051, tll_ptr w2_v905052);
tll_ptr read_word_i62(tll_ptr __v905060);
tll_ptr player_loop_i63(tll_ptr ans_v905079, tll_ptr repeat_v905080, tll_ptr c_v905081);
tll_ptr player_i64(tll_ptr c_v905198);
tll_ptr get_at_i66(tll_ptr A_v905217, tll_ptr n_v905218, tll_ptr xs_v905219);
tll_ptr rand_word_i67(tll_ptr __v905235);
tll_ptr server_loop_i68(tll_ptr ans_v905250, tll_ptr repeat_v905251, tll_ptr c_v905252);
tll_ptr server_i69(tll_ptr c_v905310);

tll_ptr addnclo_i110;
tll_ptr and_thenLLLclo_i126;
tll_ptr and_thenLULclo_i125;
tll_ptr and_thenULLclo_i124;
tll_ptr and_thenULUclo_i123;
tll_ptr and_thenUULclo_i122;
tll_ptr and_thenUUUclo_i121;
tll_ptr andbclo_i99;
tll_ptr appendLLclo_i132;
tll_ptr appendULclo_i131;
tll_ptr appendUUclo_i130;
tll_ptr catsclo_i117;
tll_ptr comparebclo_i102;
tll_ptr comparecclo_i116;
tll_ptr comparenclo_i108;
tll_ptr comparesclo_i120;
tll_ptr containsclo_i142;
tll_ptr digit_of_charclo_i139;
tll_ptr digits_i36;
tll_ptr divnclo_i113;
tll_ptr eqcclo_i115;
tll_ptr eqnclo_i107;
tll_ptr eqsclo_i119;
tll_ptr eqwclo_i145;
tll_ptr get_atclo_i136;
tll_ptr get_atclo_i149;
tll_ptr gtenclo_i105;
tll_ptr gtnclo_i106;
tll_ptr lenLLclo_i129;
tll_ptr lenULclo_i128;
tll_ptr lenUUclo_i127;
tll_ptr ltenclo_i103;
tll_ptr ltnclo_i104;
tll_ptr modnclo_i114;
tll_ptr mulnclo_i112;
tll_ptr nat_of_string_loopclo_i140;
tll_ptr nat_of_stringclo_i141;
tll_ptr notbclo_i101;
tll_ptr orbclo_i100;
tll_ptr player_loopclo_i147;
tll_ptr playerclo_i148;
tll_ptr predclo_i109;
tll_ptr prerrclo_i135;
tll_ptr printclo_i134;
tll_ptr rand_wordclo_i150;
tll_ptr read_wordclo_i146;
tll_ptr readlineclo_i133;
tll_ptr server_loopclo_i151;
tll_ptr serverclo_i152;
tll_ptr string_diffclo_i143;
tll_ptr string_of_digitclo_i137;
tll_ptr string_of_natclo_i138;
tll_ptr strlenclo_i118;
tll_ptr subnclo_i111;
tll_ptr word_diffclo_i144;

tll_ptr andb_i1(tll_ptr b1_v904656, tll_ptr b2_v904657) {
  tll_ptr ifte_ret_t1;
  if (b1_v904656) {
    ifte_ret_t1 = b2_v904657;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v904660, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v904660);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v904658, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v904658);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v904661, tll_ptr b2_v904662) {
  tll_ptr ifte_ret_t7;
  if (b1_v904661) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v904662;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v904665, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v904665);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v904663, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v904663);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v904666) {
  tll_ptr ifte_ret_t13;
  if (b_v904666) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v904667, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v904667);
  return call_ret_t14;
}

tll_ptr compareb_i4(tll_ptr b1_v904668, tll_ptr b2_v904669) {
  tll_ptr EQ_t17; tll_ptr EQ_t21; tll_ptr GT_t18; tll_ptr LT_t20;
  tll_ptr ifte_ret_t19; tll_ptr ifte_ret_t22; tll_ptr ifte_ret_t23;
  if (b1_v904668) {
    if (b2_v904669) {
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
    if (b2_v904669) {
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

tll_ptr lam_fun_t25(tll_ptr b2_v904672, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = compareb_i4(env[0], b2_v904672);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr b1_v904670, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, b1_v904670);
  return lam_clo_t26;
}

tll_ptr lten_i5(tll_ptr x_v904673, tll_ptr y_v904674) {
  tll_ptr lten_ret_t29;
  instr_lten(&lten_ret_t29, x_v904673, y_v904674);
  return lten_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v904677, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = lten_i5(env[0], y_v904677);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v904675, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v904675);
  return lam_clo_t32;
}

tll_ptr ltn_i6(tll_ptr x_v904678, tll_ptr y_v904679) {
  tll_ptr ltn_ret_t35;
  instr_ltn(&ltn_ret_t35, x_v904678, y_v904679);
  return ltn_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v904682, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = ltn_i6(env[0], y_v904682);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v904680, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v904680);
  return lam_clo_t38;
}

tll_ptr gten_i7(tll_ptr x_v904683, tll_ptr y_v904684) {
  tll_ptr gten_ret_t41;
  instr_gten(&gten_ret_t41, x_v904683, y_v904684);
  return gten_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v904687, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = gten_i7(env[0], y_v904687);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v904685, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v904685);
  return lam_clo_t44;
}

tll_ptr gtn_i8(tll_ptr x_v904688, tll_ptr y_v904689) {
  tll_ptr gtn_ret_t47;
  instr_gtn(&gtn_ret_t47, x_v904688, y_v904689);
  return gtn_ret_t47;
}

tll_ptr lam_fun_t49(tll_ptr y_v904692, tll_env env) {
  tll_ptr call_ret_t48;
  call_ret_t48 = gtn_i8(env[0], y_v904692);
  return call_ret_t48;
}

tll_ptr lam_fun_t51(tll_ptr x_v904690, tll_env env) {
  tll_ptr lam_clo_t50;
  instr_clo(&lam_clo_t50, &lam_fun_t49, 1, x_v904690);
  return lam_clo_t50;
}

tll_ptr eqn_i9(tll_ptr x_v904693, tll_ptr y_v904694) {
  tll_ptr eqn_ret_t53;
  instr_eqn(&eqn_ret_t53, x_v904693, y_v904694);
  return eqn_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v904697, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = eqn_i9(env[0], y_v904697);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v904695, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v904695);
  return lam_clo_t56;
}

tll_ptr comparen_i10(tll_ptr n1_v904698, tll_ptr n2_v904699) {
  tll_ptr EQ_t65; tll_ptr GT_t62; tll_ptr LT_t64; tll_ptr add_ret_t60;
  tll_ptr add_ret_t61; tll_ptr call_ret_t59; tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t66; tll_ptr ifte_ret_t67;
  if (n1_v904698) {
    if (n2_v904699) {
      add_ret_t60 = n1_v904698 - 1;
      add_ret_t61 = n2_v904699 - 1;
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
    if (n2_v904699) {
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

tll_ptr lam_fun_t69(tll_ptr n2_v904702, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = comparen_i10(env[0], n2_v904702);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr n1_v904700, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, n1_v904700);
  return lam_clo_t70;
}

tll_ptr pred_i11(tll_ptr x_v904703) {
  tll_ptr add_ret_t73; tll_ptr ifte_ret_t74;
  if (x_v904703) {
    add_ret_t73 = x_v904703 - 1;
    ifte_ret_t74 = add_ret_t73;
  }
  else {
    ifte_ret_t74 = (tll_ptr)0;
  }
  return ifte_ret_t74;
}

tll_ptr lam_fun_t76(tll_ptr x_v904704, tll_env env) {
  tll_ptr call_ret_t75;
  call_ret_t75 = pred_i11(x_v904704);
  return call_ret_t75;
}

tll_ptr addn_i12(tll_ptr x_v904705, tll_ptr y_v904706) {
  tll_ptr addn_ret_t78;
  instr_addn(&addn_ret_t78, x_v904705, y_v904706);
  return addn_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v904709, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i12(env[0], y_v904709);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v904707, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v904707);
  return lam_clo_t81;
}

tll_ptr subn_i13(tll_ptr x_v904710, tll_ptr y_v904711) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v904711) {
    call_ret_t85 = pred_i11(x_v904710);
    add_ret_t86 = y_v904711 - 1;
    call_ret_t84 = subn_i13(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v904710;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v904714, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i13(env[0], y_v904714);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v904712, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v904712);
  return lam_clo_t90;
}

tll_ptr muln_i14(tll_ptr x_v904715, tll_ptr y_v904716) {
  tll_ptr muln_ret_t93;
  instr_muln(&muln_ret_t93, x_v904715, y_v904716);
  return muln_ret_t93;
}

tll_ptr lam_fun_t95(tll_ptr y_v904719, tll_env env) {
  tll_ptr call_ret_t94;
  call_ret_t94 = muln_i14(env[0], y_v904719);
  return call_ret_t94;
}

tll_ptr lam_fun_t97(tll_ptr x_v904717, tll_env env) {
  tll_ptr lam_clo_t96;
  instr_clo(&lam_clo_t96, &lam_fun_t95, 1, x_v904717);
  return lam_clo_t96;
}

tll_ptr divn_i15(tll_ptr x_v904720, tll_ptr y_v904721) {
  tll_ptr divn_ret_t99;
  instr_divn(&divn_ret_t99, x_v904720, y_v904721);
  return divn_ret_t99;
}

tll_ptr lam_fun_t101(tll_ptr y_v904724, tll_env env) {
  tll_ptr call_ret_t100;
  call_ret_t100 = divn_i15(env[0], y_v904724);
  return call_ret_t100;
}

tll_ptr lam_fun_t103(tll_ptr x_v904722, tll_env env) {
  tll_ptr lam_clo_t102;
  instr_clo(&lam_clo_t102, &lam_fun_t101, 1, x_v904722);
  return lam_clo_t102;
}

tll_ptr modn_i16(tll_ptr x_v904725, tll_ptr y_v904726) {
  tll_ptr modn_ret_t105;
  instr_modn(&modn_ret_t105, x_v904725, y_v904726);
  return modn_ret_t105;
}

tll_ptr lam_fun_t107(tll_ptr y_v904729, tll_env env) {
  tll_ptr call_ret_t106;
  call_ret_t106 = modn_i16(env[0], y_v904729);
  return call_ret_t106;
}

tll_ptr lam_fun_t109(tll_ptr x_v904727, tll_env env) {
  tll_ptr lam_clo_t108;
  instr_clo(&lam_clo_t108, &lam_fun_t107, 1, x_v904727);
  return lam_clo_t108;
}

tll_ptr eqc_i17(tll_ptr c1_v904730, tll_ptr c2_v904731) {
  tll_ptr call_ret_t113; tll_ptr n1_v904732; tll_ptr n2_v904733;
  tll_ptr switch_ret_t111; tll_ptr switch_ret_t112;
  switch(((tll_node)c1_v904730)->tag) {
    case 5:
      n1_v904732 = ((tll_node)c1_v904730)->data[0];
      switch(((tll_node)c2_v904731)->tag) {
        case 5:
          n2_v904733 = ((tll_node)c2_v904731)->data[0];
          call_ret_t113 = eqn_i9(n1_v904732, n2_v904733);
          switch_ret_t112 = call_ret_t113;
          break;
      }
      switch_ret_t111 = switch_ret_t112;
      break;
  }
  return switch_ret_t111;
}

tll_ptr lam_fun_t115(tll_ptr c2_v904736, tll_env env) {
  tll_ptr call_ret_t114;
  call_ret_t114 = eqc_i17(env[0], c2_v904736);
  return call_ret_t114;
}

tll_ptr lam_fun_t117(tll_ptr c1_v904734, tll_env env) {
  tll_ptr lam_clo_t116;
  instr_clo(&lam_clo_t116, &lam_fun_t115, 1, c1_v904734);
  return lam_clo_t116;
}

tll_ptr comparec_i18(tll_ptr c1_v904737, tll_ptr c2_v904738) {
  tll_ptr call_ret_t121; tll_ptr n1_v904739; tll_ptr n2_v904740;
  tll_ptr switch_ret_t119; tll_ptr switch_ret_t120;
  switch(((tll_node)c1_v904737)->tag) {
    case 5:
      n1_v904739 = ((tll_node)c1_v904737)->data[0];
      switch(((tll_node)c2_v904738)->tag) {
        case 5:
          n2_v904740 = ((tll_node)c2_v904738)->data[0];
          call_ret_t121 = comparen_i10(n1_v904739, n2_v904740);
          switch_ret_t120 = call_ret_t121;
          break;
      }
      switch_ret_t119 = switch_ret_t120;
      break;
  }
  return switch_ret_t119;
}

tll_ptr lam_fun_t123(tll_ptr c2_v904743, tll_env env) {
  tll_ptr call_ret_t122;
  call_ret_t122 = comparec_i18(env[0], c2_v904743);
  return call_ret_t122;
}

tll_ptr lam_fun_t125(tll_ptr c1_v904741, tll_env env) {
  tll_ptr lam_clo_t124;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 1, c1_v904741);
  return lam_clo_t124;
}

tll_ptr cats_i19(tll_ptr s1_v904744, tll_ptr s2_v904745) {
  tll_ptr String_t129; tll_ptr c_v904746; tll_ptr call_ret_t128;
  tll_ptr s1_v904747; tll_ptr switch_ret_t127;
  switch(((tll_node)s1_v904744)->tag) {
    case 6:
      switch_ret_t127 = s2_v904745;
      break;
    case 7:
      c_v904746 = ((tll_node)s1_v904744)->data[0];
      s1_v904747 = ((tll_node)s1_v904744)->data[1];
      call_ret_t128 = cats_i19(s1_v904747, s2_v904745);
      instr_struct(&String_t129, 7, 2, c_v904746, call_ret_t128);
      switch_ret_t127 = String_t129;
      break;
  }
  return switch_ret_t127;
}

tll_ptr lam_fun_t131(tll_ptr s2_v904750, tll_env env) {
  tll_ptr call_ret_t130;
  call_ret_t130 = cats_i19(env[0], s2_v904750);
  return call_ret_t130;
}

tll_ptr lam_fun_t133(tll_ptr s1_v904748, tll_env env) {
  tll_ptr lam_clo_t132;
  instr_clo(&lam_clo_t132, &lam_fun_t131, 1, s1_v904748);
  return lam_clo_t132;
}

tll_ptr strlen_i20(tll_ptr s_v904751) {
  tll_ptr __v904752; tll_ptr add_ret_t137; tll_ptr call_ret_t136;
  tll_ptr s_v904753; tll_ptr switch_ret_t135;
  switch(((tll_node)s_v904751)->tag) {
    case 6:
      switch_ret_t135 = (tll_ptr)0;
      break;
    case 7:
      __v904752 = ((tll_node)s_v904751)->data[0];
      s_v904753 = ((tll_node)s_v904751)->data[1];
      call_ret_t136 = strlen_i20(s_v904753);
      add_ret_t137 = call_ret_t136 + 1;
      switch_ret_t135 = add_ret_t137;
      break;
  }
  return switch_ret_t135;
}

tll_ptr lam_fun_t139(tll_ptr s_v904754, tll_env env) {
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i20(s_v904754);
  return call_ret_t138;
}

tll_ptr eqs_i21(tll_ptr s1_v904755, tll_ptr s2_v904756) {
  tll_ptr __v904757; tll_ptr __v904758; tll_ptr c1_v904759;
  tll_ptr c2_v904761; tll_ptr call_ret_t144; tll_ptr call_ret_t145;
  tll_ptr call_ret_t146; tll_ptr s1_v904760; tll_ptr s2_v904762;
  tll_ptr switch_ret_t141; tll_ptr switch_ret_t142; tll_ptr switch_ret_t143;
  switch(((tll_node)s1_v904755)->tag) {
    case 6:
      switch(((tll_node)s2_v904756)->tag) {
        case 6:
          switch_ret_t142 = (tll_ptr)1;
          break;
        case 7:
          __v904757 = ((tll_node)s2_v904756)->data[0];
          __v904758 = ((tll_node)s2_v904756)->data[1];
          switch_ret_t142 = (tll_ptr)0;
          break;
      }
      switch_ret_t141 = switch_ret_t142;
      break;
    case 7:
      c1_v904759 = ((tll_node)s1_v904755)->data[0];
      s1_v904760 = ((tll_node)s1_v904755)->data[1];
      switch(((tll_node)s2_v904756)->tag) {
        case 6:
          switch_ret_t143 = (tll_ptr)0;
          break;
        case 7:
          c2_v904761 = ((tll_node)s2_v904756)->data[0];
          s2_v904762 = ((tll_node)s2_v904756)->data[1];
          call_ret_t145 = eqc_i17(c1_v904759, c2_v904761);
          call_ret_t146 = eqs_i21(s1_v904760, s2_v904762);
          call_ret_t144 = andb_i1(call_ret_t145, call_ret_t146);
          switch_ret_t143 = call_ret_t144;
          break;
      }
      switch_ret_t141 = switch_ret_t143;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t148(tll_ptr s2_v904765, tll_env env) {
  tll_ptr call_ret_t147;
  call_ret_t147 = eqs_i21(env[0], s2_v904765);
  return call_ret_t147;
}

tll_ptr lam_fun_t150(tll_ptr s1_v904763, tll_env env) {
  tll_ptr lam_clo_t149;
  instr_clo(&lam_clo_t149, &lam_fun_t148, 1, s1_v904763);
  return lam_clo_t149;
}

tll_ptr compares_i22(tll_ptr s1_v904766, tll_ptr s2_v904767) {
  tll_ptr EQ_t154; tll_ptr GT_t157; tll_ptr GT_t162; tll_ptr LT_t155;
  tll_ptr LT_t161; tll_ptr __v904768; tll_ptr __v904769; tll_ptr c1_v904770;
  tll_ptr c2_v904772; tll_ptr call_ret_t158; tll_ptr call_ret_t160;
  tll_ptr s1_v904771; tll_ptr s2_v904773; tll_ptr switch_ret_t152;
  tll_ptr switch_ret_t153; tll_ptr switch_ret_t156; tll_ptr switch_ret_t159;
  switch(((tll_node)s1_v904766)->tag) {
    case 6:
      switch(((tll_node)s2_v904767)->tag) {
        case 6:
          instr_struct(&EQ_t154, 3, 0);
          switch_ret_t153 = EQ_t154;
          break;
        case 7:
          __v904768 = ((tll_node)s2_v904767)->data[0];
          __v904769 = ((tll_node)s2_v904767)->data[1];
          instr_struct(&LT_t155, 1, 0);
          switch_ret_t153 = LT_t155;
          break;
      }
      switch_ret_t152 = switch_ret_t153;
      break;
    case 7:
      c1_v904770 = ((tll_node)s1_v904766)->data[0];
      s1_v904771 = ((tll_node)s1_v904766)->data[1];
      switch(((tll_node)s2_v904767)->tag) {
        case 6:
          instr_struct(&GT_t157, 2, 0);
          switch_ret_t156 = GT_t157;
          break;
        case 7:
          c2_v904772 = ((tll_node)s2_v904767)->data[0];
          s2_v904773 = ((tll_node)s2_v904767)->data[1];
          call_ret_t158 = comparec_i18(c1_v904770, c2_v904772);
          switch(((tll_node)call_ret_t158)->tag) {
            case 3:
              call_ret_t160 = compares_i22(s1_v904771, s2_v904773);
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

tll_ptr lam_fun_t164(tll_ptr s2_v904776, tll_env env) {
  tll_ptr call_ret_t163;
  call_ret_t163 = compares_i22(env[0], s2_v904776);
  return call_ret_t163;
}

tll_ptr lam_fun_t166(tll_ptr s1_v904774, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, s1_v904774);
  return lam_clo_t165;
}

tll_ptr and_thenUUU_i78(tll_ptr A_v904777, tll_ptr B_v904778, tll_ptr opt_v904779, tll_ptr f_v904780) {
  tll_ptr NoneUU_t169; tll_ptr app_ret_t170; tll_ptr switch_ret_t168;
  tll_ptr x_v904781;
  switch(((tll_node)opt_v904779)->tag) {
    case 27:
      instr_struct(&NoneUU_t169, 27, 0);
      switch_ret_t168 = NoneUU_t169;
      break;
    case 28:
      x_v904781 = ((tll_node)opt_v904779)->data[0];
      instr_app(&app_ret_t170, f_v904780, x_v904781);
      switch_ret_t168 = app_ret_t170;
      break;
  }
  return switch_ret_t168;
}

tll_ptr lam_fun_t172(tll_ptr f_v904791, tll_env env) {
  tll_ptr call_ret_t171;
  call_ret_t171 = and_thenUUU_i78(env[2], env[1], env[0], f_v904791);
  return call_ret_t171;
}

tll_ptr lam_fun_t174(tll_ptr opt_v904789, tll_env env) {
  tll_ptr lam_clo_t173;
  instr_clo(&lam_clo_t173, &lam_fun_t172, 3, opt_v904789, env[0], env[1]);
  return lam_clo_t173;
}

tll_ptr lam_fun_t176(tll_ptr B_v904786, tll_env env) {
  tll_ptr lam_clo_t175;
  instr_clo(&lam_clo_t175, &lam_fun_t174, 2, B_v904786, env[0]);
  return lam_clo_t175;
}

tll_ptr lam_fun_t178(tll_ptr A_v904782, tll_env env) {
  tll_ptr lam_clo_t177;
  instr_clo(&lam_clo_t177, &lam_fun_t176, 1, A_v904782);
  return lam_clo_t177;
}

tll_ptr and_thenUUL_i77(tll_ptr A_v904792, tll_ptr B_v904793, tll_ptr opt_v904794, tll_ptr f_v904795) {
  tll_ptr NoneUL_t181; tll_ptr app_ret_t182; tll_ptr switch_ret_t180;
  tll_ptr x_v904796;
  switch(((tll_node)opt_v904794)->tag) {
    case 25:
      instr_free_struct(opt_v904794);
      instr_struct(&NoneUL_t181, 25, 0);
      switch_ret_t180 = NoneUL_t181;
      break;
    case 26:
      x_v904796 = ((tll_node)opt_v904794)->data[0];
      instr_free_struct(opt_v904794);
      instr_app(&app_ret_t182, f_v904795, x_v904796);
      switch_ret_t180 = app_ret_t182;
      break;
  }
  return switch_ret_t180;
}

tll_ptr lam_fun_t184(tll_ptr f_v904806, tll_env env) {
  tll_ptr call_ret_t183;
  call_ret_t183 = and_thenUUL_i77(env[2], env[1], env[0], f_v904806);
  return call_ret_t183;
}

tll_ptr lam_fun_t186(tll_ptr opt_v904804, tll_env env) {
  tll_ptr lam_clo_t185;
  instr_clo(&lam_clo_t185, &lam_fun_t184, 3, opt_v904804, env[0], env[1]);
  return lam_clo_t185;
}

tll_ptr lam_fun_t188(tll_ptr B_v904801, tll_env env) {
  tll_ptr lam_clo_t187;
  instr_clo(&lam_clo_t187, &lam_fun_t186, 2, B_v904801, env[0]);
  return lam_clo_t187;
}

tll_ptr lam_fun_t190(tll_ptr A_v904797, tll_env env) {
  tll_ptr lam_clo_t189;
  instr_clo(&lam_clo_t189, &lam_fun_t188, 1, A_v904797);
  return lam_clo_t189;
}

tll_ptr and_thenULU_i76(tll_ptr A_v904807, tll_ptr B_v904808, tll_ptr opt_v904809, tll_ptr f_v904810) {
  tll_ptr NoneLU_t193; tll_ptr app_ret_t194; tll_ptr switch_ret_t192;
  tll_ptr x_v904811;
  switch(((tll_node)opt_v904809)->tag) {
    case 27:
      instr_struct(&NoneLU_t193, 23, 0);
      switch_ret_t192 = NoneLU_t193;
      break;
    case 28:
      x_v904811 = ((tll_node)opt_v904809)->data[0];
      instr_app(&app_ret_t194, f_v904810, x_v904811);
      switch_ret_t192 = app_ret_t194;
      break;
  }
  return switch_ret_t192;
}

tll_ptr lam_fun_t196(tll_ptr f_v904821, tll_env env) {
  tll_ptr call_ret_t195;
  call_ret_t195 = and_thenULU_i76(env[2], env[1], env[0], f_v904821);
  return call_ret_t195;
}

tll_ptr lam_fun_t198(tll_ptr opt_v904819, tll_env env) {
  tll_ptr lam_clo_t197;
  instr_clo(&lam_clo_t197, &lam_fun_t196, 3, opt_v904819, env[0], env[1]);
  return lam_clo_t197;
}

tll_ptr lam_fun_t200(tll_ptr B_v904816, tll_env env) {
  tll_ptr lam_clo_t199;
  instr_clo(&lam_clo_t199, &lam_fun_t198, 2, B_v904816, env[0]);
  return lam_clo_t199;
}

tll_ptr lam_fun_t202(tll_ptr A_v904812, tll_env env) {
  tll_ptr lam_clo_t201;
  instr_clo(&lam_clo_t201, &lam_fun_t200, 1, A_v904812);
  return lam_clo_t201;
}

tll_ptr and_thenULL_i75(tll_ptr A_v904822, tll_ptr B_v904823, tll_ptr opt_v904824, tll_ptr f_v904825) {
  tll_ptr NoneLL_t205; tll_ptr app_ret_t206; tll_ptr switch_ret_t204;
  tll_ptr x_v904826;
  switch(((tll_node)opt_v904824)->tag) {
    case 25:
      instr_free_struct(opt_v904824);
      instr_struct(&NoneLL_t205, 21, 0);
      switch_ret_t204 = NoneLL_t205;
      break;
    case 26:
      x_v904826 = ((tll_node)opt_v904824)->data[0];
      instr_free_struct(opt_v904824);
      instr_app(&app_ret_t206, f_v904825, x_v904826);
      switch_ret_t204 = app_ret_t206;
      break;
  }
  return switch_ret_t204;
}

tll_ptr lam_fun_t208(tll_ptr f_v904836, tll_env env) {
  tll_ptr call_ret_t207;
  call_ret_t207 = and_thenULL_i75(env[2], env[1], env[0], f_v904836);
  return call_ret_t207;
}

tll_ptr lam_fun_t210(tll_ptr opt_v904834, tll_env env) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 3, opt_v904834, env[0], env[1]);
  return lam_clo_t209;
}

tll_ptr lam_fun_t212(tll_ptr B_v904831, tll_env env) {
  tll_ptr lam_clo_t211;
  instr_clo(&lam_clo_t211, &lam_fun_t210, 2, B_v904831, env[0]);
  return lam_clo_t211;
}

tll_ptr lam_fun_t214(tll_ptr A_v904827, tll_env env) {
  tll_ptr lam_clo_t213;
  instr_clo(&lam_clo_t213, &lam_fun_t212, 1, A_v904827);
  return lam_clo_t213;
}

tll_ptr and_thenLUL_i73(tll_ptr A_v904837, tll_ptr B_v904838, tll_ptr opt_v904839, tll_ptr f_v904840) {
  tll_ptr NoneUL_t217; tll_ptr app_ret_t218; tll_ptr switch_ret_t216;
  tll_ptr x_v904841;
  switch(((tll_node)opt_v904839)->tag) {
    case 21:
      instr_free_struct(opt_v904839);
      instr_struct(&NoneUL_t217, 25, 0);
      switch_ret_t216 = NoneUL_t217;
      break;
    case 22:
      x_v904841 = ((tll_node)opt_v904839)->data[0];
      instr_free_struct(opt_v904839);
      instr_app(&app_ret_t218, f_v904840, x_v904841);
      switch_ret_t216 = app_ret_t218;
      break;
  }
  return switch_ret_t216;
}

tll_ptr lam_fun_t220(tll_ptr f_v904851, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = and_thenLUL_i73(env[2], env[1], env[0], f_v904851);
  return call_ret_t219;
}

tll_ptr lam_fun_t222(tll_ptr opt_v904849, tll_env env) {
  tll_ptr lam_clo_t221;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 3, opt_v904849, env[0], env[1]);
  return lam_clo_t221;
}

tll_ptr lam_fun_t224(tll_ptr B_v904846, tll_env env) {
  tll_ptr lam_clo_t223;
  instr_clo(&lam_clo_t223, &lam_fun_t222, 2, B_v904846, env[0]);
  return lam_clo_t223;
}

tll_ptr lam_fun_t226(tll_ptr A_v904842, tll_env env) {
  tll_ptr lam_clo_t225;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 1, A_v904842);
  return lam_clo_t225;
}

tll_ptr and_thenLLL_i71(tll_ptr A_v904852, tll_ptr B_v904853, tll_ptr opt_v904854, tll_ptr f_v904855) {
  tll_ptr NoneLL_t229; tll_ptr app_ret_t230; tll_ptr switch_ret_t228;
  tll_ptr x_v904856;
  switch(((tll_node)opt_v904854)->tag) {
    case 21:
      instr_free_struct(opt_v904854);
      instr_struct(&NoneLL_t229, 21, 0);
      switch_ret_t228 = NoneLL_t229;
      break;
    case 22:
      x_v904856 = ((tll_node)opt_v904854)->data[0];
      instr_free_struct(opt_v904854);
      instr_app(&app_ret_t230, f_v904855, x_v904856);
      switch_ret_t228 = app_ret_t230;
      break;
  }
  return switch_ret_t228;
}

tll_ptr lam_fun_t232(tll_ptr f_v904866, tll_env env) {
  tll_ptr call_ret_t231;
  call_ret_t231 = and_thenLLL_i71(env[2], env[1], env[0], f_v904866);
  return call_ret_t231;
}

tll_ptr lam_fun_t234(tll_ptr opt_v904864, tll_env env) {
  tll_ptr lam_clo_t233;
  instr_clo(&lam_clo_t233, &lam_fun_t232, 3, opt_v904864, env[0], env[1]);
  return lam_clo_t233;
}

tll_ptr lam_fun_t236(tll_ptr B_v904861, tll_env env) {
  tll_ptr lam_clo_t235;
  instr_clo(&lam_clo_t235, &lam_fun_t234, 2, B_v904861, env[0]);
  return lam_clo_t235;
}

tll_ptr lam_fun_t238(tll_ptr A_v904857, tll_env env) {
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, A_v904857);
  return lam_clo_t237;
}

tll_ptr lenUU_i86(tll_ptr A_v904867, tll_ptr xs_v904868) {
  tll_ptr add_ret_t245; tll_ptr call_ret_t243; tll_ptr consUU_t246;
  tll_ptr n_v904871; tll_ptr nilUU_t241; tll_ptr pair_struct_t242;
  tll_ptr pair_struct_t247; tll_ptr switch_ret_t240; tll_ptr switch_ret_t244;
  tll_ptr x_v904869; tll_ptr xs_v904870; tll_ptr xs_v904872;
  switch(((tll_node)xs_v904868)->tag) {
    case 35:
      instr_struct(&nilUU_t241, 35, 0);
      instr_struct(&pair_struct_t242, 0, 2, (tll_ptr)0, nilUU_t241);
      switch_ret_t240 = pair_struct_t242;
      break;
    case 36:
      x_v904869 = ((tll_node)xs_v904868)->data[0];
      xs_v904870 = ((tll_node)xs_v904868)->data[1];
      call_ret_t243 = lenUU_i86(0, xs_v904870);
      switch(((tll_node)call_ret_t243)->tag) {
        case 0:
          n_v904871 = ((tll_node)call_ret_t243)->data[0];
          xs_v904872 = ((tll_node)call_ret_t243)->data[1];
          instr_free_struct(call_ret_t243);
          add_ret_t245 = n_v904871 + 1;
          instr_struct(&consUU_t246, 36, 2, x_v904869, xs_v904872);
          instr_struct(&pair_struct_t247, 0, 2, add_ret_t245, consUU_t246);
          switch_ret_t244 = pair_struct_t247;
          break;
      }
      switch_ret_t240 = switch_ret_t244;
      break;
  }
  return switch_ret_t240;
}

tll_ptr lam_fun_t249(tll_ptr xs_v904875, tll_env env) {
  tll_ptr call_ret_t248;
  call_ret_t248 = lenUU_i86(env[0], xs_v904875);
  return call_ret_t248;
}

tll_ptr lam_fun_t251(tll_ptr A_v904873, tll_env env) {
  tll_ptr lam_clo_t250;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 1, A_v904873);
  return lam_clo_t250;
}

tll_ptr lenUL_i85(tll_ptr A_v904876, tll_ptr xs_v904877) {
  tll_ptr add_ret_t258; tll_ptr call_ret_t256; tll_ptr consUL_t259;
  tll_ptr n_v904880; tll_ptr nilUL_t254; tll_ptr pair_struct_t255;
  tll_ptr pair_struct_t260; tll_ptr switch_ret_t253; tll_ptr switch_ret_t257;
  tll_ptr x_v904878; tll_ptr xs_v904879; tll_ptr xs_v904881;
  switch(((tll_node)xs_v904877)->tag) {
    case 33:
      instr_free_struct(xs_v904877);
      instr_struct(&nilUL_t254, 33, 0);
      instr_struct(&pair_struct_t255, 0, 2, (tll_ptr)0, nilUL_t254);
      switch_ret_t253 = pair_struct_t255;
      break;
    case 34:
      x_v904878 = ((tll_node)xs_v904877)->data[0];
      xs_v904879 = ((tll_node)xs_v904877)->data[1];
      instr_free_struct(xs_v904877);
      call_ret_t256 = lenUL_i85(0, xs_v904879);
      switch(((tll_node)call_ret_t256)->tag) {
        case 0:
          n_v904880 = ((tll_node)call_ret_t256)->data[0];
          xs_v904881 = ((tll_node)call_ret_t256)->data[1];
          instr_free_struct(call_ret_t256);
          add_ret_t258 = n_v904880 + 1;
          instr_struct(&consUL_t259, 34, 2, x_v904878, xs_v904881);
          instr_struct(&pair_struct_t260, 0, 2, add_ret_t258, consUL_t259);
          switch_ret_t257 = pair_struct_t260;
          break;
      }
      switch_ret_t253 = switch_ret_t257;
      break;
  }
  return switch_ret_t253;
}

tll_ptr lam_fun_t262(tll_ptr xs_v904884, tll_env env) {
  tll_ptr call_ret_t261;
  call_ret_t261 = lenUL_i85(env[0], xs_v904884);
  return call_ret_t261;
}

tll_ptr lam_fun_t264(tll_ptr A_v904882, tll_env env) {
  tll_ptr lam_clo_t263;
  instr_clo(&lam_clo_t263, &lam_fun_t262, 1, A_v904882);
  return lam_clo_t263;
}

tll_ptr lenLL_i83(tll_ptr A_v904885, tll_ptr xs_v904886) {
  tll_ptr add_ret_t271; tll_ptr call_ret_t269; tll_ptr consLL_t272;
  tll_ptr n_v904889; tll_ptr nilLL_t267; tll_ptr pair_struct_t268;
  tll_ptr pair_struct_t273; tll_ptr switch_ret_t266; tll_ptr switch_ret_t270;
  tll_ptr x_v904887; tll_ptr xs_v904888; tll_ptr xs_v904890;
  switch(((tll_node)xs_v904886)->tag) {
    case 29:
      instr_free_struct(xs_v904886);
      instr_struct(&nilLL_t267, 29, 0);
      instr_struct(&pair_struct_t268, 0, 2, (tll_ptr)0, nilLL_t267);
      switch_ret_t266 = pair_struct_t268;
      break;
    case 30:
      x_v904887 = ((tll_node)xs_v904886)->data[0];
      xs_v904888 = ((tll_node)xs_v904886)->data[1];
      instr_free_struct(xs_v904886);
      call_ret_t269 = lenLL_i83(0, xs_v904888);
      switch(((tll_node)call_ret_t269)->tag) {
        case 0:
          n_v904889 = ((tll_node)call_ret_t269)->data[0];
          xs_v904890 = ((tll_node)call_ret_t269)->data[1];
          instr_free_struct(call_ret_t269);
          add_ret_t271 = n_v904889 + 1;
          instr_struct(&consLL_t272, 30, 2, x_v904887, xs_v904890);
          instr_struct(&pair_struct_t273, 0, 2, add_ret_t271, consLL_t272);
          switch_ret_t270 = pair_struct_t273;
          break;
      }
      switch_ret_t266 = switch_ret_t270;
      break;
  }
  return switch_ret_t266;
}

tll_ptr lam_fun_t275(tll_ptr xs_v904893, tll_env env) {
  tll_ptr call_ret_t274;
  call_ret_t274 = lenLL_i83(env[0], xs_v904893);
  return call_ret_t274;
}

tll_ptr lam_fun_t277(tll_ptr A_v904891, tll_env env) {
  tll_ptr lam_clo_t276;
  instr_clo(&lam_clo_t276, &lam_fun_t275, 1, A_v904891);
  return lam_clo_t276;
}

tll_ptr appendUU_i90(tll_ptr A_v904894, tll_ptr xs_v904895, tll_ptr ys_v904896) {
  tll_ptr call_ret_t280; tll_ptr consUU_t281; tll_ptr switch_ret_t279;
  tll_ptr x_v904897; tll_ptr xs_v904898;
  switch(((tll_node)xs_v904895)->tag) {
    case 35:
      switch_ret_t279 = ys_v904896;
      break;
    case 36:
      x_v904897 = ((tll_node)xs_v904895)->data[0];
      xs_v904898 = ((tll_node)xs_v904895)->data[1];
      call_ret_t280 = appendUU_i90(0, xs_v904898, ys_v904896);
      instr_struct(&consUU_t281, 36, 2, x_v904897, call_ret_t280);
      switch_ret_t279 = consUU_t281;
      break;
  }
  return switch_ret_t279;
}

tll_ptr lam_fun_t283(tll_ptr ys_v904904, tll_env env) {
  tll_ptr call_ret_t282;
  call_ret_t282 = appendUU_i90(env[1], env[0], ys_v904904);
  return call_ret_t282;
}

tll_ptr lam_fun_t285(tll_ptr xs_v904902, tll_env env) {
  tll_ptr lam_clo_t284;
  instr_clo(&lam_clo_t284, &lam_fun_t283, 2, xs_v904902, env[0]);
  return lam_clo_t284;
}

tll_ptr lam_fun_t287(tll_ptr A_v904899, tll_env env) {
  tll_ptr lam_clo_t286;
  instr_clo(&lam_clo_t286, &lam_fun_t285, 1, A_v904899);
  return lam_clo_t286;
}

tll_ptr appendUL_i89(tll_ptr A_v904905, tll_ptr xs_v904906, tll_ptr ys_v904907) {
  tll_ptr call_ret_t290; tll_ptr consUL_t291; tll_ptr switch_ret_t289;
  tll_ptr x_v904908; tll_ptr xs_v904909;
  switch(((tll_node)xs_v904906)->tag) {
    case 33:
      instr_free_struct(xs_v904906);
      switch_ret_t289 = ys_v904907;
      break;
    case 34:
      x_v904908 = ((tll_node)xs_v904906)->data[0];
      xs_v904909 = ((tll_node)xs_v904906)->data[1];
      instr_free_struct(xs_v904906);
      call_ret_t290 = appendUL_i89(0, xs_v904909, ys_v904907);
      instr_struct(&consUL_t291, 34, 2, x_v904908, call_ret_t290);
      switch_ret_t289 = consUL_t291;
      break;
  }
  return switch_ret_t289;
}

tll_ptr lam_fun_t293(tll_ptr ys_v904915, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = appendUL_i89(env[1], env[0], ys_v904915);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v904913, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 2, xs_v904913, env[0]);
  return lam_clo_t294;
}

tll_ptr lam_fun_t297(tll_ptr A_v904910, tll_env env) {
  tll_ptr lam_clo_t296;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 1, A_v904910);
  return lam_clo_t296;
}

tll_ptr appendLL_i87(tll_ptr A_v904916, tll_ptr xs_v904917, tll_ptr ys_v904918) {
  tll_ptr call_ret_t300; tll_ptr consLL_t301; tll_ptr switch_ret_t299;
  tll_ptr x_v904919; tll_ptr xs_v904920;
  switch(((tll_node)xs_v904917)->tag) {
    case 29:
      instr_free_struct(xs_v904917);
      switch_ret_t299 = ys_v904918;
      break;
    case 30:
      x_v904919 = ((tll_node)xs_v904917)->data[0];
      xs_v904920 = ((tll_node)xs_v904917)->data[1];
      instr_free_struct(xs_v904917);
      call_ret_t300 = appendLL_i87(0, xs_v904920, ys_v904918);
      instr_struct(&consLL_t301, 30, 2, x_v904919, call_ret_t300);
      switch_ret_t299 = consLL_t301;
      break;
  }
  return switch_ret_t299;
}

tll_ptr lam_fun_t303(tll_ptr ys_v904926, tll_env env) {
  tll_ptr call_ret_t302;
  call_ret_t302 = appendLL_i87(env[1], env[0], ys_v904926);
  return call_ret_t302;
}

tll_ptr lam_fun_t305(tll_ptr xs_v904924, tll_env env) {
  tll_ptr lam_clo_t304;
  instr_clo(&lam_clo_t304, &lam_fun_t303, 2, xs_v904924, env[0]);
  return lam_clo_t304;
}

tll_ptr lam_fun_t307(tll_ptr A_v904921, tll_env env) {
  tll_ptr lam_clo_t306;
  instr_clo(&lam_clo_t306, &lam_fun_t305, 1, A_v904921);
  return lam_clo_t306;
}

tll_ptr lam_fun_t314(tll_ptr __v904928, tll_env env) {
  tll_ptr __v904937; tll_ptr ch_v904935; tll_ptr ch_v904936;
  tll_ptr ch_v904939; tll_ptr ch_v904940; tll_ptr prim_ch_t309;
  tll_ptr recv_msg_t311; tll_ptr s_v904938; tll_ptr send_ch_t310;
  tll_ptr send_ch_t313; tll_ptr switch_ret_t312;
  instr_open(&prim_ch_t309, &proc_stdin);
  ch_v904935 = prim_ch_t309;
  instr_send(&send_ch_t310, ch_v904935, (tll_ptr)1);
  ch_v904936 = send_ch_t310;
  instr_recv(&recv_msg_t311, ch_v904936);
  __v904937 = recv_msg_t311;
  switch(((tll_node)__v904937)->tag) {
    case 0:
      s_v904938 = ((tll_node)__v904937)->data[0];
      ch_v904939 = ((tll_node)__v904937)->data[1];
      instr_free_struct(__v904937);
      instr_send(&send_ch_t313, ch_v904939, (tll_ptr)0);
      ch_v904940 = send_ch_t313;
      switch_ret_t312 = s_v904938;
      break;
  }
  return switch_ret_t312;
}

tll_ptr readline_i33(tll_ptr __v904927) {
  tll_ptr lam_clo_t315;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 0);
  return lam_clo_t315;
}

tll_ptr lam_fun_t317(tll_ptr __v904941, tll_env env) {
  tll_ptr call_ret_t316;
  call_ret_t316 = readline_i33(__v904941);
  return call_ret_t316;
}

tll_ptr lam_fun_t323(tll_ptr __v904943, tll_env env) {
  tll_ptr ch_v904948; tll_ptr ch_v904949; tll_ptr ch_v904950;
  tll_ptr ch_v904951; tll_ptr prim_ch_t319; tll_ptr send_ch_t320;
  tll_ptr send_ch_t321; tll_ptr send_ch_t322;
  instr_open(&prim_ch_t319, &proc_stdout);
  ch_v904948 = prim_ch_t319;
  instr_send(&send_ch_t320, ch_v904948, (tll_ptr)1);
  ch_v904949 = send_ch_t320;
  instr_send(&send_ch_t321, ch_v904949, env[0]);
  ch_v904950 = send_ch_t321;
  instr_send(&send_ch_t322, ch_v904950, (tll_ptr)0);
  ch_v904951 = send_ch_t322;
  return 0;
}

tll_ptr print_i34(tll_ptr s_v904942) {
  tll_ptr lam_clo_t324;
  instr_clo(&lam_clo_t324, &lam_fun_t323, 1, s_v904942);
  return lam_clo_t324;
}

tll_ptr lam_fun_t326(tll_ptr s_v904952, tll_env env) {
  tll_ptr call_ret_t325;
  call_ret_t325 = print_i34(s_v904952);
  return call_ret_t325;
}

tll_ptr lam_fun_t332(tll_ptr __v904954, tll_env env) {
  tll_ptr ch_v904959; tll_ptr ch_v904960; tll_ptr ch_v904961;
  tll_ptr ch_v904962; tll_ptr prim_ch_t328; tll_ptr send_ch_t329;
  tll_ptr send_ch_t330; tll_ptr send_ch_t331;
  instr_open(&prim_ch_t328, &proc_stderr);
  ch_v904959 = prim_ch_t328;
  instr_send(&send_ch_t329, ch_v904959, (tll_ptr)1);
  ch_v904960 = send_ch_t329;
  instr_send(&send_ch_t330, ch_v904960, env[0]);
  ch_v904961 = send_ch_t330;
  instr_send(&send_ch_t331, ch_v904961, (tll_ptr)0);
  ch_v904962 = send_ch_t331;
  return 0;
}

tll_ptr prerr_i35(tll_ptr s_v904953) {
  tll_ptr lam_clo_t333;
  instr_clo(&lam_clo_t333, &lam_fun_t332, 1, s_v904953);
  return lam_clo_t333;
}

tll_ptr lam_fun_t335(tll_ptr s_v904963, tll_env env) {
  tll_ptr call_ret_t334;
  call_ret_t334 = prerr_i35(s_v904963);
  return call_ret_t334;
}

tll_ptr get_at_i37(tll_ptr A_v904964, tll_ptr n_v904965, tll_ptr xs_v904966, tll_ptr a_v904967) {
  tll_ptr __v904968; tll_ptr __v904971; tll_ptr add_ret_t380;
  tll_ptr call_ret_t379; tll_ptr ifte_ret_t382; tll_ptr switch_ret_t378;
  tll_ptr switch_ret_t381; tll_ptr x_v904970; tll_ptr xs_v904969;
  if (n_v904965) {
    switch(((tll_node)xs_v904966)->tag) {
      case 35:
        switch_ret_t378 = a_v904967;
        break;
      case 36:
        __v904968 = ((tll_node)xs_v904966)->data[0];
        xs_v904969 = ((tll_node)xs_v904966)->data[1];
        add_ret_t380 = n_v904965 - 1;
        call_ret_t379 = get_at_i37(0, add_ret_t380, xs_v904969, a_v904967);
        switch_ret_t378 = call_ret_t379;
        break;
    }
    ifte_ret_t382 = switch_ret_t378;
  }
  else {
    switch(((tll_node)xs_v904966)->tag) {
      case 35:
        switch_ret_t381 = a_v904967;
        break;
      case 36:
        x_v904970 = ((tll_node)xs_v904966)->data[0];
        __v904971 = ((tll_node)xs_v904966)->data[1];
        switch_ret_t381 = x_v904970;
        break;
    }
    ifte_ret_t382 = switch_ret_t381;
  }
  return ifte_ret_t382;
}

tll_ptr lam_fun_t384(tll_ptr a_v904981, tll_env env) {
  tll_ptr call_ret_t383;
  call_ret_t383 = get_at_i37(env[2], env[1], env[0], a_v904981);
  return call_ret_t383;
}

tll_ptr lam_fun_t386(tll_ptr xs_v904979, tll_env env) {
  tll_ptr lam_clo_t385;
  instr_clo(&lam_clo_t385, &lam_fun_t384, 3, xs_v904979, env[0], env[1]);
  return lam_clo_t385;
}

tll_ptr lam_fun_t388(tll_ptr n_v904976, tll_env env) {
  tll_ptr lam_clo_t387;
  instr_clo(&lam_clo_t387, &lam_fun_t386, 2, n_v904976, env[0]);
  return lam_clo_t387;
}

tll_ptr lam_fun_t390(tll_ptr A_v904972, tll_env env) {
  tll_ptr lam_clo_t389;
  instr_clo(&lam_clo_t389, &lam_fun_t388, 1, A_v904972);
  return lam_clo_t389;
}

tll_ptr string_of_digit_i38(tll_ptr n_v904982) {
  tll_ptr EmptyString_t393; tll_ptr call_ret_t392;
  instr_struct(&EmptyString_t393, 6, 0);
  call_ret_t392 = get_at_i37(0, n_v904982, digits_i36, EmptyString_t393);
  return call_ret_t392;
}

tll_ptr lam_fun_t395(tll_ptr n_v904983, tll_env env) {
  tll_ptr call_ret_t394;
  call_ret_t394 = string_of_digit_i38(n_v904983);
  return call_ret_t394;
}

tll_ptr string_of_nat_i39(tll_ptr n_v904984) {
  tll_ptr call_ret_t397; tll_ptr call_ret_t398; tll_ptr call_ret_t399;
  tll_ptr call_ret_t400; tll_ptr call_ret_t401; tll_ptr call_ret_t402;
  tll_ptr ifte_ret_t403; tll_ptr n_v904986; tll_ptr s_v904985;
  call_ret_t398 = modn_i16(n_v904984, (tll_ptr)10);
  call_ret_t397 = string_of_digit_i38(call_ret_t398);
  s_v904985 = call_ret_t397;
  call_ret_t399 = divn_i15(n_v904984, (tll_ptr)10);
  n_v904986 = call_ret_t399;
  call_ret_t400 = ltn_i6((tll_ptr)0, n_v904986);
  if (call_ret_t400) {
    call_ret_t402 = string_of_nat_i39(n_v904986);
    call_ret_t401 = cats_i19(call_ret_t402, s_v904985);
    ifte_ret_t403 = call_ret_t401;
  }
  else {
    ifte_ret_t403 = s_v904985;
  }
  return ifte_ret_t403;
}

tll_ptr lam_fun_t405(tll_ptr n_v904987, tll_env env) {
  tll_ptr call_ret_t404;
  call_ret_t404 = string_of_nat_i39(n_v904987);
  return call_ret_t404;
}

tll_ptr digit_of_char_i40(tll_ptr c_v904988) {
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
  call_ret_t407 = eqc_i17(c_v904988, Char_t408);
  if (call_ret_t407) {
    instr_struct(&SomeUL_t409, 26, 1, (tll_ptr)0);
    ifte_ret_t447 = SomeUL_t409;
  }
  else {
    instr_struct(&Char_t411, 5, 1, (tll_ptr)49);
    call_ret_t410 = eqc_i17(c_v904988, Char_t411);
    if (call_ret_t410) {
      instr_struct(&SomeUL_t412, 26, 1, (tll_ptr)1);
      ifte_ret_t446 = SomeUL_t412;
    }
    else {
      instr_struct(&Char_t414, 5, 1, (tll_ptr)50);
      call_ret_t413 = eqc_i17(c_v904988, Char_t414);
      if (call_ret_t413) {
        instr_struct(&SomeUL_t415, 26, 1, (tll_ptr)2);
        ifte_ret_t445 = SomeUL_t415;
      }
      else {
        instr_struct(&Char_t417, 5, 1, (tll_ptr)51);
        call_ret_t416 = eqc_i17(c_v904988, Char_t417);
        if (call_ret_t416) {
          instr_struct(&SomeUL_t418, 26, 1, (tll_ptr)3);
          ifte_ret_t444 = SomeUL_t418;
        }
        else {
          instr_struct(&Char_t420, 5, 1, (tll_ptr)52);
          call_ret_t419 = eqc_i17(c_v904988, Char_t420);
          if (call_ret_t419) {
            instr_struct(&SomeUL_t421, 26, 1, (tll_ptr)4);
            ifte_ret_t443 = SomeUL_t421;
          }
          else {
            instr_struct(&Char_t423, 5, 1, (tll_ptr)53);
            call_ret_t422 = eqc_i17(c_v904988, Char_t423);
            if (call_ret_t422) {
              instr_struct(&SomeUL_t424, 26, 1, (tll_ptr)5);
              ifte_ret_t442 = SomeUL_t424;
            }
            else {
              instr_struct(&Char_t426, 5, 1, (tll_ptr)54);
              call_ret_t425 = eqc_i17(c_v904988, Char_t426);
              if (call_ret_t425) {
                instr_struct(&SomeUL_t427, 26, 1, (tll_ptr)6);
                ifte_ret_t441 = SomeUL_t427;
              }
              else {
                instr_struct(&Char_t429, 5, 1, (tll_ptr)55);
                call_ret_t428 = eqc_i17(c_v904988, Char_t429);
                if (call_ret_t428) {
                  instr_struct(&SomeUL_t430, 26, 1, (tll_ptr)7);
                  ifte_ret_t440 = SomeUL_t430;
                }
                else {
                  instr_struct(&Char_t432, 5, 1, (tll_ptr)56);
                  call_ret_t431 = eqc_i17(c_v904988, Char_t432);
                  if (call_ret_t431) {
                    instr_struct(&SomeUL_t433, 26, 1, (tll_ptr)8);
                    ifte_ret_t439 = SomeUL_t433;
                  }
                  else {
                    instr_struct(&Char_t435, 5, 1, (tll_ptr)57);
                    call_ret_t434 = eqc_i17(c_v904988, Char_t435);
                    if (call_ret_t434) {
                      instr_struct(&SomeUL_t436, 26, 1, (tll_ptr)9);
                      ifte_ret_t438 = SomeUL_t436;
                    }
                    else {
                      instr_struct(&NoneUL_t437, 25, 0);
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

tll_ptr lam_fun_t449(tll_ptr c_v904989, tll_env env) {
  tll_ptr call_ret_t448;
  call_ret_t448 = digit_of_char_i40(c_v904989);
  return call_ret_t448;
}

tll_ptr nat_of_string_loop_i41(tll_ptr s_v904990, tll_ptr acc_v904991) {
  tll_ptr NoneUL_t455; tll_ptr SomeUL_t452; tll_ptr c_v904992;
  tll_ptr call_ret_t453; tll_ptr call_ret_t456; tll_ptr call_ret_t457;
  tll_ptr call_ret_t458; tll_ptr n_v904994; tll_ptr s_v904993;
  tll_ptr switch_ret_t451; tll_ptr switch_ret_t454;
  switch(((tll_node)s_v904990)->tag) {
    case 6:
      instr_struct(&SomeUL_t452, 26, 1, acc_v904991);
      switch_ret_t451 = SomeUL_t452;
      break;
    case 7:
      c_v904992 = ((tll_node)s_v904990)->data[0];
      s_v904993 = ((tll_node)s_v904990)->data[1];
      call_ret_t453 = digit_of_char_i40(c_v904992);
      switch(((tll_node)call_ret_t453)->tag) {
        case 25:
          instr_free_struct(call_ret_t453);
          instr_struct(&NoneUL_t455, 25, 0);
          switch_ret_t454 = NoneUL_t455;
          break;
        case 26:
          n_v904994 = ((tll_node)call_ret_t453)->data[0];
          instr_free_struct(call_ret_t453);
          call_ret_t458 = muln_i14(acc_v904991, (tll_ptr)10);
          call_ret_t457 = addn_i12(call_ret_t458, n_v904994);
          call_ret_t456 = nat_of_string_loop_i41(s_v904993, call_ret_t457);
          switch_ret_t454 = call_ret_t456;
          break;
      }
      switch_ret_t451 = switch_ret_t454;
      break;
  }
  return switch_ret_t451;
}

tll_ptr lam_fun_t460(tll_ptr acc_v904997, tll_env env) {
  tll_ptr call_ret_t459;
  call_ret_t459 = nat_of_string_loop_i41(env[0], acc_v904997);
  return call_ret_t459;
}

tll_ptr lam_fun_t462(tll_ptr s_v904995, tll_env env) {
  tll_ptr lam_clo_t461;
  instr_clo(&lam_clo_t461, &lam_fun_t460, 1, s_v904995);
  return lam_clo_t461;
}

tll_ptr nat_of_string_i42(tll_ptr s_v904998) {
  tll_ptr call_ret_t464;
  call_ret_t464 = nat_of_string_loop_i41(s_v904998, (tll_ptr)0);
  return call_ret_t464;
}

tll_ptr lam_fun_t466(tll_ptr s_v904999, tll_env env) {
  tll_ptr call_ret_t465;
  call_ret_t465 = nat_of_string_i42(s_v904999);
  return call_ret_t465;
}

tll_ptr contains_i51(tll_ptr c_v905000, tll_ptr s_v905001) {
  tll_ptr c0_v905002; tll_ptr call_ret_t469; tll_ptr call_ret_t470;
  tll_ptr ifte_ret_t471; tll_ptr s_v905003; tll_ptr switch_ret_t468;
  switch(((tll_node)s_v905001)->tag) {
    case 6:
      switch_ret_t468 = (tll_ptr)0;
      break;
    case 7:
      c0_v905002 = ((tll_node)s_v905001)->data[0];
      s_v905003 = ((tll_node)s_v905001)->data[1];
      call_ret_t469 = eqc_i17(c_v905000, c0_v905002);
      if (call_ret_t469) {
        ifte_ret_t471 = (tll_ptr)1;
      }
      else {
        call_ret_t470 = contains_i51(c_v905000, s_v905003);
        ifte_ret_t471 = call_ret_t470;
      }
      switch_ret_t468 = ifte_ret_t471;
      break;
  }
  return switch_ret_t468;
}

tll_ptr lam_fun_t473(tll_ptr s_v905006, tll_env env) {
  tll_ptr call_ret_t472;
  call_ret_t472 = contains_i51(env[0], s_v905006);
  return call_ret_t472;
}

tll_ptr lam_fun_t475(tll_ptr c_v905004, tll_env env) {
  tll_ptr lam_clo_t474;
  instr_clo(&lam_clo_t474, &lam_fun_t473, 1, c_v905004);
  return lam_clo_t474;
}

tll_ptr lam_fun_t481(tll_ptr e_v905010, tll_env env) {
  tll_ptr EmptyString_t479; tll_ptr SPairUUU_t480;
  instr_struct(&EmptyString_t479, 6, 0);
  instr_struct(&SPairUUU_t480, 44, 2, EmptyString_t479, 0);
  return SPairUUU_t480;
}

tll_ptr lam_fun_t483(tll_ptr e_v905013, tll_env env) {
  
  
  return 0;
}

tll_ptr lam_fun_t486(tll_ptr e_v905016, tll_env env) {
  
  
  return 0;
}

tll_ptr lam_fun_t499(tll_ptr e1_v905028, tll_env env) {
  tll_ptr Char_t495; tll_ptr EmptyString_t496; tll_ptr SPairUUU_t498;
  tll_ptr String_t497; tll_ptr call_ret_t494;
  instr_struct(&Char_t495, 5, 1, (tll_ptr)89);
  instr_struct(&EmptyString_t496, 6, 0);
  instr_struct(&String_t497, 7, 2, Char_t495, EmptyString_t496);
  call_ret_t494 = cats_i19(String_t497, env[0]);
  instr_struct(&SPairUUU_t498, 44, 2, call_ret_t494, 0);
  return SPairUUU_t498;
}

tll_ptr lam_fun_t507(tll_ptr e2_v905032, tll_env env) {
  tll_ptr Char_t503; tll_ptr EmptyString_t504; tll_ptr SPairUUU_t506;
  tll_ptr String_t505; tll_ptr call_ret_t502;
  instr_struct(&Char_t503, 5, 1, (tll_ptr)73);
  instr_struct(&EmptyString_t504, 6, 0);
  instr_struct(&String_t505, 7, 2, Char_t503, EmptyString_t504);
  call_ret_t502 = cats_i19(String_t505, env[0]);
  instr_struct(&SPairUUU_t506, 44, 2, call_ret_t502, 0);
  return SPairUUU_t506;
}

tll_ptr lam_fun_t514(tll_ptr e2_v905033, tll_env env) {
  tll_ptr Char_t510; tll_ptr EmptyString_t511; tll_ptr SPairUUU_t513;
  tll_ptr String_t512; tll_ptr call_ret_t509;
  instr_struct(&Char_t510, 5, 1, (tll_ptr)78);
  instr_struct(&EmptyString_t511, 6, 0);
  instr_struct(&String_t512, 7, 2, Char_t510, EmptyString_t511);
  call_ret_t509 = cats_i19(String_t512, env[0]);
  instr_struct(&SPairUUU_t513, 44, 2, call_ret_t509, 0);
  return SPairUUU_t513;
}

tll_ptr lam_fun_t518(tll_ptr e1_v905029, tll_env env) {
  tll_ptr app_ret_t517; tll_ptr call_ret_t501; tll_ptr ifte_ret_t516;
  tll_ptr lam_clo_t508; tll_ptr lam_clo_t515;
  call_ret_t501 = contains_i51(env[1], env[2]);
  if (call_ret_t501) {
    instr_clo(&lam_clo_t508, &lam_fun_t507, 1, env[0]);
    ifte_ret_t516 = lam_clo_t508;
  }
  else {
    instr_clo(&lam_clo_t515, &lam_fun_t514, 1, env[0]);
    ifte_ret_t516 = lam_clo_t515;
  }
  instr_app(&app_ret_t517, ifte_ret_t516, 0);
  return app_ret_t517;
}

tll_ptr lam_fun_t522(tll_ptr e_v905019, tll_env env) {
  tll_ptr app_ret_t488; tll_ptr app_ret_t489; tll_ptr app_ret_t490;
  tll_ptr app_ret_t491; tll_ptr app_ret_t521; tll_ptr call_ret_t493;
  tll_ptr df_v905026; tll_ptr ifte_ret_t520; tll_ptr lam_clo_t500;
  tll_ptr lam_clo_t519; tll_ptr pf_v905027; tll_ptr switch_ret_t492;
  instr_app(&app_ret_t488, string_diffclo_i143, env[4]);
  instr_app(&app_ret_t489, app_ret_t488, env[2]);
  instr_app(&app_ret_t490, app_ret_t489, env[0]);
  instr_app(&app_ret_t491, app_ret_t490, 0);
  switch(((tll_node)app_ret_t491)->tag) {
    case 44:
      df_v905026 = ((tll_node)app_ret_t491)->data[0];
      pf_v905027 = ((tll_node)app_ret_t491)->data[1];
      call_ret_t493 = eqc_i17(env[3], env[1]);
      if (call_ret_t493) {
        instr_clo(&lam_clo_t500, &lam_fun_t499, 1, df_v905026);
        ifte_ret_t520 = lam_clo_t500;
      }
      else {
        instr_clo(&lam_clo_t519, &lam_fun_t518, 3, df_v905026, env[1], env[4]);
        ifte_ret_t520 = lam_clo_t519;
      }
      instr_app(&app_ret_t521, ifte_ret_t520, 0);
      switch_ret_t492 = app_ret_t521;
      break;
  }
  return switch_ret_t492;
}

tll_ptr string_diff_i52(tll_ptr ans_v905007, tll_ptr s1_v905008, tll_ptr s2_v905009) {
  tll_ptr c1_v905014; tll_ptr c2_v905011; tll_ptr c2_v905017;
  tll_ptr lam_clo_t482; tll_ptr lam_clo_t484; tll_ptr lam_clo_t487;
  tll_ptr lam_clo_t523; tll_ptr s1_v905015; tll_ptr s2_v905012;
  tll_ptr s2_v905018; tll_ptr switch_ret_t477; tll_ptr switch_ret_t478;
  tll_ptr switch_ret_t485;
  switch(((tll_node)s1_v905008)->tag) {
    case 6:
      switch(((tll_node)s2_v905009)->tag) {
        case 6:
          instr_clo(&lam_clo_t482, &lam_fun_t481, 0);
          switch_ret_t478 = lam_clo_t482;
          break;
        case 7:
          c2_v905011 = ((tll_node)s2_v905009)->data[0];
          s2_v905012 = ((tll_node)s2_v905009)->data[1];
          instr_clo(&lam_clo_t484, &lam_fun_t483, 0);
          switch_ret_t478 = lam_clo_t484;
          break;
      }
      switch_ret_t477 = switch_ret_t478;
      break;
    case 7:
      c1_v905014 = ((tll_node)s1_v905008)->data[0];
      s1_v905015 = ((tll_node)s1_v905008)->data[1];
      switch(((tll_node)s2_v905009)->tag) {
        case 6:
          instr_clo(&lam_clo_t487, &lam_fun_t486, 0);
          switch_ret_t485 = lam_clo_t487;
          break;
        case 7:
          c2_v905017 = ((tll_node)s2_v905009)->data[0];
          s2_v905018 = ((tll_node)s2_v905009)->data[1];
          instr_clo(&lam_clo_t523, &lam_fun_t522, 5,
                    s2_v905018, c2_v905017, s1_v905015, c1_v905014,
                    ans_v905007);
          switch_ret_t485 = lam_clo_t523;
          break;
      }
      switch_ret_t477 = switch_ret_t485;
      break;
  }
  return switch_ret_t477;
}

tll_ptr lam_fun_t525(tll_ptr s2_v905039, tll_env env) {
  tll_ptr call_ret_t524;
  call_ret_t524 = string_diff_i52(env[1], env[0], s2_v905039);
  return call_ret_t524;
}

tll_ptr lam_fun_t527(tll_ptr s1_v905037, tll_env env) {
  tll_ptr lam_clo_t526;
  instr_clo(&lam_clo_t526, &lam_fun_t525, 2, s1_v905037, env[0]);
  return lam_clo_t526;
}

tll_ptr lam_fun_t529(tll_ptr ans_v905034, tll_env env) {
  tll_ptr lam_clo_t528;
  instr_clo(&lam_clo_t528, &lam_fun_t527, 1, ans_v905034);
  return lam_clo_t528;
}

tll_ptr word_diff_i54(tll_ptr ans_v905040, tll_ptr guess_v905041) {
  tll_ptr SPairUUU_t539; tll_ptr Word_t538; tll_ptr app_ret_t533;
  tll_ptr app_ret_t534; tll_ptr app_ret_t535; tll_ptr app_ret_t536;
  tll_ptr h_v905047; tll_ptr pf1_v905043; tll_ptr pf2_v905045;
  tll_ptr s1_v905042; tll_ptr s2_v905044; tll_ptr s3_v905046;
  tll_ptr switch_ret_t531; tll_ptr switch_ret_t532; tll_ptr switch_ret_t537;
  switch(((tll_node)ans_v905040)->tag) {
    case 17:
      s1_v905042 = ((tll_node)ans_v905040)->data[0];
      pf1_v905043 = ((tll_node)ans_v905040)->data[1];
      switch(((tll_node)guess_v905041)->tag) {
        case 17:
          s2_v905044 = ((tll_node)guess_v905041)->data[0];
          pf2_v905045 = ((tll_node)guess_v905041)->data[1];
          instr_app(&app_ret_t533, string_diffclo_i143, s1_v905042);
          instr_app(&app_ret_t534, app_ret_t533, s1_v905042);
          instr_app(&app_ret_t535, app_ret_t534, s2_v905044);
          instr_app(&app_ret_t536, app_ret_t535, 0);
          switch(((tll_node)app_ret_t536)->tag) {
            case 44:
              s3_v905046 = ((tll_node)app_ret_t536)->data[0];
              h_v905047 = ((tll_node)app_ret_t536)->data[1];
              instr_struct(&Word_t538, 17, 2, s3_v905046, 0);
              instr_struct(&SPairUUU_t539, 44, 2, Word_t538, 0);
              switch_ret_t537 = SPairUUU_t539;
              break;
          }
          switch_ret_t532 = switch_ret_t537;
          break;
      }
      switch_ret_t531 = switch_ret_t532;
      break;
  }
  return switch_ret_t531;
}

tll_ptr lam_fun_t541(tll_ptr guess_v905050, tll_env env) {
  tll_ptr call_ret_t540;
  call_ret_t540 = word_diff_i54(env[0], guess_v905050);
  return call_ret_t540;
}

tll_ptr lam_fun_t543(tll_ptr ans_v905048, tll_env env) {
  tll_ptr lam_clo_t542;
  instr_clo(&lam_clo_t542, &lam_fun_t541, 1, ans_v905048);
  return lam_clo_t542;
}

tll_ptr eqw_i55(tll_ptr w1_v905051, tll_ptr w2_v905052) {
  tll_ptr __v905054; tll_ptr __v905056; tll_ptr call_ret_t547;
  tll_ptr s1_v905053; tll_ptr s2_v905055; tll_ptr switch_ret_t545;
  tll_ptr switch_ret_t546;
  switch(((tll_node)w1_v905051)->tag) {
    case 17:
      s1_v905053 = ((tll_node)w1_v905051)->data[0];
      __v905054 = ((tll_node)w1_v905051)->data[1];
      switch(((tll_node)w2_v905052)->tag) {
        case 17:
          s2_v905055 = ((tll_node)w2_v905052)->data[0];
          __v905056 = ((tll_node)w2_v905052)->data[1];
          call_ret_t547 = eqs_i21(s1_v905053, s2_v905055);
          switch_ret_t546 = call_ret_t547;
          break;
      }
      switch_ret_t545 = switch_ret_t546;
      break;
  }
  return switch_ret_t545;
}

tll_ptr lam_fun_t549(tll_ptr w2_v905059, tll_env env) {
  tll_ptr call_ret_t548;
  call_ret_t548 = eqw_i55(env[0], w2_v905059);
  return call_ret_t548;
}

tll_ptr lam_fun_t551(tll_ptr w1_v905057, tll_env env) {
  tll_ptr lam_clo_t550;
  instr_clo(&lam_clo_t550, &lam_fun_t549, 1, w1_v905057);
  return lam_clo_t550;
}

tll_ptr lam_fun_t558(tll_ptr __v905071, tll_env env) {
  tll_ptr Word_t557;
  instr_struct(&Word_t557, 17, 2, env[0], 0);
  return Word_t557;
}

tll_ptr lam_fun_t560(tll_ptr e_v905069, tll_env env) {
  tll_ptr lam_clo_t559;
  instr_clo(&lam_clo_t559, &lam_fun_t558, 1, env[0]);
  return lam_clo_t559;
}

tll_ptr lam_fun_t641(tll_ptr __v905075, tll_env env) {
  tll_ptr Char_t563; tll_ptr Char_t564; tll_ptr Char_t565; tll_ptr Char_t566;
  tll_ptr Char_t567; tll_ptr Char_t568; tll_ptr Char_t569; tll_ptr Char_t570;
  tll_ptr Char_t571; tll_ptr Char_t572; tll_ptr Char_t573; tll_ptr Char_t574;
  tll_ptr Char_t575; tll_ptr Char_t576; tll_ptr Char_t577; tll_ptr Char_t578;
  tll_ptr Char_t579; tll_ptr Char_t580; tll_ptr Char_t581; tll_ptr Char_t582;
  tll_ptr Char_t583; tll_ptr Char_t584; tll_ptr Char_t585; tll_ptr Char_t586;
  tll_ptr Char_t587; tll_ptr Char_t588; tll_ptr Char_t589; tll_ptr Char_t590;
  tll_ptr Char_t591; tll_ptr Char_t592; tll_ptr Char_t593; tll_ptr Char_t594;
  tll_ptr Char_t595; tll_ptr Char_t596; tll_ptr Char_t597; tll_ptr Char_t598;
  tll_ptr Char_t599; tll_ptr EmptyString_t600; tll_ptr String_t601;
  tll_ptr String_t602; tll_ptr String_t603; tll_ptr String_t604;
  tll_ptr String_t605; tll_ptr String_t606; tll_ptr String_t607;
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
  tll_ptr __v905077; tll_ptr app_ret_t638; tll_ptr app_ret_t640;
  tll_ptr call_ret_t562; tll_ptr call_ret_t639;
  instr_struct(&Char_t563, 5, 1, (tll_ptr)112);
  instr_struct(&Char_t564, 5, 1, (tll_ptr)108);
  instr_struct(&Char_t565, 5, 1, (tll_ptr)101);
  instr_struct(&Char_t566, 5, 1, (tll_ptr)97);
  instr_struct(&Char_t567, 5, 1, (tll_ptr)115);
  instr_struct(&Char_t568, 5, 1, (tll_ptr)101);
  instr_struct(&Char_t569, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t570, 5, 1, (tll_ptr)105);
  instr_struct(&Char_t571, 5, 1, (tll_ptr)110);
  instr_struct(&Char_t572, 5, 1, (tll_ptr)112);
  instr_struct(&Char_t573, 5, 1, (tll_ptr)117);
  instr_struct(&Char_t574, 5, 1, (tll_ptr)116);
  instr_struct(&Char_t575, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t576, 5, 1, (tll_ptr)97);
  instr_struct(&Char_t577, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t578, 5, 1, (tll_ptr)119);
  instr_struct(&Char_t579, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t580, 5, 1, (tll_ptr)114);
  instr_struct(&Char_t581, 5, 1, (tll_ptr)100);
  instr_struct(&Char_t582, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t583, 5, 1, (tll_ptr)119);
  instr_struct(&Char_t584, 5, 1, (tll_ptr)105);
  instr_struct(&Char_t585, 5, 1, (tll_ptr)116);
  instr_struct(&Char_t586, 5, 1, (tll_ptr)104);
  instr_struct(&Char_t587, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t588, 5, 1, (tll_ptr)108);
  instr_struct(&Char_t589, 5, 1, (tll_ptr)101);
  instr_struct(&Char_t590, 5, 1, (tll_ptr)110);
  instr_struct(&Char_t591, 5, 1, (tll_ptr)103);
  instr_struct(&Char_t592, 5, 1, (tll_ptr)116);
  instr_struct(&Char_t593, 5, 1, (tll_ptr)104);
  instr_struct(&Char_t594, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t595, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t596, 5, 1, (tll_ptr)102);
  instr_struct(&Char_t597, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t598, 5, 1, (tll_ptr)53);
  instr_struct(&Char_t599, 5, 1, (tll_ptr)10);
  instr_struct(&EmptyString_t600, 6, 0);
  instr_struct(&String_t601, 7, 2, Char_t599, EmptyString_t600);
  instr_struct(&String_t602, 7, 2, Char_t598, String_t601);
  instr_struct(&String_t603, 7, 2, Char_t597, String_t602);
  instr_struct(&String_t604, 7, 2, Char_t596, String_t603);
  instr_struct(&String_t605, 7, 2, Char_t595, String_t604);
  instr_struct(&String_t606, 7, 2, Char_t594, String_t605);
  instr_struct(&String_t607, 7, 2, Char_t593, String_t606);
  instr_struct(&String_t608, 7, 2, Char_t592, String_t607);
  instr_struct(&String_t609, 7, 2, Char_t591, String_t608);
  instr_struct(&String_t610, 7, 2, Char_t590, String_t609);
  instr_struct(&String_t611, 7, 2, Char_t589, String_t610);
  instr_struct(&String_t612, 7, 2, Char_t588, String_t611);
  instr_struct(&String_t613, 7, 2, Char_t587, String_t612);
  instr_struct(&String_t614, 7, 2, Char_t586, String_t613);
  instr_struct(&String_t615, 7, 2, Char_t585, String_t614);
  instr_struct(&String_t616, 7, 2, Char_t584, String_t615);
  instr_struct(&String_t617, 7, 2, Char_t583, String_t616);
  instr_struct(&String_t618, 7, 2, Char_t582, String_t617);
  instr_struct(&String_t619, 7, 2, Char_t581, String_t618);
  instr_struct(&String_t620, 7, 2, Char_t580, String_t619);
  instr_struct(&String_t621, 7, 2, Char_t579, String_t620);
  instr_struct(&String_t622, 7, 2, Char_t578, String_t621);
  instr_struct(&String_t623, 7, 2, Char_t577, String_t622);
  instr_struct(&String_t624, 7, 2, Char_t576, String_t623);
  instr_struct(&String_t625, 7, 2, Char_t575, String_t624);
  instr_struct(&String_t626, 7, 2, Char_t574, String_t625);
  instr_struct(&String_t627, 7, 2, Char_t573, String_t626);
  instr_struct(&String_t628, 7, 2, Char_t572, String_t627);
  instr_struct(&String_t629, 7, 2, Char_t571, String_t628);
  instr_struct(&String_t630, 7, 2, Char_t570, String_t629);
  instr_struct(&String_t631, 7, 2, Char_t569, String_t630);
  instr_struct(&String_t632, 7, 2, Char_t568, String_t631);
  instr_struct(&String_t633, 7, 2, Char_t567, String_t632);
  instr_struct(&String_t634, 7, 2, Char_t566, String_t633);
  instr_struct(&String_t635, 7, 2, Char_t565, String_t634);
  instr_struct(&String_t636, 7, 2, Char_t564, String_t635);
  instr_struct(&String_t637, 7, 2, Char_t563, String_t636);
  call_ret_t562 = print_i34(String_t637);
  instr_app(&app_ret_t638, call_ret_t562, 0);
  instr_free_clo(call_ret_t562);
  __v905077 = app_ret_t638;
  call_ret_t639 = read_word_i62(0);
  instr_app(&app_ret_t640, call_ret_t639, 0);
  instr_free_clo(call_ret_t639);
  return app_ret_t640;
}

tll_ptr lam_fun_t643(tll_ptr __v905072, tll_env env) {
  tll_ptr lam_clo_t642;
  instr_clo(&lam_clo_t642, &lam_fun_t641, 0);
  return lam_clo_t642;
}

tll_ptr lam_fun_t648(tll_ptr __v905061, tll_env env) {
  tll_ptr app_ret_t554; tll_ptr app_ret_t646; tll_ptr app_ret_t647;
  tll_ptr call_ret_t553; tll_ptr call_ret_t555; tll_ptr call_ret_t556;
  tll_ptr ifte_ret_t645; tll_ptr lam_clo_t561; tll_ptr lam_clo_t644;
  tll_ptr s_v905068;
  call_ret_t553 = readline_i33(0);
  instr_app(&app_ret_t554, call_ret_t553, 0);
  instr_free_clo(call_ret_t553);
  s_v905068 = app_ret_t554;
  call_ret_t556 = strlen_i20(s_v905068);
  call_ret_t555 = eqn_i9(call_ret_t556, (tll_ptr)5);
  if (call_ret_t555) {
    instr_clo(&lam_clo_t561, &lam_fun_t560, 1, s_v905068);
    ifte_ret_t645 = lam_clo_t561;
  }
  else {
    instr_clo(&lam_clo_t644, &lam_fun_t643, 0);
    ifte_ret_t645 = lam_clo_t644;
  }
  instr_app(&app_ret_t646, ifte_ret_t645, 0);
  instr_app(&app_ret_t647, app_ret_t646, 0);
  instr_free_clo(app_ret_t646);
  return app_ret_t647;
}

tll_ptr read_word_i62(tll_ptr __v905060) {
  tll_ptr lam_clo_t649;
  instr_clo(&lam_clo_t649, &lam_fun_t648, 0);
  return lam_clo_t649;
}

tll_ptr lam_fun_t651(tll_ptr __v905078, tll_env env) {
  tll_ptr call_ret_t650;
  call_ret_t650 = read_word_i62(__v905078);
  return call_ret_t650;
}

tll_ptr lam_fun_t682(tll_ptr __v905135, tll_env env) {
  tll_ptr Char_t661; tll_ptr Char_t662; tll_ptr Char_t663; tll_ptr Char_t664;
  tll_ptr Char_t665; tll_ptr Char_t666; tll_ptr Char_t667; tll_ptr Char_t668;
  tll_ptr Char_t669; tll_ptr EmptyString_t670; tll_ptr String_t671;
  tll_ptr String_t672; tll_ptr String_t673; tll_ptr String_t674;
  tll_ptr String_t675; tll_ptr String_t676; tll_ptr String_t677;
  tll_ptr String_t678; tll_ptr String_t679; tll_ptr __v905137;
  tll_ptr app_ret_t680; tll_ptr call_ret_t660; tll_ptr close_tmp_t681;
  instr_struct(&Char_t661, 5, 1, (tll_ptr)89);
  instr_struct(&Char_t662, 5, 1, (tll_ptr)111);
  instr_struct(&Char_t663, 5, 1, (tll_ptr)117);
  instr_struct(&Char_t664, 5, 1, (tll_ptr)32);
  instr_struct(&Char_t665, 5, 1, (tll_ptr)87);
  instr_struct(&Char_t666, 5, 1, (tll_ptr)105);
  instr_struct(&Char_t667, 5, 1, (tll_ptr)110);
  instr_struct(&Char_t668, 5, 1, (tll_ptr)33);
  instr_struct(&Char_t669, 5, 1, (tll_ptr)10);
  instr_struct(&EmptyString_t670, 6, 0);
  instr_struct(&String_t671, 7, 2, Char_t669, EmptyString_t670);
  instr_struct(&String_t672, 7, 2, Char_t668, String_t671);
  instr_struct(&String_t673, 7, 2, Char_t667, String_t672);
  instr_struct(&String_t674, 7, 2, Char_t666, String_t673);
  instr_struct(&String_t675, 7, 2, Char_t665, String_t674);
  instr_struct(&String_t676, 7, 2, Char_t664, String_t675);
  instr_struct(&String_t677, 7, 2, Char_t663, String_t676);
  instr_struct(&String_t678, 7, 2, Char_t662, String_t677);
  instr_struct(&String_t679, 7, 2, Char_t661, String_t678);
  call_ret_t660 = print_i34(String_t679);
  instr_app(&app_ret_t680, call_ret_t660, 0);
  instr_free_clo(call_ret_t660);
  __v905137 = app_ret_t680;
  instr_close(&close_tmp_t681, env[0]);
  return close_tmp_t681;
}

tll_ptr lam_fun_t684(tll_ptr c_v905132, tll_env env) {
  tll_ptr lam_clo_t683;
  instr_clo(&lam_clo_t683, &lam_fun_t682, 1, c_v905132);
  return lam_clo_t683;
}

tll_ptr lam_fun_t787(tll_ptr __v905148, tll_env env) {
  tll_ptr Char_t696; tll_ptr Char_t697; tll_ptr Char_t698; tll_ptr Char_t699;
  tll_ptr Char_t700; tll_ptr Char_t701; tll_ptr Char_t702; tll_ptr Char_t703;
  tll_ptr Char_t704; tll_ptr Char_t705; tll_ptr Char_t706; tll_ptr Char_t707;
  tll_ptr Char_t708; tll_ptr Char_t709; tll_ptr Char_t710; tll_ptr Char_t711;
  tll_ptr Char_t712; tll_ptr Char_t731; tll_ptr Char_t732; tll_ptr Char_t733;
  tll_ptr Char_t734; tll_ptr Char_t735; tll_ptr Char_t736; tll_ptr Char_t737;
  tll_ptr Char_t738; tll_ptr Char_t739; tll_ptr Char_t740; tll_ptr Char_t741;
  tll_ptr Char_t756; tll_ptr Char_t757; tll_ptr Char_t758; tll_ptr Char_t759;
  tll_ptr Char_t760; tll_ptr Char_t761; tll_ptr Char_t762; tll_ptr Char_t763;
  tll_ptr Char_t764; tll_ptr Char_t765; tll_ptr Char_t766; tll_ptr Char_t767;
  tll_ptr Char_t768; tll_ptr EmptyString_t713; tll_ptr EmptyString_t742;
  tll_ptr EmptyString_t769; tll_ptr String_t714; tll_ptr String_t715;
  tll_ptr String_t716; tll_ptr String_t717; tll_ptr String_t718;
  tll_ptr String_t719; tll_ptr String_t720; tll_ptr String_t721;
  tll_ptr String_t722; tll_ptr String_t723; tll_ptr String_t724;
  tll_ptr String_t725; tll_ptr String_t726; tll_ptr String_t727;
  tll_ptr String_t728; tll_ptr String_t729; tll_ptr String_t730;
  tll_ptr String_t743; tll_ptr String_t744; tll_ptr String_t745;
  tll_ptr String_t746; tll_ptr String_t747; tll_ptr String_t748;
  tll_ptr String_t749; tll_ptr String_t750; tll_ptr String_t751;
  tll_ptr String_t752; tll_ptr String_t753; tll_ptr String_t770;
  tll_ptr String_t771; tll_ptr String_t772; tll_ptr String_t773;
  tll_ptr String_t774; tll_ptr String_t775; tll_ptr String_t776;
  tll_ptr String_t777; tll_ptr String_t778; tll_ptr String_t779;
  tll_ptr String_t780; tll_ptr String_t781; tll_ptr String_t782;
  tll_ptr __v905157; tll_ptr __v905163; tll_ptr __v905164;
  tll_ptr add_ret_t755; tll_ptr add_ret_t785; tll_ptr app_ret_t783;
  tll_ptr app_ret_t786; tll_ptr c_v905159; tll_ptr c_v905161;
  tll_ptr call_ret_t691; tll_ptr call_ret_t692; tll_ptr call_ret_t693;
  tll_ptr call_ret_t694; tll_ptr call_ret_t695; tll_ptr call_ret_t754;
  tll_ptr call_ret_t784; tll_ptr diff_v905158; tll_ptr pair_struct_t688;
  tll_ptr pf_v905160; tll_ptr recv_msg_t686; tll_ptr s_v905162;
  tll_ptr switch_ret_t687; tll_ptr switch_ret_t689; tll_ptr switch_ret_t690;
  instr_recv(&recv_msg_t686, env[0]);
  __v905157 = recv_msg_t686;
  switch(((tll_node)__v905157)->tag) {
    case 0:
      diff_v905158 = ((tll_node)__v905157)->data[0];
      c_v905159 = ((tll_node)__v905157)->data[1];
      instr_free_struct(__v905157);
      instr_struct(&pair_struct_t688, 0, 2, 0, c_v905159);
      switch(((tll_node)pair_struct_t688)->tag) {
        case 0:
          pf_v905160 = ((tll_node)pair_struct_t688)->data[0];
          c_v905161 = ((tll_node)pair_struct_t688)->data[1];
          instr_free_struct(pair_struct_t688);
          switch(((tll_node)diff_v905158)->tag) {
            case 17:
              s_v905162 = ((tll_node)diff_v905158)->data[0];
              __v905163 = ((tll_node)diff_v905158)->data[1];
              instr_struct(&Char_t696, 5, 1, (tll_ptr)73);
              instr_struct(&Char_t697, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t698, 5, 1, (tll_ptr)99);
              instr_struct(&Char_t699, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t700, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t701, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t702, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t703, 5, 1, (tll_ptr)99);
              instr_struct(&Char_t704, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t705, 5, 1, (tll_ptr)44);
              instr_struct(&Char_t706, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t707, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t708, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t709, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t710, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t711, 5, 1, (tll_ptr)58);
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
              instr_struct(&String_t725, 7, 2, Char_t701, String_t724);
              instr_struct(&String_t726, 7, 2, Char_t700, String_t725);
              instr_struct(&String_t727, 7, 2, Char_t699, String_t726);
              instr_struct(&String_t728, 7, 2, Char_t698, String_t727);
              instr_struct(&String_t729, 7, 2, Char_t697, String_t728);
              instr_struct(&String_t730, 7, 2, Char_t696, String_t729);
              call_ret_t695 = cats_i19(String_t730, s_v905162);
              instr_struct(&Char_t731, 5, 1, (tll_ptr)46);
              instr_struct(&Char_t732, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t733, 5, 1, (tll_ptr)89);
              instr_struct(&Char_t734, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t735, 5, 1, (tll_ptr)117);
              instr_struct(&Char_t736, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t737, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t738, 5, 1, (tll_ptr)97);
              instr_struct(&Char_t739, 5, 1, (tll_ptr)118);
              instr_struct(&Char_t740, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t741, 5, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t742, 6, 0);
              instr_struct(&String_t743, 7, 2, Char_t741, EmptyString_t742);
              instr_struct(&String_t744, 7, 2, Char_t740, String_t743);
              instr_struct(&String_t745, 7, 2, Char_t739, String_t744);
              instr_struct(&String_t746, 7, 2, Char_t738, String_t745);
              instr_struct(&String_t747, 7, 2, Char_t737, String_t746);
              instr_struct(&String_t748, 7, 2, Char_t736, String_t747);
              instr_struct(&String_t749, 7, 2, Char_t735, String_t748);
              instr_struct(&String_t750, 7, 2, Char_t734, String_t749);
              instr_struct(&String_t751, 7, 2, Char_t733, String_t750);
              instr_struct(&String_t752, 7, 2, Char_t732, String_t751);
              instr_struct(&String_t753, 7, 2, Char_t731, String_t752);
              call_ret_t694 = cats_i19(call_ret_t695, String_t753);
              add_ret_t755 = env[1] - 1;
              call_ret_t754 = string_of_nat_i39(add_ret_t755);
              call_ret_t693 = cats_i19(call_ret_t694, call_ret_t754);
              instr_struct(&Char_t756, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t757, 5, 1, (tll_ptr)109);
              instr_struct(&Char_t758, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t759, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t760, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t761, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t762, 5, 1, (tll_ptr)116);
              instr_struct(&Char_t763, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t764, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t765, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t766, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t767, 5, 1, (tll_ptr)46);
              instr_struct(&Char_t768, 5, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t769, 6, 0);
              instr_struct(&String_t770, 7, 2, Char_t768, EmptyString_t769);
              instr_struct(&String_t771, 7, 2, Char_t767, String_t770);
              instr_struct(&String_t772, 7, 2, Char_t766, String_t771);
              instr_struct(&String_t773, 7, 2, Char_t765, String_t772);
              instr_struct(&String_t774, 7, 2, Char_t764, String_t773);
              instr_struct(&String_t775, 7, 2, Char_t763, String_t774);
              instr_struct(&String_t776, 7, 2, Char_t762, String_t775);
              instr_struct(&String_t777, 7, 2, Char_t761, String_t776);
              instr_struct(&String_t778, 7, 2, Char_t760, String_t777);
              instr_struct(&String_t779, 7, 2, Char_t759, String_t778);
              instr_struct(&String_t780, 7, 2, Char_t758, String_t779);
              instr_struct(&String_t781, 7, 2, Char_t757, String_t780);
              instr_struct(&String_t782, 7, 2, Char_t756, String_t781);
              call_ret_t692 = cats_i19(call_ret_t693, String_t782);
              call_ret_t691 = print_i34(call_ret_t692);
              instr_app(&app_ret_t783, call_ret_t691, 0);
              instr_free_clo(call_ret_t691);
              __v905164 = app_ret_t783;
              add_ret_t785 = env[1] - 1;
              call_ret_t784 = player_loop_i63(0, add_ret_t785, c_v905161);
              instr_app(&app_ret_t786, call_ret_t784, 0);
              instr_free_clo(call_ret_t784);
              switch_ret_t690 = app_ret_t786;
              break;
          }
          switch_ret_t689 = switch_ret_t690;
          break;
      }
      switch_ret_t687 = switch_ret_t689;
      break;
  }
  return switch_ret_t687;
}

tll_ptr lam_fun_t789(tll_ptr c_v905138, tll_env env) {
  tll_ptr lam_clo_t788;
  instr_clo(&lam_clo_t788, &lam_fun_t787, 2, c_v905138, env[0]);
  return lam_clo_t788;
}

tll_ptr lam_fun_t794(tll_ptr __v905104, tll_env env) {
  tll_ptr __v905127; tll_ptr app_ret_t654; tll_ptr app_ret_t792;
  tll_ptr app_ret_t793; tll_ptr b_v905128; tll_ptr c_v905126;
  tll_ptr c_v905129; tll_ptr c_v905131; tll_ptr call_ret_t653;
  tll_ptr guess_v905125; tll_ptr ifte_ret_t791; tll_ptr lam_clo_t685;
  tll_ptr lam_clo_t790; tll_ptr pair_struct_t658; tll_ptr pf_v905130;
  tll_ptr recv_msg_t656; tll_ptr send_ch_t655; tll_ptr switch_ret_t657;
  tll_ptr switch_ret_t659;
  call_ret_t653 = read_word_i62(0);
  instr_app(&app_ret_t654, call_ret_t653, 0);
  instr_free_clo(call_ret_t653);
  guess_v905125 = app_ret_t654;
  instr_send(&send_ch_t655, env[0], guess_v905125);
  c_v905126 = send_ch_t655;
  instr_recv(&recv_msg_t656, c_v905126);
  __v905127 = recv_msg_t656;
  switch(((tll_node)__v905127)->tag) {
    case 0:
      b_v905128 = ((tll_node)__v905127)->data[0];
      c_v905129 = ((tll_node)__v905127)->data[1];
      instr_free_struct(__v905127);
      instr_struct(&pair_struct_t658, 0, 2, 0, c_v905129);
      switch(((tll_node)pair_struct_t658)->tag) {
        case 0:
          pf_v905130 = ((tll_node)pair_struct_t658)->data[0];
          c_v905131 = ((tll_node)pair_struct_t658)->data[1];
          instr_free_struct(pair_struct_t658);
          if (b_v905128) {
            instr_clo(&lam_clo_t685, &lam_fun_t684, 0);
            ifte_ret_t791 = lam_clo_t685;
          }
          else {
            instr_clo(&lam_clo_t790, &lam_fun_t789, 1, env[1]);
            ifte_ret_t791 = lam_clo_t790;
          }
          instr_app(&app_ret_t792, ifte_ret_t791, c_v905131);
          instr_free_clo(ifte_ret_t791);
          instr_app(&app_ret_t793, app_ret_t792, 0);
          instr_free_clo(app_ret_t792);
          switch_ret_t659 = app_ret_t793;
          break;
      }
      switch_ret_t657 = switch_ret_t659;
      break;
  }
  return switch_ret_t657;
}

tll_ptr lam_fun_t796(tll_ptr c_v905082, tll_env env) {
  tll_ptr lam_clo_t795;
  instr_clo(&lam_clo_t795, &lam_fun_t794, 2, c_v905082, env[0]);
  return lam_clo_t795;
}

tll_ptr lam_fun_t862(tll_ptr __v905175, tll_env env) {
  tll_ptr Char_t806; tll_ptr Char_t807; tll_ptr Char_t808; tll_ptr Char_t809;
  tll_ptr Char_t810; tll_ptr Char_t811; tll_ptr Char_t812; tll_ptr Char_t813;
  tll_ptr Char_t814; tll_ptr Char_t815; tll_ptr Char_t816; tll_ptr Char_t817;
  tll_ptr Char_t818; tll_ptr Char_t819; tll_ptr Char_t820; tll_ptr Char_t821;
  tll_ptr Char_t822; tll_ptr Char_t823; tll_ptr Char_t824; tll_ptr Char_t825;
  tll_ptr Char_t826; tll_ptr Char_t827; tll_ptr Char_t828; tll_ptr Char_t829;
  tll_ptr Char_t855; tll_ptr Char_t856; tll_ptr EmptyString_t830;
  tll_ptr EmptyString_t857; tll_ptr String_t831; tll_ptr String_t832;
  tll_ptr String_t833; tll_ptr String_t834; tll_ptr String_t835;
  tll_ptr String_t836; tll_ptr String_t837; tll_ptr String_t838;
  tll_ptr String_t839; tll_ptr String_t840; tll_ptr String_t841;
  tll_ptr String_t842; tll_ptr String_t843; tll_ptr String_t844;
  tll_ptr String_t845; tll_ptr String_t846; tll_ptr String_t847;
  tll_ptr String_t848; tll_ptr String_t849; tll_ptr String_t850;
  tll_ptr String_t851; tll_ptr String_t852; tll_ptr String_t853;
  tll_ptr String_t854; tll_ptr String_t858; tll_ptr String_t859;
  tll_ptr __v905184; tll_ptr __v905190; tll_ptr __v905191;
  tll_ptr ans_v905185; tll_ptr app_ret_t860; tll_ptr c_v905186;
  tll_ptr c_v905188; tll_ptr call_ret_t803; tll_ptr call_ret_t804;
  tll_ptr call_ret_t805; tll_ptr close_tmp_t861; tll_ptr pair_struct_t800;
  tll_ptr pf_v905187; tll_ptr recv_msg_t798; tll_ptr s_v905189;
  tll_ptr switch_ret_t799; tll_ptr switch_ret_t801; tll_ptr switch_ret_t802;
  instr_recv(&recv_msg_t798, env[0]);
  __v905184 = recv_msg_t798;
  switch(((tll_node)__v905184)->tag) {
    case 0:
      ans_v905185 = ((tll_node)__v905184)->data[0];
      c_v905186 = ((tll_node)__v905184)->data[1];
      instr_free_struct(__v905184);
      instr_struct(&pair_struct_t800, 0, 2, 0, c_v905186);
      switch(((tll_node)pair_struct_t800)->tag) {
        case 0:
          pf_v905187 = ((tll_node)pair_struct_t800)->data[0];
          c_v905188 = ((tll_node)pair_struct_t800)->data[1];
          instr_free_struct(pair_struct_t800);
          switch(((tll_node)ans_v905185)->tag) {
            case 17:
              s_v905189 = ((tll_node)ans_v905185)->data[0];
              __v905190 = ((tll_node)ans_v905185)->data[1];
              instr_struct(&Char_t806, 5, 1, (tll_ptr)89);
              instr_struct(&Char_t807, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t808, 5, 1, (tll_ptr)117);
              instr_struct(&Char_t809, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t810, 5, 1, (tll_ptr)76);
              instr_struct(&Char_t811, 5, 1, (tll_ptr)111);
              instr_struct(&Char_t812, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t813, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t814, 5, 1, (tll_ptr)33);
              instr_struct(&Char_t815, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t816, 5, 1, (tll_ptr)84);
              instr_struct(&Char_t817, 5, 1, (tll_ptr)104);
              instr_struct(&Char_t818, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t819, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t820, 5, 1, (tll_ptr)97);
              instr_struct(&Char_t821, 5, 1, (tll_ptr)110);
              instr_struct(&Char_t822, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t823, 5, 1, (tll_ptr)119);
              instr_struct(&Char_t824, 5, 1, (tll_ptr)101);
              instr_struct(&Char_t825, 5, 1, (tll_ptr)114);
              instr_struct(&Char_t826, 5, 1, (tll_ptr)32);
              instr_struct(&Char_t827, 5, 1, (tll_ptr)105);
              instr_struct(&Char_t828, 5, 1, (tll_ptr)115);
              instr_struct(&Char_t829, 5, 1, (tll_ptr)32);
              instr_struct(&EmptyString_t830, 6, 0);
              instr_struct(&String_t831, 7, 2, Char_t829, EmptyString_t830);
              instr_struct(&String_t832, 7, 2, Char_t828, String_t831);
              instr_struct(&String_t833, 7, 2, Char_t827, String_t832);
              instr_struct(&String_t834, 7, 2, Char_t826, String_t833);
              instr_struct(&String_t835, 7, 2, Char_t825, String_t834);
              instr_struct(&String_t836, 7, 2, Char_t824, String_t835);
              instr_struct(&String_t837, 7, 2, Char_t823, String_t836);
              instr_struct(&String_t838, 7, 2, Char_t822, String_t837);
              instr_struct(&String_t839, 7, 2, Char_t821, String_t838);
              instr_struct(&String_t840, 7, 2, Char_t820, String_t839);
              instr_struct(&String_t841, 7, 2, Char_t819, String_t840);
              instr_struct(&String_t842, 7, 2, Char_t818, String_t841);
              instr_struct(&String_t843, 7, 2, Char_t817, String_t842);
              instr_struct(&String_t844, 7, 2, Char_t816, String_t843);
              instr_struct(&String_t845, 7, 2, Char_t815, String_t844);
              instr_struct(&String_t846, 7, 2, Char_t814, String_t845);
              instr_struct(&String_t847, 7, 2, Char_t813, String_t846);
              instr_struct(&String_t848, 7, 2, Char_t812, String_t847);
              instr_struct(&String_t849, 7, 2, Char_t811, String_t848);
              instr_struct(&String_t850, 7, 2, Char_t810, String_t849);
              instr_struct(&String_t851, 7, 2, Char_t809, String_t850);
              instr_struct(&String_t852, 7, 2, Char_t808, String_t851);
              instr_struct(&String_t853, 7, 2, Char_t807, String_t852);
              instr_struct(&String_t854, 7, 2, Char_t806, String_t853);
              call_ret_t805 = cats_i19(String_t854, s_v905189);
              instr_struct(&Char_t855, 5, 1, (tll_ptr)46);
              instr_struct(&Char_t856, 5, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t857, 6, 0);
              instr_struct(&String_t858, 7, 2, Char_t856, EmptyString_t857);
              instr_struct(&String_t859, 7, 2, Char_t855, String_t858);
              call_ret_t804 = cats_i19(call_ret_t805, String_t859);
              call_ret_t803 = print_i34(call_ret_t804);
              instr_app(&app_ret_t860, call_ret_t803, 0);
              instr_free_clo(call_ret_t803);
              __v905191 = app_ret_t860;
              instr_close(&close_tmp_t861, c_v905188);
              switch_ret_t802 = close_tmp_t861;
              break;
          }
          switch_ret_t801 = switch_ret_t802;
          break;
      }
      switch_ret_t799 = switch_ret_t801;
      break;
  }
  return switch_ret_t799;
}

tll_ptr lam_fun_t864(tll_ptr c_v905165, tll_env env) {
  tll_ptr lam_clo_t863;
  instr_clo(&lam_clo_t863, &lam_fun_t862, 1, c_v905165);
  return lam_clo_t863;
}

tll_ptr player_loop_i63(tll_ptr ans_v905079, tll_ptr repeat_v905080, tll_ptr c_v905081) {
  tll_ptr app_ret_t867; tll_ptr ifte_ret_t866; tll_ptr lam_clo_t797;
  tll_ptr lam_clo_t865;
  if (repeat_v905080) {
    instr_clo(&lam_clo_t797, &lam_fun_t796, 1, repeat_v905080);
    ifte_ret_t866 = lam_clo_t797;
  }
  else {
    instr_clo(&lam_clo_t865, &lam_fun_t864, 0);
    ifte_ret_t866 = lam_clo_t865;
  }
  instr_app(&app_ret_t867, ifte_ret_t866, c_v905081);
  return app_ret_t867;
}

tll_ptr lam_fun_t869(tll_ptr c_v905197, tll_env env) {
  tll_ptr call_ret_t868;
  call_ret_t868 = player_loop_i63(env[1], env[0], c_v905197);
  return call_ret_t868;
}

tll_ptr lam_fun_t871(tll_ptr repeat_v905195, tll_env env) {
  tll_ptr lam_clo_t870;
  instr_clo(&lam_clo_t870, &lam_fun_t869, 2, repeat_v905195, env[0]);
  return lam_clo_t870;
}

tll_ptr lam_fun_t873(tll_ptr ans_v905192, tll_env env) {
  tll_ptr lam_clo_t872;
  instr_clo(&lam_clo_t872, &lam_fun_t871, 1, ans_v905192);
  return lam_clo_t872;
}

tll_ptr lam_fun_t1018(tll_ptr __v905199, tll_env env) {
  tll_ptr Char_t1000; tll_ptr Char_t1001; tll_ptr Char_t1002;
  tll_ptr Char_t1003; tll_ptr Char_t1004; tll_ptr Char_t1005;
  tll_ptr Char_t880; tll_ptr Char_t881; tll_ptr Char_t882; tll_ptr Char_t883;
  tll_ptr Char_t884; tll_ptr Char_t885; tll_ptr Char_t886; tll_ptr Char_t887;
  tll_ptr Char_t888; tll_ptr Char_t889; tll_ptr Char_t890; tll_ptr Char_t891;
  tll_ptr Char_t907; tll_ptr Char_t908; tll_ptr Char_t909; tll_ptr Char_t910;
  tll_ptr Char_t911; tll_ptr Char_t912; tll_ptr Char_t913; tll_ptr Char_t914;
  tll_ptr Char_t915; tll_ptr Char_t916; tll_ptr Char_t917; tll_ptr Char_t918;
  tll_ptr Char_t919; tll_ptr Char_t920; tll_ptr Char_t921; tll_ptr Char_t922;
  tll_ptr Char_t923; tll_ptr Char_t924; tll_ptr Char_t925; tll_ptr Char_t926;
  tll_ptr Char_t927; tll_ptr Char_t928; tll_ptr Char_t929; tll_ptr Char_t930;
  tll_ptr Char_t931; tll_ptr Char_t932; tll_ptr Char_t933; tll_ptr Char_t934;
  tll_ptr Char_t935; tll_ptr Char_t936; tll_ptr Char_t937; tll_ptr Char_t938;
  tll_ptr Char_t939; tll_ptr Char_t978; tll_ptr Char_t979; tll_ptr Char_t980;
  tll_ptr Char_t981; tll_ptr Char_t982; tll_ptr Char_t983; tll_ptr Char_t984;
  tll_ptr Char_t985; tll_ptr Char_t986; tll_ptr Char_t998; tll_ptr Char_t999;
  tll_ptr EmptyString_t1006; tll_ptr EmptyString_t892;
  tll_ptr EmptyString_t940; tll_ptr EmptyString_t987; tll_ptr String_t1007;
  tll_ptr String_t1008; tll_ptr String_t1009; tll_ptr String_t1010;
  tll_ptr String_t1011; tll_ptr String_t1012; tll_ptr String_t1013;
  tll_ptr String_t1014; tll_ptr String_t893; tll_ptr String_t894;
  tll_ptr String_t895; tll_ptr String_t896; tll_ptr String_t897;
  tll_ptr String_t898; tll_ptr String_t899; tll_ptr String_t900;
  tll_ptr String_t901; tll_ptr String_t902; tll_ptr String_t903;
  tll_ptr String_t904; tll_ptr String_t941; tll_ptr String_t942;
  tll_ptr String_t943; tll_ptr String_t944; tll_ptr String_t945;
  tll_ptr String_t946; tll_ptr String_t947; tll_ptr String_t948;
  tll_ptr String_t949; tll_ptr String_t950; tll_ptr String_t951;
  tll_ptr String_t952; tll_ptr String_t953; tll_ptr String_t954;
  tll_ptr String_t955; tll_ptr String_t956; tll_ptr String_t957;
  tll_ptr String_t958; tll_ptr String_t959; tll_ptr String_t960;
  tll_ptr String_t961; tll_ptr String_t962; tll_ptr String_t963;
  tll_ptr String_t964; tll_ptr String_t965; tll_ptr String_t966;
  tll_ptr String_t967; tll_ptr String_t968; tll_ptr String_t969;
  tll_ptr String_t970; tll_ptr String_t971; tll_ptr String_t972;
  tll_ptr String_t973; tll_ptr String_t988; tll_ptr String_t989;
  tll_ptr String_t990; tll_ptr String_t991; tll_ptr String_t992;
  tll_ptr String_t993; tll_ptr String_t994; tll_ptr String_t995;
  tll_ptr String_t996; tll_ptr __v905210; tll_ptr __v905213;
  tll_ptr __v905214; tll_ptr __v905215; tll_ptr ans_v905208;
  tll_ptr app_ret_t1015; tll_ptr app_ret_t1017; tll_ptr app_ret_t905;
  tll_ptr app_ret_t974; tll_ptr c_v905209; tll_ptr c_v905212;
  tll_ptr call_ret_t1016; tll_ptr call_ret_t879; tll_ptr call_ret_t906;
  tll_ptr call_ret_t975; tll_ptr call_ret_t976; tll_ptr call_ret_t977;
  tll_ptr call_ret_t997; tll_ptr pair_struct_t875; tll_ptr recv_msg_t877;
  tll_ptr repeat_v905211; tll_ptr switch_ret_t876; tll_ptr switch_ret_t878;
  instr_struct(&pair_struct_t875, 0, 2, 0, env[0]);
  switch(((tll_node)pair_struct_t875)->tag) {
    case 0:
      ans_v905208 = ((tll_node)pair_struct_t875)->data[0];
      c_v905209 = ((tll_node)pair_struct_t875)->data[1];
      instr_free_struct(pair_struct_t875);
      instr_recv(&recv_msg_t877, c_v905209);
      __v905210 = recv_msg_t877;
      switch(((tll_node)__v905210)->tag) {
        case 0:
          repeat_v905211 = ((tll_node)__v905210)->data[0];
          c_v905212 = ((tll_node)__v905210)->data[1];
          instr_free_struct(__v905210);
          instr_struct(&Char_t880, 5, 1, (tll_ptr)87);
          instr_struct(&Char_t881, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t882, 5, 1, (tll_ptr)114);
          instr_struct(&Char_t883, 5, 1, (tll_ptr)100);
          instr_struct(&Char_t884, 5, 1, (tll_ptr)108);
          instr_struct(&Char_t885, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t886, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t887, 5, 1, (tll_ptr)71);
          instr_struct(&Char_t888, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t889, 5, 1, (tll_ptr)109);
          instr_struct(&Char_t890, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t891, 5, 1, (tll_ptr)10);
          instr_struct(&EmptyString_t892, 6, 0);
          instr_struct(&String_t893, 7, 2, Char_t891, EmptyString_t892);
          instr_struct(&String_t894, 7, 2, Char_t890, String_t893);
          instr_struct(&String_t895, 7, 2, Char_t889, String_t894);
          instr_struct(&String_t896, 7, 2, Char_t888, String_t895);
          instr_struct(&String_t897, 7, 2, Char_t887, String_t896);
          instr_struct(&String_t898, 7, 2, Char_t886, String_t897);
          instr_struct(&String_t899, 7, 2, Char_t885, String_t898);
          instr_struct(&String_t900, 7, 2, Char_t884, String_t899);
          instr_struct(&String_t901, 7, 2, Char_t883, String_t900);
          instr_struct(&String_t902, 7, 2, Char_t882, String_t901);
          instr_struct(&String_t903, 7, 2, Char_t881, String_t902);
          instr_struct(&String_t904, 7, 2, Char_t880, String_t903);
          call_ret_t879 = print_i34(String_t904);
          instr_app(&app_ret_t905, call_ret_t879, 0);
          instr_free_clo(call_ret_t879);
          __v905213 = app_ret_t905;
          instr_struct(&Char_t907, 5, 1, (tll_ptr)80);
          instr_struct(&Char_t908, 5, 1, (tll_ptr)108);
          instr_struct(&Char_t909, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t910, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t911, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t912, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t913, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t914, 5, 1, (tll_ptr)103);
          instr_struct(&Char_t915, 5, 1, (tll_ptr)117);
          instr_struct(&Char_t916, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t917, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t918, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t919, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t920, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t921, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t922, 5, 1, (tll_ptr)119);
          instr_struct(&Char_t923, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t924, 5, 1, (tll_ptr)114);
          instr_struct(&Char_t925, 5, 1, (tll_ptr)100);
          instr_struct(&Char_t926, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t927, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t928, 5, 1, (tll_ptr)102);
          instr_struct(&Char_t929, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t930, 5, 1, (tll_ptr)108);
          instr_struct(&Char_t931, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t932, 5, 1, (tll_ptr)110);
          instr_struct(&Char_t933, 5, 1, (tll_ptr)103);
          instr_struct(&Char_t934, 5, 1, (tll_ptr)116);
          instr_struct(&Char_t935, 5, 1, (tll_ptr)104);
          instr_struct(&Char_t936, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t937, 5, 1, (tll_ptr)53);
          instr_struct(&Char_t938, 5, 1, (tll_ptr)46);
          instr_struct(&Char_t939, 5, 1, (tll_ptr)10);
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
          instr_struct(&String_t950, 7, 2, Char_t930, String_t949);
          instr_struct(&String_t951, 7, 2, Char_t929, String_t950);
          instr_struct(&String_t952, 7, 2, Char_t928, String_t951);
          instr_struct(&String_t953, 7, 2, Char_t927, String_t952);
          instr_struct(&String_t954, 7, 2, Char_t926, String_t953);
          instr_struct(&String_t955, 7, 2, Char_t925, String_t954);
          instr_struct(&String_t956, 7, 2, Char_t924, String_t955);
          instr_struct(&String_t957, 7, 2, Char_t923, String_t956);
          instr_struct(&String_t958, 7, 2, Char_t922, String_t957);
          instr_struct(&String_t959, 7, 2, Char_t921, String_t958);
          instr_struct(&String_t960, 7, 2, Char_t920, String_t959);
          instr_struct(&String_t961, 7, 2, Char_t919, String_t960);
          instr_struct(&String_t962, 7, 2, Char_t918, String_t961);
          instr_struct(&String_t963, 7, 2, Char_t917, String_t962);
          instr_struct(&String_t964, 7, 2, Char_t916, String_t963);
          instr_struct(&String_t965, 7, 2, Char_t915, String_t964);
          instr_struct(&String_t966, 7, 2, Char_t914, String_t965);
          instr_struct(&String_t967, 7, 2, Char_t913, String_t966);
          instr_struct(&String_t968, 7, 2, Char_t912, String_t967);
          instr_struct(&String_t969, 7, 2, Char_t911, String_t968);
          instr_struct(&String_t970, 7, 2, Char_t910, String_t969);
          instr_struct(&String_t971, 7, 2, Char_t909, String_t970);
          instr_struct(&String_t972, 7, 2, Char_t908, String_t971);
          instr_struct(&String_t973, 7, 2, Char_t907, String_t972);
          call_ret_t906 = print_i34(String_t973);
          instr_app(&app_ret_t974, call_ret_t906, 0);
          instr_free_clo(call_ret_t906);
          __v905214 = app_ret_t974;
          instr_struct(&Char_t978, 5, 1, (tll_ptr)89);
          instr_struct(&Char_t979, 5, 1, (tll_ptr)111);
          instr_struct(&Char_t980, 5, 1, (tll_ptr)117);
          instr_struct(&Char_t981, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t982, 5, 1, (tll_ptr)104);
          instr_struct(&Char_t983, 5, 1, (tll_ptr)97);
          instr_struct(&Char_t984, 5, 1, (tll_ptr)118);
          instr_struct(&Char_t985, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t986, 5, 1, (tll_ptr)32);
          instr_struct(&EmptyString_t987, 6, 0);
          instr_struct(&String_t988, 7, 2, Char_t986, EmptyString_t987);
          instr_struct(&String_t989, 7, 2, Char_t985, String_t988);
          instr_struct(&String_t990, 7, 2, Char_t984, String_t989);
          instr_struct(&String_t991, 7, 2, Char_t983, String_t990);
          instr_struct(&String_t992, 7, 2, Char_t982, String_t991);
          instr_struct(&String_t993, 7, 2, Char_t981, String_t992);
          instr_struct(&String_t994, 7, 2, Char_t980, String_t993);
          instr_struct(&String_t995, 7, 2, Char_t979, String_t994);
          instr_struct(&String_t996, 7, 2, Char_t978, String_t995);
          call_ret_t997 = string_of_nat_i39(repeat_v905211);
          call_ret_t977 = cats_i19(String_t996, call_ret_t997);
          instr_struct(&Char_t998, 5, 1, (tll_ptr)32);
          instr_struct(&Char_t999, 5, 1, (tll_ptr)116);
          instr_struct(&Char_t1000, 5, 1, (tll_ptr)114);
          instr_struct(&Char_t1001, 5, 1, (tll_ptr)105);
          instr_struct(&Char_t1002, 5, 1, (tll_ptr)101);
          instr_struct(&Char_t1003, 5, 1, (tll_ptr)115);
          instr_struct(&Char_t1004, 5, 1, (tll_ptr)46);
          instr_struct(&Char_t1005, 5, 1, (tll_ptr)10);
          instr_struct(&EmptyString_t1006, 6, 0);
          instr_struct(&String_t1007, 7, 2, Char_t1005, EmptyString_t1006);
          instr_struct(&String_t1008, 7, 2, Char_t1004, String_t1007);
          instr_struct(&String_t1009, 7, 2, Char_t1003, String_t1008);
          instr_struct(&String_t1010, 7, 2, Char_t1002, String_t1009);
          instr_struct(&String_t1011, 7, 2, Char_t1001, String_t1010);
          instr_struct(&String_t1012, 7, 2, Char_t1000, String_t1011);
          instr_struct(&String_t1013, 7, 2, Char_t999, String_t1012);
          instr_struct(&String_t1014, 7, 2, Char_t998, String_t1013);
          call_ret_t976 = cats_i19(call_ret_t977, String_t1014);
          call_ret_t975 = print_i34(call_ret_t976);
          instr_app(&app_ret_t1015, call_ret_t975, 0);
          instr_free_clo(call_ret_t975);
          __v905215 = app_ret_t1015;
          call_ret_t1016 = player_loop_i63(0, repeat_v905211, c_v905212);
          instr_app(&app_ret_t1017, call_ret_t1016, 0);
          instr_free_clo(call_ret_t1016);
          switch_ret_t878 = app_ret_t1017;
          break;
      }
      switch_ret_t876 = switch_ret_t878;
      break;
  }
  return switch_ret_t876;
}

tll_ptr player_i64(tll_ptr c_v905198) {
  tll_ptr lam_clo_t1019;
  instr_clo(&lam_clo_t1019, &lam_fun_t1018, 1, c_v905198);
  return lam_clo_t1019;
}

tll_ptr lam_fun_t1021(tll_ptr c_v905216, tll_env env) {
  tll_ptr call_ret_t1020;
  call_ret_t1020 = player_i64(c_v905216);
  return call_ret_t1020;
}

tll_ptr lam_fun_t1024(tll_ptr e_v905220, tll_env env) {
  
  
  return 0;
}

tll_ptr lam_fun_t1033(tll_ptr e_v905223, tll_env env) {
  tll_ptr SPairUUU_t1032; tll_ptr add_ret_t1027; tll_ptr app_ret_t1026;
  tll_ptr app_ret_t1028; tll_ptr app_ret_t1029; tll_ptr app_ret_t1030;
  tll_ptr pf_v905227; tll_ptr switch_ret_t1031; tll_ptr x0_v905226;
  instr_app(&app_ret_t1026, get_atclo_i149, 0);
  add_ret_t1027 = env[1] - 1;
  instr_app(&app_ret_t1028, app_ret_t1026, add_ret_t1027);
  instr_app(&app_ret_t1029, app_ret_t1028, env[0]);
  instr_app(&app_ret_t1030, app_ret_t1029, 0);
  switch(((tll_node)app_ret_t1030)->tag) {
    case 44:
      x0_v905226 = ((tll_node)app_ret_t1030)->data[0];
      pf_v905227 = ((tll_node)app_ret_t1030)->data[1];
      instr_struct(&SPairUUU_t1032, 44, 2, x0_v905226, 0);
      switch_ret_t1031 = SPairUUU_t1032;
      break;
  }
  return switch_ret_t1031;
}

tll_ptr lam_fun_t1036(tll_ptr e_v905228, tll_env env) {
  tll_ptr SPairUUU_t1035;
  instr_struct(&SPairUUU_t1035, 44, 2, env[0], 0);
  return SPairUUU_t1035;
}

tll_ptr get_at_i66(tll_ptr A_v905217, tll_ptr n_v905218, tll_ptr xs_v905219) {
  tll_ptr ifte_ret_t1038; tll_ptr lam_clo_t1025; tll_ptr lam_clo_t1034;
  tll_ptr lam_clo_t1037; tll_ptr switch_ret_t1023; tll_ptr x_v905221;
  tll_ptr xs_v905222;
  switch(((tll_node)xs_v905219)->tag) {
    case 35:
      instr_clo(&lam_clo_t1025, &lam_fun_t1024, 0);
      switch_ret_t1023 = lam_clo_t1025;
      break;
    case 36:
      x_v905221 = ((tll_node)xs_v905219)->data[0];
      xs_v905222 = ((tll_node)xs_v905219)->data[1];
      if (n_v905218) {
        instr_clo(&lam_clo_t1034, &lam_fun_t1033, 2, xs_v905222, n_v905218);
        ifte_ret_t1038 = lam_clo_t1034;
      }
      else {
        instr_clo(&lam_clo_t1037, &lam_fun_t1036, 1, x_v905221);
        ifte_ret_t1038 = lam_clo_t1037;
      }
      switch_ret_t1023 = ifte_ret_t1038;
      break;
  }
  return switch_ret_t1023;
}

tll_ptr lam_fun_t1040(tll_ptr xs_v905234, tll_env env) {
  tll_ptr call_ret_t1039;
  call_ret_t1039 = get_at_i66(env[1], env[0], xs_v905234);
  return call_ret_t1039;
}

tll_ptr lam_fun_t1042(tll_ptr n_v905232, tll_env env) {
  tll_ptr lam_clo_t1041;
  instr_clo(&lam_clo_t1041, &lam_fun_t1040, 2, n_v905232, env[0]);
  return lam_clo_t1041;
}

tll_ptr lam_fun_t1044(tll_ptr A_v905229, tll_env env) {
  tll_ptr lam_clo_t1043;
  instr_clo(&lam_clo_t1043, &lam_fun_t1042, 1, A_v905229);
  return lam_clo_t1043;
}

tll_ptr lam_fun_t1314(tll_ptr __v905236, tll_env env) {
  tll_ptr Char_t1050; tll_ptr Char_t1051; tll_ptr Char_t1052;
  tll_ptr Char_t1053; tll_ptr Char_t1054; tll_ptr Char_t1062;
  tll_ptr Char_t1063; tll_ptr Char_t1064; tll_ptr Char_t1065;
  tll_ptr Char_t1066; tll_ptr Char_t1074; tll_ptr Char_t1075;
  tll_ptr Char_t1076; tll_ptr Char_t1077; tll_ptr Char_t1078;
  tll_ptr Char_t1086; tll_ptr Char_t1087; tll_ptr Char_t1088;
  tll_ptr Char_t1089; tll_ptr Char_t1090; tll_ptr Char_t1098;
  tll_ptr Char_t1099; tll_ptr Char_t1100; tll_ptr Char_t1101;
  tll_ptr Char_t1102; tll_ptr Char_t1110; tll_ptr Char_t1111;
  tll_ptr Char_t1112; tll_ptr Char_t1113; tll_ptr Char_t1114;
  tll_ptr Char_t1122; tll_ptr Char_t1123; tll_ptr Char_t1124;
  tll_ptr Char_t1125; tll_ptr Char_t1126; tll_ptr Char_t1134;
  tll_ptr Char_t1135; tll_ptr Char_t1136; tll_ptr Char_t1137;
  tll_ptr Char_t1138; tll_ptr Char_t1146; tll_ptr Char_t1147;
  tll_ptr Char_t1148; tll_ptr Char_t1149; tll_ptr Char_t1150;
  tll_ptr Char_t1158; tll_ptr Char_t1159; tll_ptr Char_t1160;
  tll_ptr Char_t1161; tll_ptr Char_t1162; tll_ptr Char_t1170;
  tll_ptr Char_t1171; tll_ptr Char_t1172; tll_ptr Char_t1173;
  tll_ptr Char_t1174; tll_ptr Char_t1182; tll_ptr Char_t1183;
  tll_ptr Char_t1184; tll_ptr Char_t1185; tll_ptr Char_t1186;
  tll_ptr Char_t1194; tll_ptr Char_t1195; tll_ptr Char_t1196;
  tll_ptr Char_t1197; tll_ptr Char_t1198; tll_ptr Char_t1206;
  tll_ptr Char_t1207; tll_ptr Char_t1208; tll_ptr Char_t1209;
  tll_ptr Char_t1210; tll_ptr Char_t1218; tll_ptr Char_t1219;
  tll_ptr Char_t1220; tll_ptr Char_t1221; tll_ptr Char_t1222;
  tll_ptr Char_t1230; tll_ptr Char_t1231; tll_ptr Char_t1232;
  tll_ptr Char_t1233; tll_ptr Char_t1234; tll_ptr Char_t1242;
  tll_ptr Char_t1243; tll_ptr Char_t1244; tll_ptr Char_t1245;
  tll_ptr Char_t1246; tll_ptr Char_t1254; tll_ptr Char_t1255;
  tll_ptr Char_t1256; tll_ptr Char_t1257; tll_ptr Char_t1258;
  tll_ptr Char_t1266; tll_ptr Char_t1267; tll_ptr Char_t1268;
  tll_ptr Char_t1269; tll_ptr Char_t1270; tll_ptr Char_t1278;
  tll_ptr Char_t1279; tll_ptr Char_t1280; tll_ptr Char_t1281;
  tll_ptr Char_t1282; tll_ptr EmptyString_t1055; tll_ptr EmptyString_t1067;
  tll_ptr EmptyString_t1079; tll_ptr EmptyString_t1091;
  tll_ptr EmptyString_t1103; tll_ptr EmptyString_t1115;
  tll_ptr EmptyString_t1127; tll_ptr EmptyString_t1139;
  tll_ptr EmptyString_t1151; tll_ptr EmptyString_t1163;
  tll_ptr EmptyString_t1175; tll_ptr EmptyString_t1187;
  tll_ptr EmptyString_t1199; tll_ptr EmptyString_t1211;
  tll_ptr EmptyString_t1223; tll_ptr EmptyString_t1235;
  tll_ptr EmptyString_t1247; tll_ptr EmptyString_t1259;
  tll_ptr EmptyString_t1271; tll_ptr EmptyString_t1283; tll_ptr String_t1056;
  tll_ptr String_t1057; tll_ptr String_t1058; tll_ptr String_t1059;
  tll_ptr String_t1060; tll_ptr String_t1068; tll_ptr String_t1069;
  tll_ptr String_t1070; tll_ptr String_t1071; tll_ptr String_t1072;
  tll_ptr String_t1080; tll_ptr String_t1081; tll_ptr String_t1082;
  tll_ptr String_t1083; tll_ptr String_t1084; tll_ptr String_t1092;
  tll_ptr String_t1093; tll_ptr String_t1094; tll_ptr String_t1095;
  tll_ptr String_t1096; tll_ptr String_t1104; tll_ptr String_t1105;
  tll_ptr String_t1106; tll_ptr String_t1107; tll_ptr String_t1108;
  tll_ptr String_t1116; tll_ptr String_t1117; tll_ptr String_t1118;
  tll_ptr String_t1119; tll_ptr String_t1120; tll_ptr String_t1128;
  tll_ptr String_t1129; tll_ptr String_t1130; tll_ptr String_t1131;
  tll_ptr String_t1132; tll_ptr String_t1140; tll_ptr String_t1141;
  tll_ptr String_t1142; tll_ptr String_t1143; tll_ptr String_t1144;
  tll_ptr String_t1152; tll_ptr String_t1153; tll_ptr String_t1154;
  tll_ptr String_t1155; tll_ptr String_t1156; tll_ptr String_t1164;
  tll_ptr String_t1165; tll_ptr String_t1166; tll_ptr String_t1167;
  tll_ptr String_t1168; tll_ptr String_t1176; tll_ptr String_t1177;
  tll_ptr String_t1178; tll_ptr String_t1179; tll_ptr String_t1180;
  tll_ptr String_t1188; tll_ptr String_t1189; tll_ptr String_t1190;
  tll_ptr String_t1191; tll_ptr String_t1192; tll_ptr String_t1200;
  tll_ptr String_t1201; tll_ptr String_t1202; tll_ptr String_t1203;
  tll_ptr String_t1204; tll_ptr String_t1212; tll_ptr String_t1213;
  tll_ptr String_t1214; tll_ptr String_t1215; tll_ptr String_t1216;
  tll_ptr String_t1224; tll_ptr String_t1225; tll_ptr String_t1226;
  tll_ptr String_t1227; tll_ptr String_t1228; tll_ptr String_t1236;
  tll_ptr String_t1237; tll_ptr String_t1238; tll_ptr String_t1239;
  tll_ptr String_t1240; tll_ptr String_t1248; tll_ptr String_t1249;
  tll_ptr String_t1250; tll_ptr String_t1251; tll_ptr String_t1252;
  tll_ptr String_t1260; tll_ptr String_t1261; tll_ptr String_t1262;
  tll_ptr String_t1263; tll_ptr String_t1264; tll_ptr String_t1272;
  tll_ptr String_t1273; tll_ptr String_t1274; tll_ptr String_t1275;
  tll_ptr String_t1276; tll_ptr String_t1284; tll_ptr String_t1285;
  tll_ptr String_t1286; tll_ptr String_t1287; tll_ptr String_t1288;
  tll_ptr Word_t1061; tll_ptr Word_t1073; tll_ptr Word_t1085;
  tll_ptr Word_t1097; tll_ptr Word_t1109; tll_ptr Word_t1121;
  tll_ptr Word_t1133; tll_ptr Word_t1145; tll_ptr Word_t1157;
  tll_ptr Word_t1169; tll_ptr Word_t1181; tll_ptr Word_t1193;
  tll_ptr Word_t1205; tll_ptr Word_t1217; tll_ptr Word_t1229;
  tll_ptr Word_t1241; tll_ptr Word_t1253; tll_ptr Word_t1265;
  tll_ptr Word_t1277; tll_ptr Word_t1289; tll_ptr __v905245;
  tll_ptr __v905248; tll_ptr app_ret_t1048; tll_ptr app_ret_t1049;
  tll_ptr app_ret_t1311; tll_ptr app_ret_t1312; tll_ptr consUU_t1291;
  tll_ptr consUU_t1292; tll_ptr consUU_t1293; tll_ptr consUU_t1294;
  tll_ptr consUU_t1295; tll_ptr consUU_t1296; tll_ptr consUU_t1297;
  tll_ptr consUU_t1298; tll_ptr consUU_t1299; tll_ptr consUU_t1300;
  tll_ptr consUU_t1301; tll_ptr consUU_t1302; tll_ptr consUU_t1303;
  tll_ptr consUU_t1304; tll_ptr consUU_t1305; tll_ptr consUU_t1306;
  tll_ptr consUU_t1307; tll_ptr consUU_t1308; tll_ptr consUU_t1309;
  tll_ptr consUU_t1310; tll_ptr n_v905244; tll_ptr nilUU_t1290;
  tll_ptr pf_v905246; tll_ptr r_v905243; tll_ptr rand_tmp_t1046;
  tll_ptr switch_ret_t1047; tll_ptr switch_ret_t1313; tll_ptr w_v905247;
  instr_rand(&rand_tmp_t1046, (tll_ptr)0, (tll_ptr)19);
  r_v905243 = rand_tmp_t1046;
  switch(((tll_node)r_v905243)->tag) {
    case 4:
      n_v905244 = ((tll_node)r_v905243)->data[0];
      __v905245 = ((tll_node)r_v905243)->data[1];
      pf_v905246 = ((tll_node)r_v905243)->data[2];
      instr_free_struct(r_v905243);
      instr_app(&app_ret_t1048, get_atclo_i149, 0);
      instr_app(&app_ret_t1049, app_ret_t1048, n_v905244);
      instr_struct(&Char_t1050, 5, 1, (tll_ptr)114);
      instr_struct(&Char_t1051, 5, 1, (tll_ptr)111);
      instr_struct(&Char_t1052, 5, 1, (tll_ptr)117);
      instr_struct(&Char_t1053, 5, 1, (tll_ptr)116);
      instr_struct(&Char_t1054, 5, 1, (tll_ptr)101);
      instr_struct(&EmptyString_t1055, 6, 0);
      instr_struct(&String_t1056, 7, 2, Char_t1054, EmptyString_t1055);
      instr_struct(&String_t1057, 7, 2, Char_t1053, String_t1056);
      instr_struct(&String_t1058, 7, 2, Char_t1052, String_t1057);
      instr_struct(&String_t1059, 7, 2, Char_t1051, String_t1058);
      instr_struct(&String_t1060, 7, 2, Char_t1050, String_t1059);
      instr_struct(&Word_t1061, 17, 2, String_t1060, 0);
      instr_struct(&Char_t1062, 5, 1, (tll_ptr)99);
      instr_struct(&Char_t1063, 5, 1, (tll_ptr)114);
      instr_struct(&Char_t1064, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t1065, 5, 1, (tll_ptr)115);
      instr_struct(&Char_t1066, 5, 1, (tll_ptr)104);
      instr_struct(&EmptyString_t1067, 6, 0);
      instr_struct(&String_t1068, 7, 2, Char_t1066, EmptyString_t1067);
      instr_struct(&String_t1069, 7, 2, Char_t1065, String_t1068);
      instr_struct(&String_t1070, 7, 2, Char_t1064, String_t1069);
      instr_struct(&String_t1071, 7, 2, Char_t1063, String_t1070);
      instr_struct(&String_t1072, 7, 2, Char_t1062, String_t1071);
      instr_struct(&Word_t1073, 17, 2, String_t1072, 0);
      instr_struct(&Char_t1074, 5, 1, (tll_ptr)99);
      instr_struct(&Char_t1075, 5, 1, (tll_ptr)108);
      instr_struct(&Char_t1076, 5, 1, (tll_ptr)111);
      instr_struct(&Char_t1077, 5, 1, (tll_ptr)119);
      instr_struct(&Char_t1078, 5, 1, (tll_ptr)110);
      instr_struct(&EmptyString_t1079, 6, 0);
      instr_struct(&String_t1080, 7, 2, Char_t1078, EmptyString_t1079);
      instr_struct(&String_t1081, 7, 2, Char_t1077, String_t1080);
      instr_struct(&String_t1082, 7, 2, Char_t1076, String_t1081);
      instr_struct(&String_t1083, 7, 2, Char_t1075, String_t1082);
      instr_struct(&String_t1084, 7, 2, Char_t1074, String_t1083);
      instr_struct(&Word_t1085, 17, 2, String_t1084, 0);
      instr_struct(&Char_t1086, 5, 1, (tll_ptr)115);
      instr_struct(&Char_t1087, 5, 1, (tll_ptr)104);
      instr_struct(&Char_t1088, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t1089, 5, 1, (tll_ptr)107);
      instr_struct(&Char_t1090, 5, 1, (tll_ptr)121);
      instr_struct(&EmptyString_t1091, 6, 0);
      instr_struct(&String_t1092, 7, 2, Char_t1090, EmptyString_t1091);
      instr_struct(&String_t1093, 7, 2, Char_t1089, String_t1092);
      instr_struct(&String_t1094, 7, 2, Char_t1088, String_t1093);
      instr_struct(&String_t1095, 7, 2, Char_t1087, String_t1094);
      instr_struct(&String_t1096, 7, 2, Char_t1086, String_t1095);
      instr_struct(&Word_t1097, 17, 2, String_t1096, 0);
      instr_struct(&Char_t1098, 5, 1, (tll_ptr)118);
      instr_struct(&Char_t1099, 5, 1, (tll_ptr)101);
      instr_struct(&Char_t1100, 5, 1, (tll_ptr)103);
      instr_struct(&Char_t1101, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t1102, 5, 1, (tll_ptr)110);
      instr_struct(&EmptyString_t1103, 6, 0);
      instr_struct(&String_t1104, 7, 2, Char_t1102, EmptyString_t1103);
      instr_struct(&String_t1105, 7, 2, Char_t1101, String_t1104);
      instr_struct(&String_t1106, 7, 2, Char_t1100, String_t1105);
      instr_struct(&String_t1107, 7, 2, Char_t1099, String_t1106);
      instr_struct(&String_t1108, 7, 2, Char_t1098, String_t1107);
      instr_struct(&Word_t1109, 17, 2, String_t1108, 0);
      instr_struct(&Char_t1110, 5, 1, (tll_ptr)112);
      instr_struct(&Char_t1111, 5, 1, (tll_ptr)111);
      instr_struct(&Char_t1112, 5, 1, (tll_ptr)119);
      instr_struct(&Char_t1113, 5, 1, (tll_ptr)101);
      instr_struct(&Char_t1114, 5, 1, (tll_ptr)114);
      instr_struct(&EmptyString_t1115, 6, 0);
      instr_struct(&String_t1116, 7, 2, Char_t1114, EmptyString_t1115);
      instr_struct(&String_t1117, 7, 2, Char_t1113, String_t1116);
      instr_struct(&String_t1118, 7, 2, Char_t1112, String_t1117);
      instr_struct(&String_t1119, 7, 2, Char_t1111, String_t1118);
      instr_struct(&String_t1120, 7, 2, Char_t1110, String_t1119);
      instr_struct(&Word_t1121, 17, 2, String_t1120, 0);
      instr_struct(&Char_t1122, 5, 1, (tll_ptr)116);
      instr_struct(&Char_t1123, 5, 1, (tll_ptr)114);
      instr_struct(&Char_t1124, 5, 1, (tll_ptr)117);
      instr_struct(&Char_t1125, 5, 1, (tll_ptr)115);
      instr_struct(&Char_t1126, 5, 1, (tll_ptr)116);
      instr_struct(&EmptyString_t1127, 6, 0);
      instr_struct(&String_t1128, 7, 2, Char_t1126, EmptyString_t1127);
      instr_struct(&String_t1129, 7, 2, Char_t1125, String_t1128);
      instr_struct(&String_t1130, 7, 2, Char_t1124, String_t1129);
      instr_struct(&String_t1131, 7, 2, Char_t1123, String_t1130);
      instr_struct(&String_t1132, 7, 2, Char_t1122, String_t1131);
      instr_struct(&Word_t1133, 17, 2, String_t1132, 0);
      instr_struct(&Char_t1134, 5, 1, (tll_ptr)101);
      instr_struct(&Char_t1135, 5, 1, (tll_ptr)110);
      instr_struct(&Char_t1136, 5, 1, (tll_ptr)106);
      instr_struct(&Char_t1137, 5, 1, (tll_ptr)111);
      instr_struct(&Char_t1138, 5, 1, (tll_ptr)121);
      instr_struct(&EmptyString_t1139, 6, 0);
      instr_struct(&String_t1140, 7, 2, Char_t1138, EmptyString_t1139);
      instr_struct(&String_t1141, 7, 2, Char_t1137, String_t1140);
      instr_struct(&String_t1142, 7, 2, Char_t1136, String_t1141);
      instr_struct(&String_t1143, 7, 2, Char_t1135, String_t1142);
      instr_struct(&String_t1144, 7, 2, Char_t1134, String_t1143);
      instr_struct(&Word_t1145, 17, 2, String_t1144, 0);
      instr_struct(&Char_t1146, 5, 1, (tll_ptr)98);
      instr_struct(&Char_t1147, 5, 1, (tll_ptr)114);
      instr_struct(&Char_t1148, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t1149, 5, 1, (tll_ptr)105);
      instr_struct(&Char_t1150, 5, 1, (tll_ptr)110);
      instr_struct(&EmptyString_t1151, 6, 0);
      instr_struct(&String_t1152, 7, 2, Char_t1150, EmptyString_t1151);
      instr_struct(&String_t1153, 7, 2, Char_t1149, String_t1152);
      instr_struct(&String_t1154, 7, 2, Char_t1148, String_t1153);
      instr_struct(&String_t1155, 7, 2, Char_t1147, String_t1154);
      instr_struct(&String_t1156, 7, 2, Char_t1146, String_t1155);
      instr_struct(&Word_t1157, 17, 2, String_t1156, 0);
      instr_struct(&Char_t1158, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t1159, 5, 1, (tll_ptr)100);
      instr_struct(&Char_t1160, 5, 1, (tll_ptr)111);
      instr_struct(&Char_t1161, 5, 1, (tll_ptr)112);
      instr_struct(&Char_t1162, 5, 1, (tll_ptr)116);
      instr_struct(&EmptyString_t1163, 6, 0);
      instr_struct(&String_t1164, 7, 2, Char_t1162, EmptyString_t1163);
      instr_struct(&String_t1165, 7, 2, Char_t1161, String_t1164);
      instr_struct(&String_t1166, 7, 2, Char_t1160, String_t1165);
      instr_struct(&String_t1167, 7, 2, Char_t1159, String_t1166);
      instr_struct(&String_t1168, 7, 2, Char_t1158, String_t1167);
      instr_struct(&Word_t1169, 17, 2, String_t1168, 0);
      instr_struct(&Char_t1170, 5, 1, (tll_ptr)116);
      instr_struct(&Char_t1171, 5, 1, (tll_ptr)111);
      instr_struct(&Char_t1172, 5, 1, (tll_ptr)119);
      instr_struct(&Char_t1173, 5, 1, (tll_ptr)101);
      instr_struct(&Char_t1174, 5, 1, (tll_ptr)114);
      instr_struct(&EmptyString_t1175, 6, 0);
      instr_struct(&String_t1176, 7, 2, Char_t1174, EmptyString_t1175);
      instr_struct(&String_t1177, 7, 2, Char_t1173, String_t1176);
      instr_struct(&String_t1178, 7, 2, Char_t1172, String_t1177);
      instr_struct(&String_t1179, 7, 2, Char_t1171, String_t1178);
      instr_struct(&String_t1180, 7, 2, Char_t1170, String_t1179);
      instr_struct(&Word_t1181, 17, 2, String_t1180, 0);
      instr_struct(&Char_t1182, 5, 1, (tll_ptr)115);
      instr_struct(&Char_t1183, 5, 1, (tll_ptr)104);
      instr_struct(&Char_t1184, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t1185, 5, 1, (tll_ptr)100);
      instr_struct(&Char_t1186, 5, 1, (tll_ptr)101);
      instr_struct(&EmptyString_t1187, 6, 0);
      instr_struct(&String_t1188, 7, 2, Char_t1186, EmptyString_t1187);
      instr_struct(&String_t1189, 7, 2, Char_t1185, String_t1188);
      instr_struct(&String_t1190, 7, 2, Char_t1184, String_t1189);
      instr_struct(&String_t1191, 7, 2, Char_t1183, String_t1190);
      instr_struct(&String_t1192, 7, 2, Char_t1182, String_t1191);
      instr_struct(&Word_t1193, 17, 2, String_t1192, 0);
      instr_struct(&Char_t1194, 5, 1, (tll_ptr)100);
      instr_struct(&Char_t1195, 5, 1, (tll_ptr)101);
      instr_struct(&Char_t1196, 5, 1, (tll_ptr)108);
      instr_struct(&Char_t1197, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t1198, 5, 1, (tll_ptr)121);
      instr_struct(&EmptyString_t1199, 6, 0);
      instr_struct(&String_t1200, 7, 2, Char_t1198, EmptyString_t1199);
      instr_struct(&String_t1201, 7, 2, Char_t1197, String_t1200);
      instr_struct(&String_t1202, 7, 2, Char_t1196, String_t1201);
      instr_struct(&String_t1203, 7, 2, Char_t1195, String_t1202);
      instr_struct(&String_t1204, 7, 2, Char_t1194, String_t1203);
      instr_struct(&Word_t1205, 17, 2, String_t1204, 0);
      instr_struct(&Char_t1206, 5, 1, (tll_ptr)116);
      instr_struct(&Char_t1207, 5, 1, (tll_ptr)119);
      instr_struct(&Char_t1208, 5, 1, (tll_ptr)105);
      instr_struct(&Char_t1209, 5, 1, (tll_ptr)115);
      instr_struct(&Char_t1210, 5, 1, (tll_ptr)116);
      instr_struct(&EmptyString_t1211, 6, 0);
      instr_struct(&String_t1212, 7, 2, Char_t1210, EmptyString_t1211);
      instr_struct(&String_t1213, 7, 2, Char_t1209, String_t1212);
      instr_struct(&String_t1214, 7, 2, Char_t1208, String_t1213);
      instr_struct(&String_t1215, 7, 2, Char_t1207, String_t1214);
      instr_struct(&String_t1216, 7, 2, Char_t1206, String_t1215);
      instr_struct(&Word_t1217, 17, 2, String_t1216, 0);
      instr_struct(&Char_t1218, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t1219, 5, 1, (tll_ptr)108);
      instr_struct(&Char_t1220, 5, 1, (tll_ptr)101);
      instr_struct(&Char_t1221, 5, 1, (tll_ptr)114);
      instr_struct(&Char_t1222, 5, 1, (tll_ptr)116);
      instr_struct(&EmptyString_t1223, 6, 0);
      instr_struct(&String_t1224, 7, 2, Char_t1222, EmptyString_t1223);
      instr_struct(&String_t1225, 7, 2, Char_t1221, String_t1224);
      instr_struct(&String_t1226, 7, 2, Char_t1220, String_t1225);
      instr_struct(&String_t1227, 7, 2, Char_t1219, String_t1226);
      instr_struct(&String_t1228, 7, 2, Char_t1218, String_t1227);
      instr_struct(&Word_t1229, 17, 2, String_t1228, 0);
      instr_struct(&Char_t1230, 5, 1, (tll_ptr)99);
      instr_struct(&Char_t1231, 5, 1, (tll_ptr)104);
      instr_struct(&Char_t1232, 5, 1, (tll_ptr)111);
      instr_struct(&Char_t1233, 5, 1, (tll_ptr)107);
      instr_struct(&Char_t1234, 5, 1, (tll_ptr)101);
      instr_struct(&EmptyString_t1235, 6, 0);
      instr_struct(&String_t1236, 7, 2, Char_t1234, EmptyString_t1235);
      instr_struct(&String_t1237, 7, 2, Char_t1233, String_t1236);
      instr_struct(&String_t1238, 7, 2, Char_t1232, String_t1237);
      instr_struct(&String_t1239, 7, 2, Char_t1231, String_t1238);
      instr_struct(&String_t1240, 7, 2, Char_t1230, String_t1239);
      instr_struct(&Word_t1241, 17, 2, String_t1240, 0);
      instr_struct(&Char_t1242, 5, 1, (tll_ptr)115);
      instr_struct(&Char_t1243, 5, 1, (tll_ptr)112);
      instr_struct(&Char_t1244, 5, 1, (tll_ptr)108);
      instr_struct(&Char_t1245, 5, 1, (tll_ptr)105);
      instr_struct(&Char_t1246, 5, 1, (tll_ptr)116);
      instr_struct(&EmptyString_t1247, 6, 0);
      instr_struct(&String_t1248, 7, 2, Char_t1246, EmptyString_t1247);
      instr_struct(&String_t1249, 7, 2, Char_t1245, String_t1248);
      instr_struct(&String_t1250, 7, 2, Char_t1244, String_t1249);
      instr_struct(&String_t1251, 7, 2, Char_t1243, String_t1250);
      instr_struct(&String_t1252, 7, 2, Char_t1242, String_t1251);
      instr_struct(&Word_t1253, 17, 2, String_t1252, 0);
      instr_struct(&Char_t1254, 5, 1, (tll_ptr)114);
      instr_struct(&Char_t1255, 5, 1, (tll_ptr)104);
      instr_struct(&Char_t1256, 5, 1, (tll_ptr)121);
      instr_struct(&Char_t1257, 5, 1, (tll_ptr)109);
      instr_struct(&Char_t1258, 5, 1, (tll_ptr)101);
      instr_struct(&EmptyString_t1259, 6, 0);
      instr_struct(&String_t1260, 7, 2, Char_t1258, EmptyString_t1259);
      instr_struct(&String_t1261, 7, 2, Char_t1257, String_t1260);
      instr_struct(&String_t1262, 7, 2, Char_t1256, String_t1261);
      instr_struct(&String_t1263, 7, 2, Char_t1255, String_t1262);
      instr_struct(&String_t1264, 7, 2, Char_t1254, String_t1263);
      instr_struct(&Word_t1265, 17, 2, String_t1264, 0);
      instr_struct(&Char_t1266, 5, 1, (tll_ptr)109);
      instr_struct(&Char_t1267, 5, 1, (tll_ptr)117);
      instr_struct(&Char_t1268, 5, 1, (tll_ptr)100);
      instr_struct(&Char_t1269, 5, 1, (tll_ptr)100);
      instr_struct(&Char_t1270, 5, 1, (tll_ptr)121);
      instr_struct(&EmptyString_t1271, 6, 0);
      instr_struct(&String_t1272, 7, 2, Char_t1270, EmptyString_t1271);
      instr_struct(&String_t1273, 7, 2, Char_t1269, String_t1272);
      instr_struct(&String_t1274, 7, 2, Char_t1268, String_t1273);
      instr_struct(&String_t1275, 7, 2, Char_t1267, String_t1274);
      instr_struct(&String_t1276, 7, 2, Char_t1266, String_t1275);
      instr_struct(&Word_t1277, 17, 2, String_t1276, 0);
      instr_struct(&Char_t1278, 5, 1, (tll_ptr)112);
      instr_struct(&Char_t1279, 5, 1, (tll_ptr)108);
      instr_struct(&Char_t1280, 5, 1, (tll_ptr)97);
      instr_struct(&Char_t1281, 5, 1, (tll_ptr)110);
      instr_struct(&Char_t1282, 5, 1, (tll_ptr)116);
      instr_struct(&EmptyString_t1283, 6, 0);
      instr_struct(&String_t1284, 7, 2, Char_t1282, EmptyString_t1283);
      instr_struct(&String_t1285, 7, 2, Char_t1281, String_t1284);
      instr_struct(&String_t1286, 7, 2, Char_t1280, String_t1285);
      instr_struct(&String_t1287, 7, 2, Char_t1279, String_t1286);
      instr_struct(&String_t1288, 7, 2, Char_t1278, String_t1287);
      instr_struct(&Word_t1289, 17, 2, String_t1288, 0);
      instr_struct(&nilUU_t1290, 35, 0);
      instr_struct(&consUU_t1291, 36, 2, Word_t1289, nilUU_t1290);
      instr_struct(&consUU_t1292, 36, 2, Word_t1277, consUU_t1291);
      instr_struct(&consUU_t1293, 36, 2, Word_t1265, consUU_t1292);
      instr_struct(&consUU_t1294, 36, 2, Word_t1253, consUU_t1293);
      instr_struct(&consUU_t1295, 36, 2, Word_t1241, consUU_t1294);
      instr_struct(&consUU_t1296, 36, 2, Word_t1229, consUU_t1295);
      instr_struct(&consUU_t1297, 36, 2, Word_t1217, consUU_t1296);
      instr_struct(&consUU_t1298, 36, 2, Word_t1205, consUU_t1297);
      instr_struct(&consUU_t1299, 36, 2, Word_t1193, consUU_t1298);
      instr_struct(&consUU_t1300, 36, 2, Word_t1181, consUU_t1299);
      instr_struct(&consUU_t1301, 36, 2, Word_t1169, consUU_t1300);
      instr_struct(&consUU_t1302, 36, 2, Word_t1157, consUU_t1301);
      instr_struct(&consUU_t1303, 36, 2, Word_t1145, consUU_t1302);
      instr_struct(&consUU_t1304, 36, 2, Word_t1133, consUU_t1303);
      instr_struct(&consUU_t1305, 36, 2, Word_t1121, consUU_t1304);
      instr_struct(&consUU_t1306, 36, 2, Word_t1109, consUU_t1305);
      instr_struct(&consUU_t1307, 36, 2, Word_t1097, consUU_t1306);
      instr_struct(&consUU_t1308, 36, 2, Word_t1085, consUU_t1307);
      instr_struct(&consUU_t1309, 36, 2, Word_t1073, consUU_t1308);
      instr_struct(&consUU_t1310, 36, 2, Word_t1061, consUU_t1309);
      instr_app(&app_ret_t1311, app_ret_t1049, consUU_t1310);
      instr_app(&app_ret_t1312, app_ret_t1311, 0);
      switch(((tll_node)app_ret_t1312)->tag) {
        case 44:
          w_v905247 = ((tll_node)app_ret_t1312)->data[0];
          __v905248 = ((tll_node)app_ret_t1312)->data[1];
          switch_ret_t1313 = w_v905247;
          break;
      }
      switch_ret_t1047 = switch_ret_t1313;
      break;
  }
  return switch_ret_t1047;
}

tll_ptr rand_word_i67(tll_ptr __v905235) {
  tll_ptr lam_clo_t1315;
  instr_clo(&lam_clo_t1315, &lam_fun_t1314, 0);
  return lam_clo_t1315;
}

tll_ptr lam_fun_t1317(tll_ptr __v905249, tll_env env) {
  tll_ptr call_ret_t1316;
  call_ret_t1316 = rand_word_i67(__v905249);
  return call_ret_t1316;
}

tll_ptr lam_fun_t1323(tll_ptr __v905287, tll_env env) {
  
  
  return 0;
}

tll_ptr lam_fun_t1325(tll_ptr c_v905285, tll_env env) {
  tll_ptr lam_clo_t1324;
  instr_clo(&lam_clo_t1324, &lam_fun_t1323, 0);
  return lam_clo_t1324;
}

tll_ptr lam_fun_t1333(tll_ptr __v905295, tll_env env) {
  tll_ptr add_ret_t1331; tll_ptr app_ret_t1332; tll_ptr c_v905297;
  tll_ptr call_ret_t1330; tll_ptr send_ch_t1329;
  instr_send(&send_ch_t1329, env[1], env[0]);
  c_v905297 = send_ch_t1329;
  add_ret_t1331 = env[2] - 1;
  call_ret_t1330 = server_loop_i68(env[3], add_ret_t1331, c_v905297);
  instr_app(&app_ret_t1332, call_ret_t1330, 0);
  instr_free_clo(call_ret_t1330);
  return app_ret_t1332;
}

tll_ptr lam_fun_t1335(tll_ptr c_v905288, tll_env env) {
  tll_ptr call_ret_t1327; tll_ptr df_v905293; tll_ptr lam_clo_t1334;
  tll_ptr pf_v905294; tll_ptr switch_ret_t1328;
  call_ret_t1327 = word_diff_i54(env[2], env[0]);
  switch(((tll_node)call_ret_t1327)->tag) {
    case 44:
      df_v905293 = ((tll_node)call_ret_t1327)->data[0];
      pf_v905294 = ((tll_node)call_ret_t1327)->data[1];
      instr_clo(&lam_clo_t1334, &lam_fun_t1333, 4,
                df_v905293, c_v905288, env[1], env[2]);
      switch_ret_t1328 = lam_clo_t1334;
      break;
  }
  return switch_ret_t1328;
}

tll_ptr lam_fun_t1340(tll_ptr __v905267, tll_env env) {
  tll_ptr __v905280; tll_ptr app_ret_t1338; tll_ptr app_ret_t1339;
  tll_ptr b_v905283; tll_ptr c_v905282; tll_ptr c_v905284;
  tll_ptr call_ret_t1321; tll_ptr guess_v905281; tll_ptr ifte_ret_t1337;
  tll_ptr lam_clo_t1326; tll_ptr lam_clo_t1336; tll_ptr recv_msg_t1319;
  tll_ptr send_ch_t1322; tll_ptr switch_ret_t1320;
  instr_recv(&recv_msg_t1319, env[0]);
  __v905280 = recv_msg_t1319;
  switch(((tll_node)__v905280)->tag) {
    case 0:
      guess_v905281 = ((tll_node)__v905280)->data[0];
      c_v905282 = ((tll_node)__v905280)->data[1];
      instr_free_struct(__v905280);
      call_ret_t1321 = eqw_i55(env[2], guess_v905281);
      b_v905283 = call_ret_t1321;
      instr_send(&send_ch_t1322, c_v905282, b_v905283);
      c_v905284 = send_ch_t1322;
      if (b_v905283) {
        instr_clo(&lam_clo_t1326, &lam_fun_t1325, 0);
        ifte_ret_t1337 = lam_clo_t1326;
      }
      else {
        instr_clo(&lam_clo_t1336, &lam_fun_t1335, 3,
                  guess_v905281, env[1], env[2]);
        ifte_ret_t1337 = lam_clo_t1336;
      }
      instr_app(&app_ret_t1338, ifte_ret_t1337, c_v905284);
      instr_free_clo(ifte_ret_t1337);
      instr_app(&app_ret_t1339, app_ret_t1338, 0);
      instr_free_clo(app_ret_t1338);
      switch_ret_t1320 = app_ret_t1339;
      break;
  }
  return switch_ret_t1320;
}

tll_ptr lam_fun_t1342(tll_ptr c_v905253, tll_env env) {
  tll_ptr lam_clo_t1341;
  instr_clo(&lam_clo_t1341, &lam_fun_t1340, 3, c_v905253, env[0], env[1]);
  return lam_clo_t1341;
}

tll_ptr lam_fun_t1345(tll_ptr __v905301, tll_env env) {
  tll_ptr c_v905303; tll_ptr send_ch_t1344;
  instr_send(&send_ch_t1344, env[0], env[1]);
  c_v905303 = send_ch_t1344;
  return 0;
}

tll_ptr lam_fun_t1347(tll_ptr c_v905298, tll_env env) {
  tll_ptr lam_clo_t1346;
  instr_clo(&lam_clo_t1346, &lam_fun_t1345, 2, c_v905298, env[0]);
  return lam_clo_t1346;
}

tll_ptr server_loop_i68(tll_ptr ans_v905250, tll_ptr repeat_v905251, tll_ptr c_v905252) {
  tll_ptr app_ret_t1350; tll_ptr ifte_ret_t1349; tll_ptr lam_clo_t1343;
  tll_ptr lam_clo_t1348;
  if (repeat_v905251) {
    instr_clo(&lam_clo_t1343, &lam_fun_t1342, 2, repeat_v905251, ans_v905250);
    ifte_ret_t1349 = lam_clo_t1343;
  }
  else {
    instr_clo(&lam_clo_t1348, &lam_fun_t1347, 1, ans_v905250);
    ifte_ret_t1349 = lam_clo_t1348;
  }
  instr_app(&app_ret_t1350, ifte_ret_t1349, c_v905252);
  return app_ret_t1350;
}

tll_ptr lam_fun_t1352(tll_ptr c_v905309, tll_env env) {
  tll_ptr call_ret_t1351;
  call_ret_t1351 = server_loop_i68(env[1], env[0], c_v905309);
  return call_ret_t1351;
}

tll_ptr lam_fun_t1354(tll_ptr repeat_v905307, tll_env env) {
  tll_ptr lam_clo_t1353;
  instr_clo(&lam_clo_t1353, &lam_fun_t1352, 2, repeat_v905307, env[0]);
  return lam_clo_t1353;
}

tll_ptr lam_fun_t1356(tll_ptr ans_v905304, tll_env env) {
  tll_ptr lam_clo_t1355;
  instr_clo(&lam_clo_t1355, &lam_fun_t1354, 1, ans_v905304);
  return lam_clo_t1355;
}

tll_ptr lam_fun_t1363(tll_ptr __v905311, tll_env env) {
  tll_ptr ans_v905314; tll_ptr app_ret_t1359; tll_ptr app_ret_t1362;
  tll_ptr c_v905315; tll_ptr call_ret_t1358; tll_ptr call_ret_t1361;
  tll_ptr send_ch_t1360;
  call_ret_t1358 = rand_word_i67(0);
  instr_app(&app_ret_t1359, call_ret_t1358, 0);
  instr_free_clo(call_ret_t1358);
  ans_v905314 = app_ret_t1359;
  instr_send(&send_ch_t1360, env[0], (tll_ptr)6);
  c_v905315 = send_ch_t1360;
  call_ret_t1361 = server_loop_i68(ans_v905314, (tll_ptr)6, c_v905315);
  instr_app(&app_ret_t1362, call_ret_t1361, 0);
  instr_free_clo(call_ret_t1361);
  return app_ret_t1362;
}

tll_ptr server_i69(tll_ptr c_v905310) {
  tll_ptr lam_clo_t1364;
  instr_clo(&lam_clo_t1364, &lam_fun_t1363, 1, c_v905310);
  return lam_clo_t1364;
}

tll_ptr lam_fun_t1366(tll_ptr c_v905316, tll_env env) {
  tll_ptr call_ret_t1365;
  call_ret_t1365 = server_i69(c_v905316);
  return call_ret_t1365;
}

tll_ptr fork_fun_t1370(tll_env env) {
  tll_ptr app_ret_t1369; tll_ptr call_ret_t1368; tll_ptr fork_ret_t1372;
  call_ret_t1368 = server_i69(env[0]);
  instr_app(&app_ret_t1369, call_ret_t1368, 0);
  instr_free_clo(call_ret_t1368);
  fork_ret_t1372 = app_ret_t1369;
  instr_free_thread(env);
  return fork_ret_t1372;
}

tll_ptr fork_fun_t1378(tll_env env) {
  tll_ptr __v905326; tll_ptr __v905329; tll_ptr app_ret_t1376;
  tll_ptr c0_v905328; tll_ptr c0_v905330; tll_ptr c_v905327;
  tll_ptr call_ret_t1375; tll_ptr fork_ret_t1380; tll_ptr recv_msg_t1373;
  tll_ptr send_ch_t1377; tll_ptr switch_ret_t1374;
  instr_recv(&recv_msg_t1373, env[0]);
  __v905326 = recv_msg_t1373;
  switch(((tll_node)__v905326)->tag) {
    case 0:
      c_v905327 = ((tll_node)__v905326)->data[0];
      c0_v905328 = ((tll_node)__v905326)->data[1];
      instr_free_struct(__v905326);
      call_ret_t1375 = player_i64(c_v905327);
      instr_app(&app_ret_t1376, call_ret_t1375, 0);
      instr_free_clo(call_ret_t1375);
      __v905329 = app_ret_t1376;
      instr_send(&send_ch_t1377, c0_v905328, 0);
      c0_v905330 = send_ch_t1377;
      switch_ret_t1374 = 0;
      break;
  }
  fork_ret_t1380 = switch_ret_t1374;
  instr_free_thread(env);
  return fork_ret_t1380;
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
  tll_ptr String_t363; tll_ptr String_t366; tll_ptr __v905332;
  tll_ptr __v905333; tll_ptr c0_v905319; tll_ptr c0_v905331;
  tll_ptr c0_v905334; tll_ptr c_v905317; tll_ptr close_tmp_t1384;
  tll_ptr consUU_t368; tll_ptr consUU_t369; tll_ptr consUU_t370;
  tll_ptr consUU_t371; tll_ptr consUU_t372; tll_ptr consUU_t373;
  tll_ptr consUU_t374; tll_ptr consUU_t375; tll_ptr consUU_t376;
  tll_ptr consUU_t377; tll_ptr fork_ch_t1371; tll_ptr fork_ch_t1379;
  tll_ptr lam_clo_t1022; tll_ptr lam_clo_t104; tll_ptr lam_clo_t1045;
  tll_ptr lam_clo_t110; tll_ptr lam_clo_t118; tll_ptr lam_clo_t12;
  tll_ptr lam_clo_t126; tll_ptr lam_clo_t1318; tll_ptr lam_clo_t134;
  tll_ptr lam_clo_t1357; tll_ptr lam_clo_t1367; tll_ptr lam_clo_t140;
  tll_ptr lam_clo_t151; tll_ptr lam_clo_t16; tll_ptr lam_clo_t167;
  tll_ptr lam_clo_t179; tll_ptr lam_clo_t191; tll_ptr lam_clo_t203;
  tll_ptr lam_clo_t215; tll_ptr lam_clo_t227; tll_ptr lam_clo_t239;
  tll_ptr lam_clo_t252; tll_ptr lam_clo_t265; tll_ptr lam_clo_t278;
  tll_ptr lam_clo_t28; tll_ptr lam_clo_t288; tll_ptr lam_clo_t298;
  tll_ptr lam_clo_t308; tll_ptr lam_clo_t318; tll_ptr lam_clo_t327;
  tll_ptr lam_clo_t336; tll_ptr lam_clo_t34; tll_ptr lam_clo_t391;
  tll_ptr lam_clo_t396; tll_ptr lam_clo_t40; tll_ptr lam_clo_t406;
  tll_ptr lam_clo_t450; tll_ptr lam_clo_t46; tll_ptr lam_clo_t463;
  tll_ptr lam_clo_t467; tll_ptr lam_clo_t476; tll_ptr lam_clo_t52;
  tll_ptr lam_clo_t530; tll_ptr lam_clo_t544; tll_ptr lam_clo_t552;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t6; tll_ptr lam_clo_t652;
  tll_ptr lam_clo_t72; tll_ptr lam_clo_t77; tll_ptr lam_clo_t83;
  tll_ptr lam_clo_t874; tll_ptr lam_clo_t92; tll_ptr lam_clo_t98;
  tll_ptr nilUU_t367; tll_ptr recv_msg_t1382; tll_ptr send_ch_t1381;
  tll_ptr switch_ret_t1383;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i99 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i100 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i101 = lam_clo_t16;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  comparebclo_i102 = lam_clo_t28;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 0);
  ltenclo_i103 = lam_clo_t34;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 0);
  ltnclo_i104 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  gtenclo_i105 = lam_clo_t46;
  instr_clo(&lam_clo_t52, &lam_fun_t51, 0);
  gtnclo_i106 = lam_clo_t52;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  eqnclo_i107 = lam_clo_t58;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  comparenclo_i108 = lam_clo_t72;
  instr_clo(&lam_clo_t77, &lam_fun_t76, 0);
  predclo_i109 = lam_clo_t77;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i110 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i111 = lam_clo_t92;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  mulnclo_i112 = lam_clo_t98;
  instr_clo(&lam_clo_t104, &lam_fun_t103, 0);
  divnclo_i113 = lam_clo_t104;
  instr_clo(&lam_clo_t110, &lam_fun_t109, 0);
  modnclo_i114 = lam_clo_t110;
  instr_clo(&lam_clo_t118, &lam_fun_t117, 0);
  eqcclo_i115 = lam_clo_t118;
  instr_clo(&lam_clo_t126, &lam_fun_t125, 0);
  comparecclo_i116 = lam_clo_t126;
  instr_clo(&lam_clo_t134, &lam_fun_t133, 0);
  catsclo_i117 = lam_clo_t134;
  instr_clo(&lam_clo_t140, &lam_fun_t139, 0);
  strlenclo_i118 = lam_clo_t140;
  instr_clo(&lam_clo_t151, &lam_fun_t150, 0);
  eqsclo_i119 = lam_clo_t151;
  instr_clo(&lam_clo_t167, &lam_fun_t166, 0);
  comparesclo_i120 = lam_clo_t167;
  instr_clo(&lam_clo_t179, &lam_fun_t178, 0);
  and_thenUUUclo_i121 = lam_clo_t179;
  instr_clo(&lam_clo_t191, &lam_fun_t190, 0);
  and_thenUULclo_i122 = lam_clo_t191;
  instr_clo(&lam_clo_t203, &lam_fun_t202, 0);
  and_thenULUclo_i123 = lam_clo_t203;
  instr_clo(&lam_clo_t215, &lam_fun_t214, 0);
  and_thenULLclo_i124 = lam_clo_t215;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 0);
  and_thenLULclo_i125 = lam_clo_t227;
  instr_clo(&lam_clo_t239, &lam_fun_t238, 0);
  and_thenLLLclo_i126 = lam_clo_t239;
  instr_clo(&lam_clo_t252, &lam_fun_t251, 0);
  lenUUclo_i127 = lam_clo_t252;
  instr_clo(&lam_clo_t265, &lam_fun_t264, 0);
  lenULclo_i128 = lam_clo_t265;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 0);
  lenLLclo_i129 = lam_clo_t278;
  instr_clo(&lam_clo_t288, &lam_fun_t287, 0);
  appendUUclo_i130 = lam_clo_t288;
  instr_clo(&lam_clo_t298, &lam_fun_t297, 0);
  appendULclo_i131 = lam_clo_t298;
  instr_clo(&lam_clo_t308, &lam_fun_t307, 0);
  appendLLclo_i132 = lam_clo_t308;
  instr_clo(&lam_clo_t318, &lam_fun_t317, 0);
  readlineclo_i133 = lam_clo_t318;
  instr_clo(&lam_clo_t327, &lam_fun_t326, 0);
  printclo_i134 = lam_clo_t327;
  instr_clo(&lam_clo_t336, &lam_fun_t335, 0);
  prerrclo_i135 = lam_clo_t336;
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
  instr_struct(&nilUU_t367, 35, 0);
  instr_struct(&consUU_t368, 36, 2, String_t366, nilUU_t367);
  instr_struct(&consUU_t369, 36, 2, String_t363, consUU_t368);
  instr_struct(&consUU_t370, 36, 2, String_t360, consUU_t369);
  instr_struct(&consUU_t371, 36, 2, String_t357, consUU_t370);
  instr_struct(&consUU_t372, 36, 2, String_t354, consUU_t371);
  instr_struct(&consUU_t373, 36, 2, String_t351, consUU_t372);
  instr_struct(&consUU_t374, 36, 2, String_t348, consUU_t373);
  instr_struct(&consUU_t375, 36, 2, String_t345, consUU_t374);
  instr_struct(&consUU_t376, 36, 2, String_t342, consUU_t375);
  instr_struct(&consUU_t377, 36, 2, String_t339, consUU_t376);
  digits_i36 = consUU_t377;
  instr_clo(&lam_clo_t391, &lam_fun_t390, 0);
  get_atclo_i136 = lam_clo_t391;
  instr_clo(&lam_clo_t396, &lam_fun_t395, 0);
  string_of_digitclo_i137 = lam_clo_t396;
  instr_clo(&lam_clo_t406, &lam_fun_t405, 0);
  string_of_natclo_i138 = lam_clo_t406;
  instr_clo(&lam_clo_t450, &lam_fun_t449, 0);
  digit_of_charclo_i139 = lam_clo_t450;
  instr_clo(&lam_clo_t463, &lam_fun_t462, 0);
  nat_of_string_loopclo_i140 = lam_clo_t463;
  instr_clo(&lam_clo_t467, &lam_fun_t466, 0);
  nat_of_stringclo_i141 = lam_clo_t467;
  instr_clo(&lam_clo_t476, &lam_fun_t475, 0);
  containsclo_i142 = lam_clo_t476;
  instr_clo(&lam_clo_t530, &lam_fun_t529, 0);
  string_diffclo_i143 = lam_clo_t530;
  instr_clo(&lam_clo_t544, &lam_fun_t543, 0);
  word_diffclo_i144 = lam_clo_t544;
  instr_clo(&lam_clo_t552, &lam_fun_t551, 0);
  eqwclo_i145 = lam_clo_t552;
  instr_clo(&lam_clo_t652, &lam_fun_t651, 0);
  read_wordclo_i146 = lam_clo_t652;
  instr_clo(&lam_clo_t874, &lam_fun_t873, 0);
  player_loopclo_i147 = lam_clo_t874;
  instr_clo(&lam_clo_t1022, &lam_fun_t1021, 0);
  playerclo_i148 = lam_clo_t1022;
  instr_clo(&lam_clo_t1045, &lam_fun_t1044, 0);
  get_atclo_i149 = lam_clo_t1045;
  instr_clo(&lam_clo_t1318, &lam_fun_t1317, 0);
  rand_wordclo_i150 = lam_clo_t1318;
  instr_clo(&lam_clo_t1357, &lam_fun_t1356, 0);
  server_loopclo_i151 = lam_clo_t1357;
  instr_clo(&lam_clo_t1367, &lam_fun_t1366, 0);
  serverclo_i152 = lam_clo_t1367;
  instr_fork(&fork_ch_t1371, &fork_fun_t1370, 0);
  c_v905317 = fork_ch_t1371;
  instr_fork(&fork_ch_t1379, &fork_fun_t1378, 0);
  c0_v905319 = fork_ch_t1379;
  instr_send(&send_ch_t1381, c0_v905319, c_v905317);
  c0_v905331 = send_ch_t1381;
  instr_recv(&recv_msg_t1382, c0_v905331);
  __v905332 = recv_msg_t1382;
  switch(((tll_node)__v905332)->tag) {
    case 0:
      __v905333 = ((tll_node)__v905332)->data[0];
      c0_v905334 = ((tll_node)__v905332)->data[1];
      instr_free_struct(__v905332);
      instr_close(&close_tmp_t1384, c0_v905334);
      switch_ret_t1383 = close_tmp_t1384;
      break;
  }
  return 0;
}

