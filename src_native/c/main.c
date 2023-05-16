#include"runtime.h"

tll_ptr andb_i2(tll_ptr b1_v21780, tll_ptr b2_v21781);
tll_ptr orb_i3(tll_ptr b1_v21785, tll_ptr b2_v21786);
tll_ptr notb_i4(tll_ptr b_v21790);
tll_ptr compareb_i5(tll_ptr b1_v21792, tll_ptr b2_v21793);
tll_ptr lten_i6(tll_ptr x_v21797, tll_ptr y_v21798);
tll_ptr gten_i7(tll_ptr x_v21802, tll_ptr y_v21803);
tll_ptr ltn_i8(tll_ptr x_v21807, tll_ptr y_v21808);
tll_ptr gtn_i9(tll_ptr x_v21812, tll_ptr y_v21813);
tll_ptr eqn_i10(tll_ptr x_v21817, tll_ptr y_v21818);
tll_ptr comparen_i11(tll_ptr n1_v21822, tll_ptr n2_v21823);
tll_ptr pred_i12(tll_ptr x_v21827);
tll_ptr addn_i13(tll_ptr x_v21829, tll_ptr y_v21830);
tll_ptr subn_i14(tll_ptr x_v21834, tll_ptr y_v21835);
tll_ptr muln_i15(tll_ptr x_v21839, tll_ptr y_v21840);
tll_ptr divn_i16(tll_ptr x_v21844, tll_ptr y_v21845);
tll_ptr modn_i17(tll_ptr x_v21849, tll_ptr y_v21850);
tll_ptr eqc_i18(tll_ptr c1_v21854, tll_ptr c2_v21855);
tll_ptr comparec_i19(tll_ptr c1_v21861, tll_ptr c2_v21862);
tll_ptr cats_i20(tll_ptr s1_v21868, tll_ptr s2_v21869);
tll_ptr strlen_i21(tll_ptr s_v21875);
tll_ptr eqs_i22(tll_ptr s1_v21879, tll_ptr s2_v21880);
tll_ptr compares_i23(tll_ptr s1_v21890, tll_ptr s2_v21891);
tll_ptr and_thenUUU_i61(tll_ptr A_v21901, tll_ptr B_v21902, tll_ptr opt_v21903, tll_ptr f_v21904);
tll_ptr and_thenUUL_i60(tll_ptr A_v21916, tll_ptr B_v21917, tll_ptr opt_v21918, tll_ptr f_v21919);
tll_ptr and_thenULU_i59(tll_ptr A_v21931, tll_ptr B_v21932, tll_ptr opt_v21933, tll_ptr f_v21934);
tll_ptr and_thenULL_i58(tll_ptr A_v21946, tll_ptr B_v21947, tll_ptr opt_v21948, tll_ptr f_v21949);
tll_ptr and_thenLUL_i56(tll_ptr A_v21961, tll_ptr B_v21962, tll_ptr opt_v21963, tll_ptr f_v21964);
tll_ptr and_thenLLL_i54(tll_ptr A_v21976, tll_ptr B_v21977, tll_ptr opt_v21978, tll_ptr f_v21979);
tll_ptr lenUU_i65(tll_ptr A_v21991, tll_ptr xs_v21992);
tll_ptr lenUL_i64(tll_ptr A_v22000, tll_ptr xs_v22001);
tll_ptr lenLL_i62(tll_ptr A_v22009, tll_ptr xs_v22010);
tll_ptr appendUU_i69(tll_ptr A_v22018, tll_ptr xs_v22019, tll_ptr ys_v22020);
tll_ptr appendUL_i68(tll_ptr A_v22029, tll_ptr xs_v22030, tll_ptr ys_v22031);
tll_ptr appendLL_i66(tll_ptr A_v22040, tll_ptr xs_v22041, tll_ptr ys_v22042);
tll_ptr readline_i33(tll_ptr __v22051);
tll_ptr print_i34(tll_ptr s_v22066);
tll_ptr prerr_i35(tll_ptr s_v22077);
tll_ptr get_at_i37(tll_ptr A_v22088, tll_ptr n_v22089, tll_ptr xs_v22090, tll_ptr a_v22091);
tll_ptr string_of_digit_i38(tll_ptr n_v22106);
tll_ptr string_of_nat_i39(tll_ptr n_v22108);
tll_ptr digit_of_char_i40(tll_ptr c_v22112);
tll_ptr nat_of_string_loop_i41(tll_ptr s_v22114, tll_ptr acc_v22115);
tll_ptr nat_of_string_i42(tll_ptr s_v22122);
tll_ptr appendUU_i77(tll_ptr A_v22124, tll_ptr xs_v22125, tll_ptr ys_v22126);
tll_ptr appendUL_i76(tll_ptr A_v22135, tll_ptr xs_v22136, tll_ptr ys_v22137);
tll_ptr appendLL_i74(tll_ptr A_v22146, tll_ptr xs_v22147, tll_ptr ys_v22148);
tll_ptr idU_i85(tll_ptr A_v22157, tll_ptr x_v22158);
tll_ptr idL_i84(tll_ptr A_v22162, tll_ptr x_v22163);

tll_ptr addnclo_i97;
tll_ptr and_thenLLLclo_i113;
tll_ptr and_thenLULclo_i112;
tll_ptr and_thenULLclo_i111;
tll_ptr and_thenULUclo_i110;
tll_ptr and_thenUULclo_i109;
tll_ptr and_thenUUUclo_i108;
tll_ptr andbclo_i86;
tll_ptr appendLLclo_i119;
tll_ptr appendLLclo_i131;
tll_ptr appendULclo_i118;
tll_ptr appendULclo_i130;
tll_ptr appendUUclo_i117;
tll_ptr appendUUclo_i129;
tll_ptr catsclo_i104;
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
tll_ptr get_atclo_i123;
tll_ptr gtenclo_i91;
tll_ptr gtnclo_i93;
tll_ptr idLclo_i133;
tll_ptr idUclo_i132;
tll_ptr lenLLclo_i116;
tll_ptr lenULclo_i115;
tll_ptr lenUUclo_i114;
tll_ptr ls0_i47;
tll_ptr ls1_i48;
tll_ptr ls2_i49;
tll_ptr ltenclo_i90;
tll_ptr ltnclo_i92;
tll_ptr modnclo_i101;
tll_ptr mulnclo_i99;
tll_ptr nat_of_string_loopclo_i127;
tll_ptr nat_of_stringclo_i128;
tll_ptr notbclo_i88;
tll_ptr orbclo_i87;
tll_ptr predclo_i96;
tll_ptr prerrclo_i122;
tll_ptr printclo_i121;
tll_ptr readlineclo_i120;
tll_ptr string_of_digitclo_i124;
tll_ptr string_of_natclo_i125;
tll_ptr strlenclo_i105;
tll_ptr subnclo_i98;

tll_ptr andb_i2(tll_ptr b1_v21780, tll_ptr b2_v21781) {
  tll_ptr ifte_ret_t1;
  if (b1_v21780) {
    ifte_ret_t1 = b2_v21781;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v21784, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i2(env[0], b2_v21784);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v21782, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v21782);
  return lam_clo_t4;
}

tll_ptr orb_i3(tll_ptr b1_v21785, tll_ptr b2_v21786) {
  tll_ptr ifte_ret_t7;
  if (b1_v21785) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v21786;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v21789, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i3(env[0], b2_v21789);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v21787, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v21787);
  return lam_clo_t10;
}

tll_ptr notb_i4(tll_ptr b_v21790) {
  tll_ptr ifte_ret_t13;
  if (b_v21790) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v21791, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i4(b_v21791);
  return call_ret_t14;
}

tll_ptr compareb_i5(tll_ptr b1_v21792, tll_ptr b2_v21793) {
  tll_ptr EQ_t17; tll_ptr EQ_t21; tll_ptr GT_t18; tll_ptr LT_t20;
  tll_ptr ifte_ret_t19; tll_ptr ifte_ret_t22; tll_ptr ifte_ret_t23;
  if (b1_v21792) {
    if (b2_v21793) {
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
    if (b2_v21793) {
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

tll_ptr lam_fun_t25(tll_ptr b2_v21796, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = compareb_i5(env[0], b2_v21796);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr b1_v21794, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, b1_v21794);
  return lam_clo_t26;
}

tll_ptr lten_i6(tll_ptr x_v21797, tll_ptr y_v21798) {
  tll_ptr lten_ret_t29;
  instr_lten(&lten_ret_t29, x_v21797, y_v21798);
  return lten_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v21801, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = lten_i6(env[0], y_v21801);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v21799, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v21799);
  return lam_clo_t32;
}

tll_ptr gten_i7(tll_ptr x_v21802, tll_ptr y_v21803) {
  tll_ptr gten_ret_t35;
  instr_gten(&gten_ret_t35, x_v21802, y_v21803);
  return gten_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v21806, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = gten_i7(env[0], y_v21806);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v21804, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v21804);
  return lam_clo_t38;
}

tll_ptr ltn_i8(tll_ptr x_v21807, tll_ptr y_v21808) {
  tll_ptr ltn_ret_t41;
  instr_ltn(&ltn_ret_t41, x_v21807, y_v21808);
  return ltn_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v21811, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = ltn_i8(env[0], y_v21811);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v21809, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v21809);
  return lam_clo_t44;
}

tll_ptr gtn_i9(tll_ptr x_v21812, tll_ptr y_v21813) {
  tll_ptr gtn_ret_t47;
  instr_gtn(&gtn_ret_t47, x_v21812, y_v21813);
  return gtn_ret_t47;
}

tll_ptr lam_fun_t49(tll_ptr y_v21816, tll_env env) {
  tll_ptr call_ret_t48;
  call_ret_t48 = gtn_i9(env[0], y_v21816);
  return call_ret_t48;
}

tll_ptr lam_fun_t51(tll_ptr x_v21814, tll_env env) {
  tll_ptr lam_clo_t50;
  instr_clo(&lam_clo_t50, &lam_fun_t49, 1, x_v21814);
  return lam_clo_t50;
}

tll_ptr eqn_i10(tll_ptr x_v21817, tll_ptr y_v21818) {
  tll_ptr eqn_ret_t53;
  instr_eqn(&eqn_ret_t53, x_v21817, y_v21818);
  return eqn_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v21821, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = eqn_i10(env[0], y_v21821);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v21819, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v21819);
  return lam_clo_t56;
}

tll_ptr comparen_i11(tll_ptr n1_v21822, tll_ptr n2_v21823) {
  tll_ptr EQ_t65; tll_ptr GT_t62; tll_ptr LT_t64; tll_ptr add_ret_t60;
  tll_ptr add_ret_t61; tll_ptr call_ret_t59; tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t66; tll_ptr ifte_ret_t67;
  if (n1_v21822) {
    if (n2_v21823) {
      add_ret_t60 = n1_v21822 - 1;
      add_ret_t61 = n2_v21823 - 1;
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
    if (n2_v21823) {
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

tll_ptr lam_fun_t69(tll_ptr n2_v21826, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = comparen_i11(env[0], n2_v21826);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr n1_v21824, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, n1_v21824);
  return lam_clo_t70;
}

tll_ptr pred_i12(tll_ptr x_v21827) {
  tll_ptr add_ret_t73; tll_ptr ifte_ret_t74;
  if (x_v21827) {
    add_ret_t73 = x_v21827 - 1;
    ifte_ret_t74 = add_ret_t73;
  }
  else {
    ifte_ret_t74 = (tll_ptr)0;
  }
  return ifte_ret_t74;
}

tll_ptr lam_fun_t76(tll_ptr x_v21828, tll_env env) {
  tll_ptr call_ret_t75;
  call_ret_t75 = pred_i12(x_v21828);
  return call_ret_t75;
}

tll_ptr addn_i13(tll_ptr x_v21829, tll_ptr y_v21830) {
  tll_ptr addn_ret_t78;
  instr_addn(&addn_ret_t78, x_v21829, y_v21830);
  return addn_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v21833, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i13(env[0], y_v21833);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v21831, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v21831);
  return lam_clo_t81;
}

tll_ptr subn_i14(tll_ptr x_v21834, tll_ptr y_v21835) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v21835) {
    call_ret_t85 = pred_i12(x_v21834);
    add_ret_t86 = y_v21835 - 1;
    call_ret_t84 = subn_i14(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v21834;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v21838, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i14(env[0], y_v21838);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v21836, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v21836);
  return lam_clo_t90;
}

tll_ptr muln_i15(tll_ptr x_v21839, tll_ptr y_v21840) {
  tll_ptr muln_ret_t93;
  instr_muln(&muln_ret_t93, x_v21839, y_v21840);
  return muln_ret_t93;
}

tll_ptr lam_fun_t95(tll_ptr y_v21843, tll_env env) {
  tll_ptr call_ret_t94;
  call_ret_t94 = muln_i15(env[0], y_v21843);
  return call_ret_t94;
}

tll_ptr lam_fun_t97(tll_ptr x_v21841, tll_env env) {
  tll_ptr lam_clo_t96;
  instr_clo(&lam_clo_t96, &lam_fun_t95, 1, x_v21841);
  return lam_clo_t96;
}

tll_ptr divn_i16(tll_ptr x_v21844, tll_ptr y_v21845) {
  tll_ptr divn_ret_t99;
  instr_divn(&divn_ret_t99, x_v21844, y_v21845);
  return divn_ret_t99;
}

tll_ptr lam_fun_t101(tll_ptr y_v21848, tll_env env) {
  tll_ptr call_ret_t100;
  call_ret_t100 = divn_i16(env[0], y_v21848);
  return call_ret_t100;
}

tll_ptr lam_fun_t103(tll_ptr x_v21846, tll_env env) {
  tll_ptr lam_clo_t102;
  instr_clo(&lam_clo_t102, &lam_fun_t101, 1, x_v21846);
  return lam_clo_t102;
}

tll_ptr modn_i17(tll_ptr x_v21849, tll_ptr y_v21850) {
  tll_ptr modn_ret_t105;
  instr_modn(&modn_ret_t105, x_v21849, y_v21850);
  return modn_ret_t105;
}

tll_ptr lam_fun_t107(tll_ptr y_v21853, tll_env env) {
  tll_ptr call_ret_t106;
  call_ret_t106 = modn_i17(env[0], y_v21853);
  return call_ret_t106;
}

tll_ptr lam_fun_t109(tll_ptr x_v21851, tll_env env) {
  tll_ptr lam_clo_t108;
  instr_clo(&lam_clo_t108, &lam_fun_t107, 1, x_v21851);
  return lam_clo_t108;
}

tll_ptr eqc_i18(tll_ptr c1_v21854, tll_ptr c2_v21855) {
  tll_ptr call_ret_t113; tll_ptr n1_v21856; tll_ptr n2_v21857;
  tll_ptr switch_ret_t111; tll_ptr switch_ret_t112;
  switch(((tll_node)c1_v21854)->tag) {
    case 5:
      n1_v21856 = ((tll_node)c1_v21854)->data[0];
      switch(((tll_node)c2_v21855)->tag) {
        case 5:
          n2_v21857 = ((tll_node)c2_v21855)->data[0];
          call_ret_t113 = eqn_i10(n1_v21856, n2_v21857);
          switch_ret_t112 = call_ret_t113;
          break;
      }
      switch_ret_t111 = switch_ret_t112;
      break;
  }
  return switch_ret_t111;
}

tll_ptr lam_fun_t115(tll_ptr c2_v21860, tll_env env) {
  tll_ptr call_ret_t114;
  call_ret_t114 = eqc_i18(env[0], c2_v21860);
  return call_ret_t114;
}

tll_ptr lam_fun_t117(tll_ptr c1_v21858, tll_env env) {
  tll_ptr lam_clo_t116;
  instr_clo(&lam_clo_t116, &lam_fun_t115, 1, c1_v21858);
  return lam_clo_t116;
}

tll_ptr comparec_i19(tll_ptr c1_v21861, tll_ptr c2_v21862) {
  tll_ptr call_ret_t121; tll_ptr n1_v21863; tll_ptr n2_v21864;
  tll_ptr switch_ret_t119; tll_ptr switch_ret_t120;
  switch(((tll_node)c1_v21861)->tag) {
    case 5:
      n1_v21863 = ((tll_node)c1_v21861)->data[0];
      switch(((tll_node)c2_v21862)->tag) {
        case 5:
          n2_v21864 = ((tll_node)c2_v21862)->data[0];
          call_ret_t121 = comparen_i11(n1_v21863, n2_v21864);
          switch_ret_t120 = call_ret_t121;
          break;
      }
      switch_ret_t119 = switch_ret_t120;
      break;
  }
  return switch_ret_t119;
}

tll_ptr lam_fun_t123(tll_ptr c2_v21867, tll_env env) {
  tll_ptr call_ret_t122;
  call_ret_t122 = comparec_i19(env[0], c2_v21867);
  return call_ret_t122;
}

tll_ptr lam_fun_t125(tll_ptr c1_v21865, tll_env env) {
  tll_ptr lam_clo_t124;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 1, c1_v21865);
  return lam_clo_t124;
}

tll_ptr cats_i20(tll_ptr s1_v21868, tll_ptr s2_v21869) {
  tll_ptr String_t129; tll_ptr c_v21870; tll_ptr call_ret_t128;
  tll_ptr s1_v21871; tll_ptr switch_ret_t127;
  switch(((tll_node)s1_v21868)->tag) {
    case 6:
      switch_ret_t127 = s2_v21869;
      break;
    case 7:
      c_v21870 = ((tll_node)s1_v21868)->data[0];
      s1_v21871 = ((tll_node)s1_v21868)->data[1];
      call_ret_t128 = cats_i20(s1_v21871, s2_v21869);
      instr_struct(&String_t129, 7, 2, c_v21870, call_ret_t128);
      switch_ret_t127 = String_t129;
      break;
  }
  return switch_ret_t127;
}

tll_ptr lam_fun_t131(tll_ptr s2_v21874, tll_env env) {
  tll_ptr call_ret_t130;
  call_ret_t130 = cats_i20(env[0], s2_v21874);
  return call_ret_t130;
}

tll_ptr lam_fun_t133(tll_ptr s1_v21872, tll_env env) {
  tll_ptr lam_clo_t132;
  instr_clo(&lam_clo_t132, &lam_fun_t131, 1, s1_v21872);
  return lam_clo_t132;
}

tll_ptr strlen_i21(tll_ptr s_v21875) {
  tll_ptr __v21876; tll_ptr add_ret_t137; tll_ptr call_ret_t136;
  tll_ptr s_v21877; tll_ptr switch_ret_t135;
  switch(((tll_node)s_v21875)->tag) {
    case 6:
      switch_ret_t135 = (tll_ptr)0;
      break;
    case 7:
      __v21876 = ((tll_node)s_v21875)->data[0];
      s_v21877 = ((tll_node)s_v21875)->data[1];
      call_ret_t136 = strlen_i21(s_v21877);
      add_ret_t137 = call_ret_t136 + 1;
      switch_ret_t135 = add_ret_t137;
      break;
  }
  return switch_ret_t135;
}

tll_ptr lam_fun_t139(tll_ptr s_v21878, tll_env env) {
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i21(s_v21878);
  return call_ret_t138;
}

tll_ptr eqs_i22(tll_ptr s1_v21879, tll_ptr s2_v21880) {
  tll_ptr __v21881; tll_ptr __v21882; tll_ptr c1_v21883; tll_ptr c2_v21885;
  tll_ptr call_ret_t144; tll_ptr call_ret_t145; tll_ptr call_ret_t146;
  tll_ptr s1_v21884; tll_ptr s2_v21886; tll_ptr switch_ret_t141;
  tll_ptr switch_ret_t142; tll_ptr switch_ret_t143;
  switch(((tll_node)s1_v21879)->tag) {
    case 6:
      switch(((tll_node)s2_v21880)->tag) {
        case 6:
          switch_ret_t142 = (tll_ptr)1;
          break;
        case 7:
          __v21881 = ((tll_node)s2_v21880)->data[0];
          __v21882 = ((tll_node)s2_v21880)->data[1];
          switch_ret_t142 = (tll_ptr)0;
          break;
      }
      switch_ret_t141 = switch_ret_t142;
      break;
    case 7:
      c1_v21883 = ((tll_node)s1_v21879)->data[0];
      s1_v21884 = ((tll_node)s1_v21879)->data[1];
      switch(((tll_node)s2_v21880)->tag) {
        case 6:
          switch_ret_t143 = (tll_ptr)0;
          break;
        case 7:
          c2_v21885 = ((tll_node)s2_v21880)->data[0];
          s2_v21886 = ((tll_node)s2_v21880)->data[1];
          call_ret_t145 = eqc_i18(c1_v21883, c2_v21885);
          call_ret_t146 = eqs_i22(s1_v21884, s2_v21886);
          call_ret_t144 = andb_i2(call_ret_t145, call_ret_t146);
          switch_ret_t143 = call_ret_t144;
          break;
      }
      switch_ret_t141 = switch_ret_t143;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t148(tll_ptr s2_v21889, tll_env env) {
  tll_ptr call_ret_t147;
  call_ret_t147 = eqs_i22(env[0], s2_v21889);
  return call_ret_t147;
}

tll_ptr lam_fun_t150(tll_ptr s1_v21887, tll_env env) {
  tll_ptr lam_clo_t149;
  instr_clo(&lam_clo_t149, &lam_fun_t148, 1, s1_v21887);
  return lam_clo_t149;
}

tll_ptr compares_i23(tll_ptr s1_v21890, tll_ptr s2_v21891) {
  tll_ptr EQ_t154; tll_ptr GT_t157; tll_ptr GT_t162; tll_ptr LT_t155;
  tll_ptr LT_t161; tll_ptr __v21892; tll_ptr __v21893; tll_ptr c1_v21894;
  tll_ptr c2_v21896; tll_ptr call_ret_t158; tll_ptr call_ret_t160;
  tll_ptr s1_v21895; tll_ptr s2_v21897; tll_ptr switch_ret_t152;
  tll_ptr switch_ret_t153; tll_ptr switch_ret_t156; tll_ptr switch_ret_t159;
  switch(((tll_node)s1_v21890)->tag) {
    case 6:
      switch(((tll_node)s2_v21891)->tag) {
        case 6:
          instr_struct(&EQ_t154, 3, 0);
          switch_ret_t153 = EQ_t154;
          break;
        case 7:
          __v21892 = ((tll_node)s2_v21891)->data[0];
          __v21893 = ((tll_node)s2_v21891)->data[1];
          instr_struct(&LT_t155, 1, 0);
          switch_ret_t153 = LT_t155;
          break;
      }
      switch_ret_t152 = switch_ret_t153;
      break;
    case 7:
      c1_v21894 = ((tll_node)s1_v21890)->data[0];
      s1_v21895 = ((tll_node)s1_v21890)->data[1];
      switch(((tll_node)s2_v21891)->tag) {
        case 6:
          instr_struct(&GT_t157, 2, 0);
          switch_ret_t156 = GT_t157;
          break;
        case 7:
          c2_v21896 = ((tll_node)s2_v21891)->data[0];
          s2_v21897 = ((tll_node)s2_v21891)->data[1];
          call_ret_t158 = comparec_i19(c1_v21894, c2_v21896);
          switch(((tll_node)call_ret_t158)->tag) {
            case 3:
              call_ret_t160 = compares_i23(s1_v21895, s2_v21897);
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

tll_ptr lam_fun_t164(tll_ptr s2_v21900, tll_env env) {
  tll_ptr call_ret_t163;
  call_ret_t163 = compares_i23(env[0], s2_v21900);
  return call_ret_t163;
}

tll_ptr lam_fun_t166(tll_ptr s1_v21898, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, s1_v21898);
  return lam_clo_t165;
}

tll_ptr and_thenUUU_i61(tll_ptr A_v21901, tll_ptr B_v21902, tll_ptr opt_v21903, tll_ptr f_v21904) {
  tll_ptr NoneUU_t169; tll_ptr app_ret_t170; tll_ptr switch_ret_t168;
  tll_ptr x_v21905;
  switch(((tll_node)opt_v21903)->tag) {
    case 20:
      instr_struct(&NoneUU_t169, 20, 0);
      switch_ret_t168 = NoneUU_t169;
      break;
    case 21:
      x_v21905 = ((tll_node)opt_v21903)->data[0];
      instr_app(&app_ret_t170, f_v21904, x_v21905);
      switch_ret_t168 = app_ret_t170;
      break;
  }
  return switch_ret_t168;
}

tll_ptr lam_fun_t172(tll_ptr f_v21915, tll_env env) {
  tll_ptr call_ret_t171;
  call_ret_t171 = and_thenUUU_i61(env[2], env[1], env[0], f_v21915);
  return call_ret_t171;
}

tll_ptr lam_fun_t174(tll_ptr opt_v21913, tll_env env) {
  tll_ptr lam_clo_t173;
  instr_clo(&lam_clo_t173, &lam_fun_t172, 3, opt_v21913, env[0], env[1]);
  return lam_clo_t173;
}

tll_ptr lam_fun_t176(tll_ptr B_v21910, tll_env env) {
  tll_ptr lam_clo_t175;
  instr_clo(&lam_clo_t175, &lam_fun_t174, 2, B_v21910, env[0]);
  return lam_clo_t175;
}

tll_ptr lam_fun_t178(tll_ptr A_v21906, tll_env env) {
  tll_ptr lam_clo_t177;
  instr_clo(&lam_clo_t177, &lam_fun_t176, 1, A_v21906);
  return lam_clo_t177;
}

tll_ptr and_thenUUL_i60(tll_ptr A_v21916, tll_ptr B_v21917, tll_ptr opt_v21918, tll_ptr f_v21919) {
  tll_ptr NoneUL_t181; tll_ptr app_ret_t182; tll_ptr switch_ret_t180;
  tll_ptr x_v21920;
  switch(((tll_node)opt_v21918)->tag) {
    case 18:
      instr_free_struct(opt_v21918);
      instr_struct(&NoneUL_t181, 18, 0);
      switch_ret_t180 = NoneUL_t181;
      break;
    case 19:
      x_v21920 = ((tll_node)opt_v21918)->data[0];
      instr_free_struct(opt_v21918);
      instr_app(&app_ret_t182, f_v21919, x_v21920);
      switch_ret_t180 = app_ret_t182;
      break;
  }
  return switch_ret_t180;
}

tll_ptr lam_fun_t184(tll_ptr f_v21930, tll_env env) {
  tll_ptr call_ret_t183;
  call_ret_t183 = and_thenUUL_i60(env[2], env[1], env[0], f_v21930);
  return call_ret_t183;
}

tll_ptr lam_fun_t186(tll_ptr opt_v21928, tll_env env) {
  tll_ptr lam_clo_t185;
  instr_clo(&lam_clo_t185, &lam_fun_t184, 3, opt_v21928, env[0], env[1]);
  return lam_clo_t185;
}

tll_ptr lam_fun_t188(tll_ptr B_v21925, tll_env env) {
  tll_ptr lam_clo_t187;
  instr_clo(&lam_clo_t187, &lam_fun_t186, 2, B_v21925, env[0]);
  return lam_clo_t187;
}

tll_ptr lam_fun_t190(tll_ptr A_v21921, tll_env env) {
  tll_ptr lam_clo_t189;
  instr_clo(&lam_clo_t189, &lam_fun_t188, 1, A_v21921);
  return lam_clo_t189;
}

tll_ptr and_thenULU_i59(tll_ptr A_v21931, tll_ptr B_v21932, tll_ptr opt_v21933, tll_ptr f_v21934) {
  tll_ptr NoneLU_t193; tll_ptr app_ret_t194; tll_ptr switch_ret_t192;
  tll_ptr x_v21935;
  switch(((tll_node)opt_v21933)->tag) {
    case 20:
      instr_struct(&NoneLU_t193, 16, 0);
      switch_ret_t192 = NoneLU_t193;
      break;
    case 21:
      x_v21935 = ((tll_node)opt_v21933)->data[0];
      instr_app(&app_ret_t194, f_v21934, x_v21935);
      switch_ret_t192 = app_ret_t194;
      break;
  }
  return switch_ret_t192;
}

tll_ptr lam_fun_t196(tll_ptr f_v21945, tll_env env) {
  tll_ptr call_ret_t195;
  call_ret_t195 = and_thenULU_i59(env[2], env[1], env[0], f_v21945);
  return call_ret_t195;
}

tll_ptr lam_fun_t198(tll_ptr opt_v21943, tll_env env) {
  tll_ptr lam_clo_t197;
  instr_clo(&lam_clo_t197, &lam_fun_t196, 3, opt_v21943, env[0], env[1]);
  return lam_clo_t197;
}

tll_ptr lam_fun_t200(tll_ptr B_v21940, tll_env env) {
  tll_ptr lam_clo_t199;
  instr_clo(&lam_clo_t199, &lam_fun_t198, 2, B_v21940, env[0]);
  return lam_clo_t199;
}

tll_ptr lam_fun_t202(tll_ptr A_v21936, tll_env env) {
  tll_ptr lam_clo_t201;
  instr_clo(&lam_clo_t201, &lam_fun_t200, 1, A_v21936);
  return lam_clo_t201;
}

tll_ptr and_thenULL_i58(tll_ptr A_v21946, tll_ptr B_v21947, tll_ptr opt_v21948, tll_ptr f_v21949) {
  tll_ptr NoneLL_t205; tll_ptr app_ret_t206; tll_ptr switch_ret_t204;
  tll_ptr x_v21950;
  switch(((tll_node)opt_v21948)->tag) {
    case 18:
      instr_free_struct(opt_v21948);
      instr_struct(&NoneLL_t205, 14, 0);
      switch_ret_t204 = NoneLL_t205;
      break;
    case 19:
      x_v21950 = ((tll_node)opt_v21948)->data[0];
      instr_free_struct(opt_v21948);
      instr_app(&app_ret_t206, f_v21949, x_v21950);
      switch_ret_t204 = app_ret_t206;
      break;
  }
  return switch_ret_t204;
}

tll_ptr lam_fun_t208(tll_ptr f_v21960, tll_env env) {
  tll_ptr call_ret_t207;
  call_ret_t207 = and_thenULL_i58(env[2], env[1], env[0], f_v21960);
  return call_ret_t207;
}

tll_ptr lam_fun_t210(tll_ptr opt_v21958, tll_env env) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 3, opt_v21958, env[0], env[1]);
  return lam_clo_t209;
}

tll_ptr lam_fun_t212(tll_ptr B_v21955, tll_env env) {
  tll_ptr lam_clo_t211;
  instr_clo(&lam_clo_t211, &lam_fun_t210, 2, B_v21955, env[0]);
  return lam_clo_t211;
}

tll_ptr lam_fun_t214(tll_ptr A_v21951, tll_env env) {
  tll_ptr lam_clo_t213;
  instr_clo(&lam_clo_t213, &lam_fun_t212, 1, A_v21951);
  return lam_clo_t213;
}

tll_ptr and_thenLUL_i56(tll_ptr A_v21961, tll_ptr B_v21962, tll_ptr opt_v21963, tll_ptr f_v21964) {
  tll_ptr NoneUL_t217; tll_ptr app_ret_t218; tll_ptr switch_ret_t216;
  tll_ptr x_v21965;
  switch(((tll_node)opt_v21963)->tag) {
    case 14:
      instr_free_struct(opt_v21963);
      instr_struct(&NoneUL_t217, 18, 0);
      switch_ret_t216 = NoneUL_t217;
      break;
    case 15:
      x_v21965 = ((tll_node)opt_v21963)->data[0];
      instr_free_struct(opt_v21963);
      instr_app(&app_ret_t218, f_v21964, x_v21965);
      switch_ret_t216 = app_ret_t218;
      break;
  }
  return switch_ret_t216;
}

tll_ptr lam_fun_t220(tll_ptr f_v21975, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = and_thenLUL_i56(env[2], env[1], env[0], f_v21975);
  return call_ret_t219;
}

tll_ptr lam_fun_t222(tll_ptr opt_v21973, tll_env env) {
  tll_ptr lam_clo_t221;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 3, opt_v21973, env[0], env[1]);
  return lam_clo_t221;
}

tll_ptr lam_fun_t224(tll_ptr B_v21970, tll_env env) {
  tll_ptr lam_clo_t223;
  instr_clo(&lam_clo_t223, &lam_fun_t222, 2, B_v21970, env[0]);
  return lam_clo_t223;
}

tll_ptr lam_fun_t226(tll_ptr A_v21966, tll_env env) {
  tll_ptr lam_clo_t225;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 1, A_v21966);
  return lam_clo_t225;
}

tll_ptr and_thenLLL_i54(tll_ptr A_v21976, tll_ptr B_v21977, tll_ptr opt_v21978, tll_ptr f_v21979) {
  tll_ptr NoneLL_t229; tll_ptr app_ret_t230; tll_ptr switch_ret_t228;
  tll_ptr x_v21980;
  switch(((tll_node)opt_v21978)->tag) {
    case 14:
      instr_free_struct(opt_v21978);
      instr_struct(&NoneLL_t229, 14, 0);
      switch_ret_t228 = NoneLL_t229;
      break;
    case 15:
      x_v21980 = ((tll_node)opt_v21978)->data[0];
      instr_free_struct(opt_v21978);
      instr_app(&app_ret_t230, f_v21979, x_v21980);
      switch_ret_t228 = app_ret_t230;
      break;
  }
  return switch_ret_t228;
}

tll_ptr lam_fun_t232(tll_ptr f_v21990, tll_env env) {
  tll_ptr call_ret_t231;
  call_ret_t231 = and_thenLLL_i54(env[2], env[1], env[0], f_v21990);
  return call_ret_t231;
}

tll_ptr lam_fun_t234(tll_ptr opt_v21988, tll_env env) {
  tll_ptr lam_clo_t233;
  instr_clo(&lam_clo_t233, &lam_fun_t232, 3, opt_v21988, env[0], env[1]);
  return lam_clo_t233;
}

tll_ptr lam_fun_t236(tll_ptr B_v21985, tll_env env) {
  tll_ptr lam_clo_t235;
  instr_clo(&lam_clo_t235, &lam_fun_t234, 2, B_v21985, env[0]);
  return lam_clo_t235;
}

tll_ptr lam_fun_t238(tll_ptr A_v21981, tll_env env) {
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, A_v21981);
  return lam_clo_t237;
}

tll_ptr lenUU_i65(tll_ptr A_v21991, tll_ptr xs_v21992) {
  tll_ptr add_ret_t245; tll_ptr call_ret_t243; tll_ptr consUU_t246;
  tll_ptr n_v21995; tll_ptr nilUU_t241; tll_ptr pair_struct_t242;
  tll_ptr pair_struct_t247; tll_ptr switch_ret_t240; tll_ptr switch_ret_t244;
  tll_ptr x_v21993; tll_ptr xs_v21994; tll_ptr xs_v21996;
  switch(((tll_node)xs_v21992)->tag) {
    case 28:
      instr_struct(&nilUU_t241, 28, 0);
      instr_struct(&pair_struct_t242, 0, 2, (tll_ptr)0, nilUU_t241);
      switch_ret_t240 = pair_struct_t242;
      break;
    case 29:
      x_v21993 = ((tll_node)xs_v21992)->data[0];
      xs_v21994 = ((tll_node)xs_v21992)->data[1];
      call_ret_t243 = lenUU_i65(0, xs_v21994);
      switch(((tll_node)call_ret_t243)->tag) {
        case 0:
          n_v21995 = ((tll_node)call_ret_t243)->data[0];
          xs_v21996 = ((tll_node)call_ret_t243)->data[1];
          instr_free_struct(call_ret_t243);
          add_ret_t245 = n_v21995 + 1;
          instr_struct(&consUU_t246, 29, 2, x_v21993, xs_v21996);
          instr_struct(&pair_struct_t247, 0, 2, add_ret_t245, consUU_t246);
          switch_ret_t244 = pair_struct_t247;
          break;
      }
      switch_ret_t240 = switch_ret_t244;
      break;
  }
  return switch_ret_t240;
}

tll_ptr lam_fun_t249(tll_ptr xs_v21999, tll_env env) {
  tll_ptr call_ret_t248;
  call_ret_t248 = lenUU_i65(env[0], xs_v21999);
  return call_ret_t248;
}

tll_ptr lam_fun_t251(tll_ptr A_v21997, tll_env env) {
  tll_ptr lam_clo_t250;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 1, A_v21997);
  return lam_clo_t250;
}

tll_ptr lenUL_i64(tll_ptr A_v22000, tll_ptr xs_v22001) {
  tll_ptr add_ret_t258; tll_ptr call_ret_t256; tll_ptr consUL_t259;
  tll_ptr n_v22004; tll_ptr nilUL_t254; tll_ptr pair_struct_t255;
  tll_ptr pair_struct_t260; tll_ptr switch_ret_t253; tll_ptr switch_ret_t257;
  tll_ptr x_v22002; tll_ptr xs_v22003; tll_ptr xs_v22005;
  switch(((tll_node)xs_v22001)->tag) {
    case 26:
      instr_free_struct(xs_v22001);
      instr_struct(&nilUL_t254, 26, 0);
      instr_struct(&pair_struct_t255, 0, 2, (tll_ptr)0, nilUL_t254);
      switch_ret_t253 = pair_struct_t255;
      break;
    case 27:
      x_v22002 = ((tll_node)xs_v22001)->data[0];
      xs_v22003 = ((tll_node)xs_v22001)->data[1];
      instr_free_struct(xs_v22001);
      call_ret_t256 = lenUL_i64(0, xs_v22003);
      switch(((tll_node)call_ret_t256)->tag) {
        case 0:
          n_v22004 = ((tll_node)call_ret_t256)->data[0];
          xs_v22005 = ((tll_node)call_ret_t256)->data[1];
          instr_free_struct(call_ret_t256);
          add_ret_t258 = n_v22004 + 1;
          instr_struct(&consUL_t259, 27, 2, x_v22002, xs_v22005);
          instr_struct(&pair_struct_t260, 0, 2, add_ret_t258, consUL_t259);
          switch_ret_t257 = pair_struct_t260;
          break;
      }
      switch_ret_t253 = switch_ret_t257;
      break;
  }
  return switch_ret_t253;
}

tll_ptr lam_fun_t262(tll_ptr xs_v22008, tll_env env) {
  tll_ptr call_ret_t261;
  call_ret_t261 = lenUL_i64(env[0], xs_v22008);
  return call_ret_t261;
}

tll_ptr lam_fun_t264(tll_ptr A_v22006, tll_env env) {
  tll_ptr lam_clo_t263;
  instr_clo(&lam_clo_t263, &lam_fun_t262, 1, A_v22006);
  return lam_clo_t263;
}

tll_ptr lenLL_i62(tll_ptr A_v22009, tll_ptr xs_v22010) {
  tll_ptr add_ret_t271; tll_ptr call_ret_t269; tll_ptr consLL_t272;
  tll_ptr n_v22013; tll_ptr nilLL_t267; tll_ptr pair_struct_t268;
  tll_ptr pair_struct_t273; tll_ptr switch_ret_t266; tll_ptr switch_ret_t270;
  tll_ptr x_v22011; tll_ptr xs_v22012; tll_ptr xs_v22014;
  switch(((tll_node)xs_v22010)->tag) {
    case 22:
      instr_free_struct(xs_v22010);
      instr_struct(&nilLL_t267, 22, 0);
      instr_struct(&pair_struct_t268, 0, 2, (tll_ptr)0, nilLL_t267);
      switch_ret_t266 = pair_struct_t268;
      break;
    case 23:
      x_v22011 = ((tll_node)xs_v22010)->data[0];
      xs_v22012 = ((tll_node)xs_v22010)->data[1];
      instr_free_struct(xs_v22010);
      call_ret_t269 = lenLL_i62(0, xs_v22012);
      switch(((tll_node)call_ret_t269)->tag) {
        case 0:
          n_v22013 = ((tll_node)call_ret_t269)->data[0];
          xs_v22014 = ((tll_node)call_ret_t269)->data[1];
          instr_free_struct(call_ret_t269);
          add_ret_t271 = n_v22013 + 1;
          instr_struct(&consLL_t272, 23, 2, x_v22011, xs_v22014);
          instr_struct(&pair_struct_t273, 0, 2, add_ret_t271, consLL_t272);
          switch_ret_t270 = pair_struct_t273;
          break;
      }
      switch_ret_t266 = switch_ret_t270;
      break;
  }
  return switch_ret_t266;
}

tll_ptr lam_fun_t275(tll_ptr xs_v22017, tll_env env) {
  tll_ptr call_ret_t274;
  call_ret_t274 = lenLL_i62(env[0], xs_v22017);
  return call_ret_t274;
}

tll_ptr lam_fun_t277(tll_ptr A_v22015, tll_env env) {
  tll_ptr lam_clo_t276;
  instr_clo(&lam_clo_t276, &lam_fun_t275, 1, A_v22015);
  return lam_clo_t276;
}

tll_ptr appendUU_i69(tll_ptr A_v22018, tll_ptr xs_v22019, tll_ptr ys_v22020) {
  tll_ptr call_ret_t280; tll_ptr consUU_t281; tll_ptr switch_ret_t279;
  tll_ptr x_v22021; tll_ptr xs_v22022;
  switch(((tll_node)xs_v22019)->tag) {
    case 28:
      switch_ret_t279 = ys_v22020;
      break;
    case 29:
      x_v22021 = ((tll_node)xs_v22019)->data[0];
      xs_v22022 = ((tll_node)xs_v22019)->data[1];
      call_ret_t280 = appendUU_i69(0, xs_v22022, ys_v22020);
      instr_struct(&consUU_t281, 29, 2, x_v22021, call_ret_t280);
      switch_ret_t279 = consUU_t281;
      break;
  }
  return switch_ret_t279;
}

tll_ptr lam_fun_t283(tll_ptr ys_v22028, tll_env env) {
  tll_ptr call_ret_t282;
  call_ret_t282 = appendUU_i69(env[1], env[0], ys_v22028);
  return call_ret_t282;
}

tll_ptr lam_fun_t285(tll_ptr xs_v22026, tll_env env) {
  tll_ptr lam_clo_t284;
  instr_clo(&lam_clo_t284, &lam_fun_t283, 2, xs_v22026, env[0]);
  return lam_clo_t284;
}

tll_ptr lam_fun_t287(tll_ptr A_v22023, tll_env env) {
  tll_ptr lam_clo_t286;
  instr_clo(&lam_clo_t286, &lam_fun_t285, 1, A_v22023);
  return lam_clo_t286;
}

tll_ptr appendUL_i68(tll_ptr A_v22029, tll_ptr xs_v22030, tll_ptr ys_v22031) {
  tll_ptr call_ret_t290; tll_ptr consUL_t291; tll_ptr switch_ret_t289;
  tll_ptr x_v22032; tll_ptr xs_v22033;
  switch(((tll_node)xs_v22030)->tag) {
    case 26:
      instr_free_struct(xs_v22030);
      switch_ret_t289 = ys_v22031;
      break;
    case 27:
      x_v22032 = ((tll_node)xs_v22030)->data[0];
      xs_v22033 = ((tll_node)xs_v22030)->data[1];
      instr_free_struct(xs_v22030);
      call_ret_t290 = appendUL_i68(0, xs_v22033, ys_v22031);
      instr_struct(&consUL_t291, 27, 2, x_v22032, call_ret_t290);
      switch_ret_t289 = consUL_t291;
      break;
  }
  return switch_ret_t289;
}

tll_ptr lam_fun_t293(tll_ptr ys_v22039, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = appendUL_i68(env[1], env[0], ys_v22039);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v22037, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 2, xs_v22037, env[0]);
  return lam_clo_t294;
}

tll_ptr lam_fun_t297(tll_ptr A_v22034, tll_env env) {
  tll_ptr lam_clo_t296;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 1, A_v22034);
  return lam_clo_t296;
}

tll_ptr appendLL_i66(tll_ptr A_v22040, tll_ptr xs_v22041, tll_ptr ys_v22042) {
  tll_ptr call_ret_t300; tll_ptr consLL_t301; tll_ptr switch_ret_t299;
  tll_ptr x_v22043; tll_ptr xs_v22044;
  switch(((tll_node)xs_v22041)->tag) {
    case 22:
      instr_free_struct(xs_v22041);
      switch_ret_t299 = ys_v22042;
      break;
    case 23:
      x_v22043 = ((tll_node)xs_v22041)->data[0];
      xs_v22044 = ((tll_node)xs_v22041)->data[1];
      instr_free_struct(xs_v22041);
      call_ret_t300 = appendLL_i66(0, xs_v22044, ys_v22042);
      instr_struct(&consLL_t301, 23, 2, x_v22043, call_ret_t300);
      switch_ret_t299 = consLL_t301;
      break;
  }
  return switch_ret_t299;
}

tll_ptr lam_fun_t303(tll_ptr ys_v22050, tll_env env) {
  tll_ptr call_ret_t302;
  call_ret_t302 = appendLL_i66(env[1], env[0], ys_v22050);
  return call_ret_t302;
}

tll_ptr lam_fun_t305(tll_ptr xs_v22048, tll_env env) {
  tll_ptr lam_clo_t304;
  instr_clo(&lam_clo_t304, &lam_fun_t303, 2, xs_v22048, env[0]);
  return lam_clo_t304;
}

tll_ptr lam_fun_t307(tll_ptr A_v22045, tll_env env) {
  tll_ptr lam_clo_t306;
  instr_clo(&lam_clo_t306, &lam_fun_t305, 1, A_v22045);
  return lam_clo_t306;
}

tll_ptr lam_fun_t314(tll_ptr __v22052, tll_env env) {
  tll_ptr __v22061; tll_ptr ch_v22059; tll_ptr ch_v22060; tll_ptr ch_v22063;
  tll_ptr ch_v22064; tll_ptr prim_ch_t309; tll_ptr recv_msg_t311;
  tll_ptr s_v22062; tll_ptr send_ch_t310; tll_ptr send_ch_t313;
  tll_ptr switch_ret_t312;
  instr_open(&prim_ch_t309, &proc_stdin);
  ch_v22059 = prim_ch_t309;
  instr_send(&send_ch_t310, ch_v22059, (tll_ptr)1);
  ch_v22060 = send_ch_t310;
  instr_recv(&recv_msg_t311, ch_v22060);
  __v22061 = recv_msg_t311;
  switch(((tll_node)__v22061)->tag) {
    case 0:
      s_v22062 = ((tll_node)__v22061)->data[0];
      ch_v22063 = ((tll_node)__v22061)->data[1];
      instr_free_struct(__v22061);
      instr_send(&send_ch_t313, ch_v22063, (tll_ptr)0);
      ch_v22064 = send_ch_t313;
      switch_ret_t312 = s_v22062;
      break;
  }
  return switch_ret_t312;
}

tll_ptr readline_i33(tll_ptr __v22051) {
  tll_ptr lam_clo_t315;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 0);
  return lam_clo_t315;
}

tll_ptr lam_fun_t317(tll_ptr __v22065, tll_env env) {
  tll_ptr call_ret_t316;
  call_ret_t316 = readline_i33(__v22065);
  return call_ret_t316;
}

tll_ptr lam_fun_t323(tll_ptr __v22067, tll_env env) {
  tll_ptr ch_v22072; tll_ptr ch_v22073; tll_ptr ch_v22074; tll_ptr ch_v22075;
  tll_ptr prim_ch_t319; tll_ptr send_ch_t320; tll_ptr send_ch_t321;
  tll_ptr send_ch_t322;
  instr_open(&prim_ch_t319, &proc_stdout);
  ch_v22072 = prim_ch_t319;
  instr_send(&send_ch_t320, ch_v22072, (tll_ptr)1);
  ch_v22073 = send_ch_t320;
  instr_send(&send_ch_t321, ch_v22073, env[0]);
  ch_v22074 = send_ch_t321;
  instr_send(&send_ch_t322, ch_v22074, (tll_ptr)0);
  ch_v22075 = send_ch_t322;
  return 0;
}

tll_ptr print_i34(tll_ptr s_v22066) {
  tll_ptr lam_clo_t324;
  instr_clo(&lam_clo_t324, &lam_fun_t323, 1, s_v22066);
  return lam_clo_t324;
}

tll_ptr lam_fun_t326(tll_ptr s_v22076, tll_env env) {
  tll_ptr call_ret_t325;
  call_ret_t325 = print_i34(s_v22076);
  return call_ret_t325;
}

tll_ptr lam_fun_t332(tll_ptr __v22078, tll_env env) {
  tll_ptr ch_v22083; tll_ptr ch_v22084; tll_ptr ch_v22085; tll_ptr ch_v22086;
  tll_ptr prim_ch_t328; tll_ptr send_ch_t329; tll_ptr send_ch_t330;
  tll_ptr send_ch_t331;
  instr_open(&prim_ch_t328, &proc_stderr);
  ch_v22083 = prim_ch_t328;
  instr_send(&send_ch_t329, ch_v22083, (tll_ptr)1);
  ch_v22084 = send_ch_t329;
  instr_send(&send_ch_t330, ch_v22084, env[0]);
  ch_v22085 = send_ch_t330;
  instr_send(&send_ch_t331, ch_v22085, (tll_ptr)0);
  ch_v22086 = send_ch_t331;
  return 0;
}

tll_ptr prerr_i35(tll_ptr s_v22077) {
  tll_ptr lam_clo_t333;
  instr_clo(&lam_clo_t333, &lam_fun_t332, 1, s_v22077);
  return lam_clo_t333;
}

tll_ptr lam_fun_t335(tll_ptr s_v22087, tll_env env) {
  tll_ptr call_ret_t334;
  call_ret_t334 = prerr_i35(s_v22087);
  return call_ret_t334;
}

tll_ptr get_at_i37(tll_ptr A_v22088, tll_ptr n_v22089, tll_ptr xs_v22090, tll_ptr a_v22091) {
  tll_ptr __v22092; tll_ptr __v22095; tll_ptr add_ret_t380;
  tll_ptr call_ret_t379; tll_ptr ifte_ret_t382; tll_ptr switch_ret_t378;
  tll_ptr switch_ret_t381; tll_ptr x_v22094; tll_ptr xs_v22093;
  if (n_v22089) {
    switch(((tll_node)xs_v22090)->tag) {
      case 28:
        switch_ret_t378 = a_v22091;
        break;
      case 29:
        __v22092 = ((tll_node)xs_v22090)->data[0];
        xs_v22093 = ((tll_node)xs_v22090)->data[1];
        add_ret_t380 = n_v22089 - 1;
        call_ret_t379 = get_at_i37(0, add_ret_t380, xs_v22093, a_v22091);
        switch_ret_t378 = call_ret_t379;
        break;
    }
    ifte_ret_t382 = switch_ret_t378;
  }
  else {
    switch(((tll_node)xs_v22090)->tag) {
      case 28:
        switch_ret_t381 = a_v22091;
        break;
      case 29:
        x_v22094 = ((tll_node)xs_v22090)->data[0];
        __v22095 = ((tll_node)xs_v22090)->data[1];
        switch_ret_t381 = x_v22094;
        break;
    }
    ifte_ret_t382 = switch_ret_t381;
  }
  return ifte_ret_t382;
}

tll_ptr lam_fun_t384(tll_ptr a_v22105, tll_env env) {
  tll_ptr call_ret_t383;
  call_ret_t383 = get_at_i37(env[2], env[1], env[0], a_v22105);
  return call_ret_t383;
}

tll_ptr lam_fun_t386(tll_ptr xs_v22103, tll_env env) {
  tll_ptr lam_clo_t385;
  instr_clo(&lam_clo_t385, &lam_fun_t384, 3, xs_v22103, env[0], env[1]);
  return lam_clo_t385;
}

tll_ptr lam_fun_t388(tll_ptr n_v22100, tll_env env) {
  tll_ptr lam_clo_t387;
  instr_clo(&lam_clo_t387, &lam_fun_t386, 2, n_v22100, env[0]);
  return lam_clo_t387;
}

tll_ptr lam_fun_t390(tll_ptr A_v22096, tll_env env) {
  tll_ptr lam_clo_t389;
  instr_clo(&lam_clo_t389, &lam_fun_t388, 1, A_v22096);
  return lam_clo_t389;
}

tll_ptr string_of_digit_i38(tll_ptr n_v22106) {
  tll_ptr EmptyString_t393; tll_ptr call_ret_t392;
  instr_struct(&EmptyString_t393, 6, 0);
  call_ret_t392 = get_at_i37(0, n_v22106, digits_i36, EmptyString_t393);
  return call_ret_t392;
}

tll_ptr lam_fun_t395(tll_ptr n_v22107, tll_env env) {
  tll_ptr call_ret_t394;
  call_ret_t394 = string_of_digit_i38(n_v22107);
  return call_ret_t394;
}

tll_ptr string_of_nat_i39(tll_ptr n_v22108) {
  tll_ptr call_ret_t397; tll_ptr call_ret_t398; tll_ptr call_ret_t399;
  tll_ptr call_ret_t400; tll_ptr call_ret_t401; tll_ptr call_ret_t402;
  tll_ptr ifte_ret_t403; tll_ptr n_v22110; tll_ptr s_v22109;
  call_ret_t398 = modn_i17(n_v22108, (tll_ptr)10);
  call_ret_t397 = string_of_digit_i38(call_ret_t398);
  s_v22109 = call_ret_t397;
  call_ret_t399 = divn_i16(n_v22108, (tll_ptr)10);
  n_v22110 = call_ret_t399;
  call_ret_t400 = ltn_i8((tll_ptr)0, n_v22110);
  if (call_ret_t400) {
    call_ret_t402 = string_of_nat_i39(n_v22110);
    call_ret_t401 = cats_i20(call_ret_t402, s_v22109);
    ifte_ret_t403 = call_ret_t401;
  }
  else {
    ifte_ret_t403 = s_v22109;
  }
  return ifte_ret_t403;
}

tll_ptr lam_fun_t405(tll_ptr n_v22111, tll_env env) {
  tll_ptr call_ret_t404;
  call_ret_t404 = string_of_nat_i39(n_v22111);
  return call_ret_t404;
}

tll_ptr digit_of_char_i40(tll_ptr c_v22112) {
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
  call_ret_t407 = eqc_i18(c_v22112, Char_t408);
  if (call_ret_t407) {
    instr_struct(&SomeUL_t409, 19, 1, (tll_ptr)0);
    ifte_ret_t447 = SomeUL_t409;
  }
  else {
    instr_struct(&Char_t411, 5, 1, (tll_ptr)49);
    call_ret_t410 = eqc_i18(c_v22112, Char_t411);
    if (call_ret_t410) {
      instr_struct(&SomeUL_t412, 19, 1, (tll_ptr)1);
      ifte_ret_t446 = SomeUL_t412;
    }
    else {
      instr_struct(&Char_t414, 5, 1, (tll_ptr)50);
      call_ret_t413 = eqc_i18(c_v22112, Char_t414);
      if (call_ret_t413) {
        instr_struct(&SomeUL_t415, 19, 1, (tll_ptr)2);
        ifte_ret_t445 = SomeUL_t415;
      }
      else {
        instr_struct(&Char_t417, 5, 1, (tll_ptr)51);
        call_ret_t416 = eqc_i18(c_v22112, Char_t417);
        if (call_ret_t416) {
          instr_struct(&SomeUL_t418, 19, 1, (tll_ptr)3);
          ifte_ret_t444 = SomeUL_t418;
        }
        else {
          instr_struct(&Char_t420, 5, 1, (tll_ptr)52);
          call_ret_t419 = eqc_i18(c_v22112, Char_t420);
          if (call_ret_t419) {
            instr_struct(&SomeUL_t421, 19, 1, (tll_ptr)4);
            ifte_ret_t443 = SomeUL_t421;
          }
          else {
            instr_struct(&Char_t423, 5, 1, (tll_ptr)53);
            call_ret_t422 = eqc_i18(c_v22112, Char_t423);
            if (call_ret_t422) {
              instr_struct(&SomeUL_t424, 19, 1, (tll_ptr)5);
              ifte_ret_t442 = SomeUL_t424;
            }
            else {
              instr_struct(&Char_t426, 5, 1, (tll_ptr)54);
              call_ret_t425 = eqc_i18(c_v22112, Char_t426);
              if (call_ret_t425) {
                instr_struct(&SomeUL_t427, 19, 1, (tll_ptr)6);
                ifte_ret_t441 = SomeUL_t427;
              }
              else {
                instr_struct(&Char_t429, 5, 1, (tll_ptr)55);
                call_ret_t428 = eqc_i18(c_v22112, Char_t429);
                if (call_ret_t428) {
                  instr_struct(&SomeUL_t430, 19, 1, (tll_ptr)7);
                  ifte_ret_t440 = SomeUL_t430;
                }
                else {
                  instr_struct(&Char_t432, 5, 1, (tll_ptr)56);
                  call_ret_t431 = eqc_i18(c_v22112, Char_t432);
                  if (call_ret_t431) {
                    instr_struct(&SomeUL_t433, 19, 1, (tll_ptr)8);
                    ifte_ret_t439 = SomeUL_t433;
                  }
                  else {
                    instr_struct(&Char_t435, 5, 1, (tll_ptr)57);
                    call_ret_t434 = eqc_i18(c_v22112, Char_t435);
                    if (call_ret_t434) {
                      instr_struct(&SomeUL_t436, 19, 1, (tll_ptr)9);
                      ifte_ret_t438 = SomeUL_t436;
                    }
                    else {
                      instr_struct(&NoneUL_t437, 18, 0);
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

tll_ptr lam_fun_t449(tll_ptr c_v22113, tll_env env) {
  tll_ptr call_ret_t448;
  call_ret_t448 = digit_of_char_i40(c_v22113);
  return call_ret_t448;
}

tll_ptr nat_of_string_loop_i41(tll_ptr s_v22114, tll_ptr acc_v22115) {
  tll_ptr NoneUL_t455; tll_ptr SomeUL_t452; tll_ptr c_v22116;
  tll_ptr call_ret_t453; tll_ptr call_ret_t456; tll_ptr call_ret_t457;
  tll_ptr call_ret_t458; tll_ptr n_v22118; tll_ptr s_v22117;
  tll_ptr switch_ret_t451; tll_ptr switch_ret_t454;
  switch(((tll_node)s_v22114)->tag) {
    case 6:
      instr_struct(&SomeUL_t452, 19, 1, acc_v22115);
      switch_ret_t451 = SomeUL_t452;
      break;
    case 7:
      c_v22116 = ((tll_node)s_v22114)->data[0];
      s_v22117 = ((tll_node)s_v22114)->data[1];
      call_ret_t453 = digit_of_char_i40(c_v22116);
      switch(((tll_node)call_ret_t453)->tag) {
        case 18:
          instr_free_struct(call_ret_t453);
          instr_struct(&NoneUL_t455, 18, 0);
          switch_ret_t454 = NoneUL_t455;
          break;
        case 19:
          n_v22118 = ((tll_node)call_ret_t453)->data[0];
          instr_free_struct(call_ret_t453);
          call_ret_t458 = muln_i15(acc_v22115, (tll_ptr)10);
          call_ret_t457 = addn_i13(call_ret_t458, n_v22118);
          call_ret_t456 = nat_of_string_loop_i41(s_v22117, call_ret_t457);
          switch_ret_t454 = call_ret_t456;
          break;
      }
      switch_ret_t451 = switch_ret_t454;
      break;
  }
  return switch_ret_t451;
}

tll_ptr lam_fun_t460(tll_ptr acc_v22121, tll_env env) {
  tll_ptr call_ret_t459;
  call_ret_t459 = nat_of_string_loop_i41(env[0], acc_v22121);
  return call_ret_t459;
}

tll_ptr lam_fun_t462(tll_ptr s_v22119, tll_env env) {
  tll_ptr lam_clo_t461;
  instr_clo(&lam_clo_t461, &lam_fun_t460, 1, s_v22119);
  return lam_clo_t461;
}

tll_ptr nat_of_string_i42(tll_ptr s_v22122) {
  tll_ptr call_ret_t464;
  call_ret_t464 = nat_of_string_loop_i41(s_v22122, (tll_ptr)0);
  return call_ret_t464;
}

tll_ptr lam_fun_t466(tll_ptr s_v22123, tll_env env) {
  tll_ptr call_ret_t465;
  call_ret_t465 = nat_of_string_i42(s_v22123);
  return call_ret_t465;
}

tll_ptr appendUU_i77(tll_ptr A_v22124, tll_ptr xs_v22125, tll_ptr ys_v22126) {
  tll_ptr ConsUU_t470; tll_ptr call_ret_t469; tll_ptr switch_ret_t468;
  tll_ptr x_v22127; tll_ptr xs_v22128;
  switch(((tll_node)xs_v22125)->tag) {
    case 36:
      switch_ret_t468 = ys_v22126;
      break;
    case 37:
      x_v22127 = ((tll_node)xs_v22125)->data[0];
      xs_v22128 = ((tll_node)xs_v22125)->data[1];
      call_ret_t469 = appendUU_i77(0, xs_v22128, ys_v22126);
      instr_struct(&ConsUU_t470, 37, 2, x_v22127, call_ret_t469);
      switch_ret_t468 = ConsUU_t470;
      break;
  }
  return switch_ret_t468;
}

tll_ptr lam_fun_t472(tll_ptr ys_v22134, tll_env env) {
  tll_ptr call_ret_t471;
  call_ret_t471 = appendUU_i77(env[1], env[0], ys_v22134);
  return call_ret_t471;
}

tll_ptr lam_fun_t474(tll_ptr xs_v22132, tll_env env) {
  tll_ptr lam_clo_t473;
  instr_clo(&lam_clo_t473, &lam_fun_t472, 2, xs_v22132, env[0]);
  return lam_clo_t473;
}

tll_ptr lam_fun_t476(tll_ptr A_v22129, tll_env env) {
  tll_ptr lam_clo_t475;
  instr_clo(&lam_clo_t475, &lam_fun_t474, 1, A_v22129);
  return lam_clo_t475;
}

tll_ptr appendUL_i76(tll_ptr A_v22135, tll_ptr xs_v22136, tll_ptr ys_v22137) {
  tll_ptr ConsUL_t480; tll_ptr call_ret_t479; tll_ptr switch_ret_t478;
  tll_ptr x_v22138; tll_ptr xs_v22139;
  switch(((tll_node)xs_v22136)->tag) {
    case 34:
      instr_free_struct(xs_v22136);
      switch_ret_t478 = ys_v22137;
      break;
    case 35:
      x_v22138 = ((tll_node)xs_v22136)->data[0];
      xs_v22139 = ((tll_node)xs_v22136)->data[1];
      instr_free_struct(xs_v22136);
      call_ret_t479 = appendUL_i76(0, xs_v22139, ys_v22137);
      instr_struct(&ConsUL_t480, 35, 2, x_v22138, call_ret_t479);
      switch_ret_t478 = ConsUL_t480;
      break;
  }
  return switch_ret_t478;
}

tll_ptr lam_fun_t482(tll_ptr ys_v22145, tll_env env) {
  tll_ptr call_ret_t481;
  call_ret_t481 = appendUL_i76(env[1], env[0], ys_v22145);
  return call_ret_t481;
}

tll_ptr lam_fun_t484(tll_ptr xs_v22143, tll_env env) {
  tll_ptr lam_clo_t483;
  instr_clo(&lam_clo_t483, &lam_fun_t482, 2, xs_v22143, env[0]);
  return lam_clo_t483;
}

tll_ptr lam_fun_t486(tll_ptr A_v22140, tll_env env) {
  tll_ptr lam_clo_t485;
  instr_clo(&lam_clo_t485, &lam_fun_t484, 1, A_v22140);
  return lam_clo_t485;
}

tll_ptr appendLL_i74(tll_ptr A_v22146, tll_ptr xs_v22147, tll_ptr ys_v22148) {
  tll_ptr ConsLL_t490; tll_ptr call_ret_t489; tll_ptr switch_ret_t488;
  tll_ptr x_v22149; tll_ptr xs_v22150;
  switch(((tll_node)xs_v22147)->tag) {
    case 30:
      instr_free_struct(xs_v22147);
      switch_ret_t488 = ys_v22148;
      break;
    case 31:
      x_v22149 = ((tll_node)xs_v22147)->data[0];
      xs_v22150 = ((tll_node)xs_v22147)->data[1];
      instr_free_struct(xs_v22147);
      call_ret_t489 = appendLL_i74(0, xs_v22150, ys_v22148);
      instr_struct(&ConsLL_t490, 31, 2, x_v22149, call_ret_t489);
      switch_ret_t488 = ConsLL_t490;
      break;
  }
  return switch_ret_t488;
}

tll_ptr lam_fun_t492(tll_ptr ys_v22156, tll_env env) {
  tll_ptr call_ret_t491;
  call_ret_t491 = appendLL_i74(env[1], env[0], ys_v22156);
  return call_ret_t491;
}

tll_ptr lam_fun_t494(tll_ptr xs_v22154, tll_env env) {
  tll_ptr lam_clo_t493;
  instr_clo(&lam_clo_t493, &lam_fun_t492, 2, xs_v22154, env[0]);
  return lam_clo_t493;
}

tll_ptr lam_fun_t496(tll_ptr A_v22151, tll_env env) {
  tll_ptr lam_clo_t495;
  instr_clo(&lam_clo_t495, &lam_fun_t494, 1, A_v22151);
  return lam_clo_t495;
}

tll_ptr idU_i85(tll_ptr A_v22157, tll_ptr x_v22158) {
  
  
  return x_v22158;
}

tll_ptr lam_fun_t504(tll_ptr x_v22161, tll_env env) {
  tll_ptr call_ret_t503;
  call_ret_t503 = idU_i85(env[0], x_v22161);
  return call_ret_t503;
}

tll_ptr lam_fun_t506(tll_ptr A_v22159, tll_env env) {
  tll_ptr lam_clo_t505;
  instr_clo(&lam_clo_t505, &lam_fun_t504, 1, A_v22159);
  return lam_clo_t505;
}

tll_ptr idL_i84(tll_ptr A_v22162, tll_ptr x_v22163) {
  
  
  return x_v22163;
}

tll_ptr lam_fun_t509(tll_ptr x_v22166, tll_env env) {
  tll_ptr call_ret_t508;
  call_ret_t508 = idL_i84(env[0], x_v22166);
  return call_ret_t508;
}

tll_ptr lam_fun_t511(tll_ptr A_v22164, tll_env env) {
  tll_ptr lam_clo_t510;
  instr_clo(&lam_clo_t510, &lam_fun_t509, 1, A_v22164);
  return lam_clo_t510;
}

int main() {
  instr_init();
  tll_ptr Char_t337; tll_ptr Char_t340; tll_ptr Char_t343; tll_ptr Char_t346;
  tll_ptr Char_t349; tll_ptr Char_t352; tll_ptr Char_t355; tll_ptr Char_t358;
  tll_ptr Char_t361; tll_ptr Char_t364; tll_ptr ConsUU_t499;
  tll_ptr ConsUU_t501; tll_ptr EmptyString_t338; tll_ptr EmptyString_t341;
  tll_ptr EmptyString_t344; tll_ptr EmptyString_t347;
  tll_ptr EmptyString_t350; tll_ptr EmptyString_t353;
  tll_ptr EmptyString_t356; tll_ptr EmptyString_t359;
  tll_ptr EmptyString_t362; tll_ptr EmptyString_t365; tll_ptr NilUU_t498;
  tll_ptr NilUU_t500; tll_ptr String_t339; tll_ptr String_t342;
  tll_ptr String_t345; tll_ptr String_t348; tll_ptr String_t351;
  tll_ptr String_t354; tll_ptr String_t357; tll_ptr String_t360;
  tll_ptr String_t363; tll_ptr String_t366; tll_ptr app_ret_t514;
  tll_ptr app_ret_t518; tll_ptr call_ret_t502; tll_ptr call_ret_t513;
  tll_ptr call_ret_t515; tll_ptr call_ret_t516; tll_ptr call_ret_t517;
  tll_ptr consUU_t368; tll_ptr consUU_t369; tll_ptr consUU_t370;
  tll_ptr consUU_t371; tll_ptr consUU_t372; tll_ptr consUU_t373;
  tll_ptr consUU_t374; tll_ptr consUU_t375; tll_ptr consUU_t376;
  tll_ptr consUU_t377; tll_ptr lam_clo_t104; tll_ptr lam_clo_t110;
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
  tll_ptr lam_clo_t477; tll_ptr lam_clo_t487; tll_ptr lam_clo_t497;
  tll_ptr lam_clo_t507; tll_ptr lam_clo_t512; tll_ptr lam_clo_t52;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t6; tll_ptr lam_clo_t72;
  tll_ptr lam_clo_t77; tll_ptr lam_clo_t83; tll_ptr lam_clo_t92;
  tll_ptr lam_clo_t98; tll_ptr nilUU_t367; tll_ptr s_v22167;
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
  gtenclo_i91 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  ltnclo_i92 = lam_clo_t46;
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
  instr_struct(&nilUU_t367, 28, 0);
  instr_struct(&consUU_t368, 29, 2, String_t366, nilUU_t367);
  instr_struct(&consUU_t369, 29, 2, String_t363, consUU_t368);
  instr_struct(&consUU_t370, 29, 2, String_t360, consUU_t369);
  instr_struct(&consUU_t371, 29, 2, String_t357, consUU_t370);
  instr_struct(&consUU_t372, 29, 2, String_t354, consUU_t371);
  instr_struct(&consUU_t373, 29, 2, String_t351, consUU_t372);
  instr_struct(&consUU_t374, 29, 2, String_t348, consUU_t373);
  instr_struct(&consUU_t375, 29, 2, String_t345, consUU_t374);
  instr_struct(&consUU_t376, 29, 2, String_t342, consUU_t375);
  instr_struct(&consUU_t377, 29, 2, String_t339, consUU_t376);
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
  instr_clo(&lam_clo_t477, &lam_fun_t476, 0);
  appendUUclo_i129 = lam_clo_t477;
  instr_clo(&lam_clo_t487, &lam_fun_t486, 0);
  appendULclo_i130 = lam_clo_t487;
  instr_clo(&lam_clo_t497, &lam_fun_t496, 0);
  appendLLclo_i131 = lam_clo_t497;
  instr_struct(&NilUU_t498, 36, 0);
  instr_struct(&ConsUU_t499, 37, 2, (tll_ptr)0, NilUU_t498);
  ls0_i47 = ConsUU_t499;
  instr_struct(&NilUU_t500, 36, 0);
  instr_struct(&ConsUU_t501, 37, 2, (tll_ptr)0, NilUU_t500);
  ls1_i48 = ConsUU_t501;
  call_ret_t502 = appendUU_i77(0, ls0_i47, ls1_i48);
  ls2_i49 = call_ret_t502;
  instr_clo(&lam_clo_t507, &lam_fun_t506, 0);
  idUclo_i132 = lam_clo_t507;
  instr_clo(&lam_clo_t512, &lam_fun_t511, 0);
  idLclo_i133 = lam_clo_t512;
  call_ret_t513 = readline_i33(0);
  instr_app(&app_ret_t514, call_ret_t513, 0);
  instr_free_clo(call_ret_t513);
  s_v22167 = app_ret_t514;
  call_ret_t517 = idU_i85(0, s_v22167);
  call_ret_t516 = print_i34(call_ret_t517);
  call_ret_t515 = idL_i84(0, call_ret_t516);
  instr_app(&app_ret_t518, call_ret_t515, 0);
  instr_free_clo(call_ret_t515);
  return 0;
}

