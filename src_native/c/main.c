#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v81806, tll_ptr b2_v81807);
tll_ptr orb_i2(tll_ptr b1_v81811, tll_ptr b2_v81812);
tll_ptr notb_i3(tll_ptr b_v81816);
tll_ptr lten_i4(tll_ptr x_v81818, tll_ptr y_v81819);
tll_ptr gten_i5(tll_ptr x_v81823, tll_ptr y_v81824);
tll_ptr ltn_i6(tll_ptr x_v81828, tll_ptr y_v81829);
tll_ptr gtn_i7(tll_ptr x_v81833, tll_ptr y_v81834);
tll_ptr eqn_i8(tll_ptr x_v81838, tll_ptr y_v81839);
tll_ptr pred_i9(tll_ptr x_v81843);
tll_ptr addn_i10(tll_ptr x_v81845, tll_ptr y_v81846);
tll_ptr subn_i11(tll_ptr x_v81850, tll_ptr y_v81851);
tll_ptr muln_i12(tll_ptr x_v81855, tll_ptr y_v81856);
tll_ptr divn_i13(tll_ptr x_v81860, tll_ptr y_v81861);
tll_ptr modn_i14(tll_ptr x_v81865, tll_ptr y_v81866);
tll_ptr cats_i15(tll_ptr s1_v81870, tll_ptr s2_v81871);
tll_ptr strlen_i16(tll_ptr s_v81877);
tll_ptr lenUU_i40(tll_ptr A_v81881, tll_ptr xs_v81882);
tll_ptr lenUL_i39(tll_ptr A_v81890, tll_ptr xs_v81891);
tll_ptr lenLL_i37(tll_ptr A_v81899, tll_ptr xs_v81900);
tll_ptr appendUU_i44(tll_ptr A_v81908, tll_ptr xs_v81909, tll_ptr ys_v81910);
tll_ptr appendUL_i43(tll_ptr A_v81919, tll_ptr xs_v81920, tll_ptr ys_v81921);
tll_ptr appendLL_i41(tll_ptr A_v81930, tll_ptr xs_v81931, tll_ptr ys_v81932);
tll_ptr readline_i25(tll_ptr __v81941);
tll_ptr print_i26(tll_ptr s_v81956);
tll_ptr prerr_i27(tll_ptr s_v81967);
tll_ptr splitU_i46(tll_ptr zs_v81978);
tll_ptr splitL_i45(tll_ptr zs_v81987);
tll_ptr mergeU_i48(tll_ptr xs_v81996, tll_ptr ys_v81997);
tll_ptr mergeL_i47(tll_ptr xs_v82005, tll_ptr ys_v82006);
tll_ptr msortU_i50(tll_ptr zs_v82014);
tll_ptr msortL_i49(tll_ptr zs_v82023);
tll_ptr cmsort_workerU_i54(tll_ptr n_v82032, tll_ptr zs_v82033, tll_ptr c_v82034);
tll_ptr cmsort_workerL_i53(tll_ptr n_v82093, tll_ptr zs_v82094, tll_ptr c_v82095);
tll_ptr cmsortU_i56(tll_ptr zs_v82154);
tll_ptr cmsortL_i55(tll_ptr zs_v82169);
tll_ptr mkListU_i58(tll_ptr n_v82184);
tll_ptr mkListL_i57(tll_ptr n_v82186);
tll_ptr free_i35(tll_ptr A_v82188, tll_ptr ls_v82189);

tll_ptr addnclo_i68;
tll_ptr andbclo_i59;
tll_ptr appendLLclo_i80;
tll_ptr appendULclo_i79;
tll_ptr appendUUclo_i78;
tll_ptr catsclo_i73;
tll_ptr cmsortLclo_i93;
tll_ptr cmsortUclo_i92;
tll_ptr cmsort_workerLclo_i91;
tll_ptr cmsort_workerUclo_i90;
tll_ptr divnclo_i71;
tll_ptr eqnclo_i66;
tll_ptr freeclo_i96;
tll_ptr gtenclo_i63;
tll_ptr gtnclo_i65;
tll_ptr lenLLclo_i77;
tll_ptr lenULclo_i76;
tll_ptr lenUUclo_i75;
tll_ptr ltenclo_i62;
tll_ptr ltnclo_i64;
tll_ptr mergeLclo_i87;
tll_ptr mergeUclo_i86;
tll_ptr mkListLclo_i95;
tll_ptr mkListUclo_i94;
tll_ptr modnclo_i72;
tll_ptr msortLclo_i89;
tll_ptr msortUclo_i88;
tll_ptr mulnclo_i70;
tll_ptr notbclo_i61;
tll_ptr orbclo_i60;
tll_ptr predclo_i67;
tll_ptr prerrclo_i83;
tll_ptr printclo_i82;
tll_ptr readlineclo_i81;
tll_ptr splitLclo_i85;
tll_ptr splitUclo_i84;
tll_ptr strlenclo_i74;
tll_ptr subnclo_i69;

tll_ptr andb_i1(tll_ptr b1_v81806, tll_ptr b2_v81807) {
  tll_ptr ifte_ret_t1;
  if (b1_v81806) {
    ifte_ret_t1 = b2_v81807;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v81810, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v81810);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v81808, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v81808);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v81811, tll_ptr b2_v81812) {
  tll_ptr ifte_ret_t7;
  if (b1_v81811) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v81812;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v81815, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v81815);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v81813, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v81813);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v81816) {
  tll_ptr ifte_ret_t13;
  if (b_v81816) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v81817, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v81817);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v81818, tll_ptr y_v81819) {
  tll_ptr add_ret_t18; tll_ptr add_ret_t19; tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  if (x_v81818) {
    if (y_v81819) {
      add_ret_t18 = x_v81818 - 1;
      add_ret_t19 = y_v81819 - 1;
      call_ret_t17 = lten_i4(add_ret_t18, add_ret_t19);
      ifte_ret_t20 = call_ret_t17;
    }
    else {
      ifte_ret_t20 = (tll_ptr)0;
    }
    ifte_ret_t21 = ifte_ret_t20;
  }
  else {
    ifte_ret_t21 = (tll_ptr)1;
  }
  return ifte_ret_t21;
}

tll_ptr lam_fun_t23(tll_ptr y_v81822, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v81822);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v81820, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v81820);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v81823, tll_ptr y_v81824) {
  tll_ptr add_ret_t28; tll_ptr add_ret_t29; tll_ptr call_ret_t27;
  tll_ptr ifte_ret_t30; tll_ptr ifte_ret_t31; tll_ptr ifte_ret_t32;
  if (x_v81823) {
    if (y_v81824) {
      add_ret_t28 = x_v81823 - 1;
      add_ret_t29 = y_v81824 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v81824) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v81827, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v81827);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v81825, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v81825);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v81828, tll_ptr y_v81829) {
  tll_ptr add_ret_t39; tll_ptr add_ret_t40; tll_ptr call_ret_t38;
  tll_ptr ifte_ret_t41; tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t43;
  if (x_v81828) {
    if (y_v81829) {
      add_ret_t39 = x_v81828 - 1;
      add_ret_t40 = y_v81829 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v81829) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v81832, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v81832);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v81830, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v81830);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v81833, tll_ptr y_v81834) {
  tll_ptr add_ret_t50; tll_ptr add_ret_t51; tll_ptr call_ret_t49;
  tll_ptr ifte_ret_t52; tll_ptr ifte_ret_t53;
  if (x_v81833) {
    if (y_v81834) {
      add_ret_t50 = x_v81833 - 1;
      add_ret_t51 = y_v81834 - 1;
      call_ret_t49 = gtn_i7(add_ret_t50, add_ret_t51);
      ifte_ret_t52 = call_ret_t49;
    }
    else {
      ifte_ret_t52 = (tll_ptr)1;
    }
    ifte_ret_t53 = ifte_ret_t52;
  }
  else {
    ifte_ret_t53 = (tll_ptr)0;
  }
  return ifte_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v81837, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v81837);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v81835, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v81835);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v81838, tll_ptr y_v81839) {
  tll_ptr add_ret_t60; tll_ptr add_ret_t61; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t62; tll_ptr ifte_ret_t63; tll_ptr ifte_ret_t64;
  if (x_v81838) {
    if (y_v81839) {
      add_ret_t60 = x_v81838 - 1;
      add_ret_t61 = y_v81839 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v81839) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v81842, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v81842);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v81840, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v81840);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v81843) {
  tll_ptr add_ret_t70; tll_ptr ifte_ret_t71;
  if (x_v81843) {
    add_ret_t70 = x_v81843 - 1;
    ifte_ret_t71 = add_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v81844, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v81844);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v81845, tll_ptr y_v81846) {
  tll_ptr add_ret_t76; tll_ptr add_ret_t77; tll_ptr call_ret_t75;
  tll_ptr ifte_ret_t78;
  if (x_v81845) {
    add_ret_t76 = x_v81845 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v81846);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v81846;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v81849, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v81849);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v81847, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v81847);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v81850, tll_ptr y_v81851) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v81851) {
    call_ret_t85 = pred_i9(x_v81850);
    add_ret_t86 = y_v81851 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v81850;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v81854, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v81854);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v81852, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v81852);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v81855, tll_ptr y_v81856) {
  tll_ptr add_ret_t95; tll_ptr call_ret_t93; tll_ptr call_ret_t94;
  tll_ptr ifte_ret_t96;
  if (x_v81855) {
    add_ret_t95 = x_v81855 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v81856);
    call_ret_t93 = addn_i10(y_v81856, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v81859, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v81859);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v81857, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v81857);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v81860, tll_ptr y_v81861) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v81860, y_v81861);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v81860, y_v81861);
    call_ret_t103 = divn_i13(call_ret_t104, y_v81861);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v81864, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v81864);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v81862, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v81862);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v81865, tll_ptr y_v81866) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v81865, y_v81866);
  call_ret_t113 = muln_i12(call_ret_t114, y_v81866);
  call_ret_t112 = subn_i11(x_v81865, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v81869, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v81869);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v81867, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v81867);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v81870, tll_ptr s2_v81871) {
  tll_ptr String_t122; tll_ptr c_v81872; tll_ptr call_ret_t121;
  tll_ptr s1_v81873; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v81870)->tag) {
    case 2:
      switch_ret_t120 = s2_v81871;
      break;
    case 3:
      c_v81872 = ((tll_node)s1_v81870)->data[0];
      s1_v81873 = ((tll_node)s1_v81870)->data[1];
      call_ret_t121 = cats_i15(s1_v81873, s2_v81871);
      instr_struct(&String_t122, 3, 2, c_v81872, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v81876, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v81876);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v81874, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v81874);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v81877) {
  tll_ptr __v81878; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v81879; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v81877)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v81878 = ((tll_node)s_v81877)->data[0];
      s_v81879 = ((tll_node)s_v81877)->data[1];
      call_ret_t129 = strlen_i16(s_v81879);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v81880, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v81880);
  return call_ret_t131;
}

tll_ptr lenUU_i40(tll_ptr A_v81881, tll_ptr xs_v81882) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v81885; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v81883; tll_ptr xs_v81884; tll_ptr xs_v81886;
  switch(((tll_node)xs_v81882)->tag) {
    case 13:
      instr_struct(&nilUU_t135, 13, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 14:
      x_v81883 = ((tll_node)xs_v81882)->data[0];
      xs_v81884 = ((tll_node)xs_v81882)->data[1];
      call_ret_t137 = lenUU_i40(0, xs_v81884);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v81885 = ((tll_node)call_ret_t137)->data[0];
          xs_v81886 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v81885 + 1;
          instr_struct(&consUU_t140, 14, 2, x_v81883, xs_v81886);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v81889, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i40(env[0], xs_v81889);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v81887, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v81887);
  return lam_clo_t144;
}

tll_ptr lenUL_i39(tll_ptr A_v81890, tll_ptr xs_v81891) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v81894; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v81892; tll_ptr xs_v81893; tll_ptr xs_v81895;
  switch(((tll_node)xs_v81891)->tag) {
    case 11:
      instr_free_struct(xs_v81891);
      instr_struct(&nilUL_t148, 11, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 12:
      x_v81892 = ((tll_node)xs_v81891)->data[0];
      xs_v81893 = ((tll_node)xs_v81891)->data[1];
      instr_free_struct(xs_v81891);
      call_ret_t150 = lenUL_i39(0, xs_v81893);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v81894 = ((tll_node)call_ret_t150)->data[0];
          xs_v81895 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v81894 + 1;
          instr_struct(&consUL_t153, 12, 2, x_v81892, xs_v81895);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v81898, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i39(env[0], xs_v81898);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v81896, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v81896);
  return lam_clo_t157;
}

tll_ptr lenLL_i37(tll_ptr A_v81899, tll_ptr xs_v81900) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v81903; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v81901; tll_ptr xs_v81902; tll_ptr xs_v81904;
  switch(((tll_node)xs_v81900)->tag) {
    case 7:
      instr_free_struct(xs_v81900);
      instr_struct(&nilLL_t161, 7, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 8:
      x_v81901 = ((tll_node)xs_v81900)->data[0];
      xs_v81902 = ((tll_node)xs_v81900)->data[1];
      instr_free_struct(xs_v81900);
      call_ret_t163 = lenLL_i37(0, xs_v81902);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v81903 = ((tll_node)call_ret_t163)->data[0];
          xs_v81904 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v81903 + 1;
          instr_struct(&consLL_t166, 8, 2, x_v81901, xs_v81904);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v81907, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i37(env[0], xs_v81907);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v81905, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v81905);
  return lam_clo_t170;
}

tll_ptr appendUU_i44(tll_ptr A_v81908, tll_ptr xs_v81909, tll_ptr ys_v81910) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v81911; tll_ptr xs_v81912;
  switch(((tll_node)xs_v81909)->tag) {
    case 13:
      switch_ret_t173 = ys_v81910;
      break;
    case 14:
      x_v81911 = ((tll_node)xs_v81909)->data[0];
      xs_v81912 = ((tll_node)xs_v81909)->data[1];
      call_ret_t174 = appendUU_i44(0, xs_v81912, ys_v81910);
      instr_struct(&consUU_t175, 14, 2, x_v81911, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v81918, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i44(env[1], env[0], ys_v81918);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v81916, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v81916, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v81913, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v81913);
  return lam_clo_t180;
}

tll_ptr appendUL_i43(tll_ptr A_v81919, tll_ptr xs_v81920, tll_ptr ys_v81921) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v81922; tll_ptr xs_v81923;
  switch(((tll_node)xs_v81920)->tag) {
    case 11:
      instr_free_struct(xs_v81920);
      switch_ret_t183 = ys_v81921;
      break;
    case 12:
      x_v81922 = ((tll_node)xs_v81920)->data[0];
      xs_v81923 = ((tll_node)xs_v81920)->data[1];
      instr_free_struct(xs_v81920);
      call_ret_t184 = appendUL_i43(0, xs_v81923, ys_v81921);
      instr_struct(&consUL_t185, 12, 2, x_v81922, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v81929, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i43(env[1], env[0], ys_v81929);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v81927, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v81927, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v81924, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v81924);
  return lam_clo_t190;
}

tll_ptr appendLL_i41(tll_ptr A_v81930, tll_ptr xs_v81931, tll_ptr ys_v81932) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v81933; tll_ptr xs_v81934;
  switch(((tll_node)xs_v81931)->tag) {
    case 7:
      instr_free_struct(xs_v81931);
      switch_ret_t193 = ys_v81932;
      break;
    case 8:
      x_v81933 = ((tll_node)xs_v81931)->data[0];
      xs_v81934 = ((tll_node)xs_v81931)->data[1];
      instr_free_struct(xs_v81931);
      call_ret_t194 = appendLL_i41(0, xs_v81934, ys_v81932);
      instr_struct(&consLL_t195, 8, 2, x_v81933, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v81940, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i41(env[1], env[0], ys_v81940);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v81938, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v81938, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v81935, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v81935);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v81942, tll_env env) {
  tll_ptr __v81951; tll_ptr ch_v81949; tll_ptr ch_v81950; tll_ptr ch_v81953;
  tll_ptr ch_v81954; tll_ptr prim_ch_t203; tll_ptr recv_msg_t205;
  tll_ptr s_v81952; tll_ptr send_ch_t204; tll_ptr send_ch_t207;
  tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v81949 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v81949, (tll_ptr)1);
  ch_v81950 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v81950);
  __v81951 = recv_msg_t205;
  switch(((tll_node)__v81951)->tag) {
    case 0:
      s_v81952 = ((tll_node)__v81951)->data[0];
      ch_v81953 = ((tll_node)__v81951)->data[1];
      instr_free_struct(__v81951);
      instr_send(&send_ch_t207, ch_v81953, (tll_ptr)0);
      ch_v81954 = send_ch_t207;
      switch_ret_t206 = s_v81952;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v81941) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v81955, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v81955);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v81957, tll_env env) {
  tll_ptr ch_v81962; tll_ptr ch_v81963; tll_ptr ch_v81964; tll_ptr ch_v81965;
  tll_ptr prim_ch_t213; tll_ptr send_ch_t214; tll_ptr send_ch_t215;
  tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v81962 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v81962, (tll_ptr)1);
  ch_v81963 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v81963, env[0]);
  ch_v81964 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v81964, (tll_ptr)0);
  ch_v81965 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v81956) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v81956);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v81966, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v81966);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v81968, tll_env env) {
  tll_ptr ch_v81973; tll_ptr ch_v81974; tll_ptr ch_v81975; tll_ptr ch_v81976;
  tll_ptr prim_ch_t222; tll_ptr send_ch_t223; tll_ptr send_ch_t224;
  tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v81973 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v81973, (tll_ptr)1);
  ch_v81974 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v81974, env[0]);
  ch_v81975 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v81975, (tll_ptr)0);
  ch_v81976 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v81967) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v81967);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v81977, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v81977);
  return call_ret_t228;
}

tll_ptr splitU_i46(tll_ptr zs_v81978) {
  tll_ptr __v81983; tll_ptr call_ret_t240; tll_ptr consUU_t237;
  tll_ptr consUU_t242; tll_ptr consUU_t243; tll_ptr nilUU_t232;
  tll_ptr nilUU_t233; tll_ptr nilUU_t236; tll_ptr nilUU_t238;
  tll_ptr pair_struct_t234; tll_ptr pair_struct_t239;
  tll_ptr pair_struct_t244; tll_ptr switch_ret_t231; tll_ptr switch_ret_t235;
  tll_ptr switch_ret_t241; tll_ptr x_v81979; tll_ptr xs_v81984;
  tll_ptr y_v81981; tll_ptr ys_v81985; tll_ptr zs_v81980; tll_ptr zs_v81982;
  switch(((tll_node)zs_v81978)->tag) {
    case 13:
      instr_struct(&nilUU_t232, 13, 0);
      instr_struct(&nilUU_t233, 13, 0);
      instr_struct(&pair_struct_t234, 0, 2, nilUU_t232, nilUU_t233);
      switch_ret_t231 = pair_struct_t234;
      break;
    case 14:
      x_v81979 = ((tll_node)zs_v81978)->data[0];
      zs_v81980 = ((tll_node)zs_v81978)->data[1];
      switch(((tll_node)zs_v81980)->tag) {
        case 13:
          instr_struct(&nilUU_t236, 13, 0);
          instr_struct(&consUU_t237, 14, 2, x_v81979, nilUU_t236);
          instr_struct(&nilUU_t238, 13, 0);
          instr_struct(&pair_struct_t239, 0, 2, consUU_t237, nilUU_t238);
          switch_ret_t235 = pair_struct_t239;
          break;
        case 14:
          y_v81981 = ((tll_node)zs_v81980)->data[0];
          zs_v81982 = ((tll_node)zs_v81980)->data[1];
          call_ret_t240 = splitU_i46(zs_v81982);
          __v81983 = call_ret_t240;
          switch(((tll_node)__v81983)->tag) {
            case 0:
              xs_v81984 = ((tll_node)__v81983)->data[0];
              ys_v81985 = ((tll_node)__v81983)->data[1];
              instr_free_struct(__v81983);
              instr_struct(&consUU_t242, 14, 2, x_v81979, xs_v81984);
              instr_struct(&consUU_t243, 14, 2, y_v81981, ys_v81985);
              instr_struct(&pair_struct_t244, 0, 2, consUU_t242, consUU_t243);
              switch_ret_t241 = pair_struct_t244;
              break;
          }
          switch_ret_t235 = switch_ret_t241;
          break;
      }
      switch_ret_t231 = switch_ret_t235;
      break;
  }
  return switch_ret_t231;
}

tll_ptr lam_fun_t246(tll_ptr zs_v81986, tll_env env) {
  tll_ptr call_ret_t245;
  call_ret_t245 = splitU_i46(zs_v81986);
  return call_ret_t245;
}

tll_ptr splitL_i45(tll_ptr zs_v81987) {
  tll_ptr __v81992; tll_ptr call_ret_t257; tll_ptr consUL_t254;
  tll_ptr consUL_t259; tll_ptr consUL_t260; tll_ptr nilUL_t249;
  tll_ptr nilUL_t250; tll_ptr nilUL_t253; tll_ptr nilUL_t255;
  tll_ptr pair_struct_t251; tll_ptr pair_struct_t256;
  tll_ptr pair_struct_t261; tll_ptr switch_ret_t248; tll_ptr switch_ret_t252;
  tll_ptr switch_ret_t258; tll_ptr x_v81988; tll_ptr xs_v81993;
  tll_ptr y_v81990; tll_ptr ys_v81994; tll_ptr zs_v81989; tll_ptr zs_v81991;
  switch(((tll_node)zs_v81987)->tag) {
    case 11:
      instr_free_struct(zs_v81987);
      instr_struct(&nilUL_t249, 11, 0);
      instr_struct(&nilUL_t250, 11, 0);
      instr_struct(&pair_struct_t251, 0, 2, nilUL_t249, nilUL_t250);
      switch_ret_t248 = pair_struct_t251;
      break;
    case 12:
      x_v81988 = ((tll_node)zs_v81987)->data[0];
      zs_v81989 = ((tll_node)zs_v81987)->data[1];
      instr_free_struct(zs_v81987);
      switch(((tll_node)zs_v81989)->tag) {
        case 11:
          instr_free_struct(zs_v81989);
          instr_struct(&nilUL_t253, 11, 0);
          instr_struct(&consUL_t254, 12, 2, x_v81988, nilUL_t253);
          instr_struct(&nilUL_t255, 11, 0);
          instr_struct(&pair_struct_t256, 0, 2, consUL_t254, nilUL_t255);
          switch_ret_t252 = pair_struct_t256;
          break;
        case 12:
          y_v81990 = ((tll_node)zs_v81989)->data[0];
          zs_v81991 = ((tll_node)zs_v81989)->data[1];
          instr_free_struct(zs_v81989);
          call_ret_t257 = splitL_i45(zs_v81991);
          __v81992 = call_ret_t257;
          switch(((tll_node)__v81992)->tag) {
            case 0:
              xs_v81993 = ((tll_node)__v81992)->data[0];
              ys_v81994 = ((tll_node)__v81992)->data[1];
              instr_free_struct(__v81992);
              instr_struct(&consUL_t259, 12, 2, x_v81988, xs_v81993);
              instr_struct(&consUL_t260, 12, 2, y_v81990, ys_v81994);
              instr_struct(&pair_struct_t261, 0, 2, consUL_t259, consUL_t260);
              switch_ret_t258 = pair_struct_t261;
              break;
          }
          switch_ret_t252 = switch_ret_t258;
          break;
      }
      switch_ret_t248 = switch_ret_t252;
      break;
  }
  return switch_ret_t248;
}

tll_ptr lam_fun_t263(tll_ptr zs_v81995, tll_env env) {
  tll_ptr call_ret_t262;
  call_ret_t262 = splitL_i45(zs_v81995);
  return call_ret_t262;
}

tll_ptr mergeU_i48(tll_ptr xs_v81996, tll_ptr ys_v81997) {
  tll_ptr call_ret_t268; tll_ptr call_ret_t269; tll_ptr call_ret_t272;
  tll_ptr consUU_t267; tll_ptr consUU_t270; tll_ptr consUU_t271;
  tll_ptr consUU_t273; tll_ptr consUU_t274; tll_ptr ifte_ret_t275;
  tll_ptr switch_ret_t265; tll_ptr switch_ret_t266; tll_ptr x_v81998;
  tll_ptr xs0_v81999; tll_ptr y_v82000; tll_ptr ys0_v82001;
  switch(((tll_node)xs_v81996)->tag) {
    case 13:
      switch_ret_t265 = ys_v81997;
      break;
    case 14:
      x_v81998 = ((tll_node)xs_v81996)->data[0];
      xs0_v81999 = ((tll_node)xs_v81996)->data[1];
      switch(((tll_node)ys_v81997)->tag) {
        case 13:
          instr_struct(&consUU_t267, 14, 2, x_v81998, xs0_v81999);
          switch_ret_t266 = consUU_t267;
          break;
        case 14:
          y_v82000 = ((tll_node)ys_v81997)->data[0];
          ys0_v82001 = ((tll_node)ys_v81997)->data[1];
          call_ret_t268 = lten_i4(x_v81998, y_v82000);
          if (call_ret_t268) {
            instr_struct(&consUU_t270, 14, 2, y_v82000, ys0_v82001);
            call_ret_t269 = mergeU_i48(xs0_v81999, consUU_t270);
            instr_struct(&consUU_t271, 14, 2, x_v81998, call_ret_t269);
            ifte_ret_t275 = consUU_t271;
          }
          else {
            instr_struct(&consUU_t273, 14, 2, x_v81998, xs0_v81999);
            call_ret_t272 = mergeU_i48(consUU_t273, ys0_v82001);
            instr_struct(&consUU_t274, 14, 2, y_v82000, call_ret_t272);
            ifte_ret_t275 = consUU_t274;
          }
          switch_ret_t266 = ifte_ret_t275;
          break;
      }
      switch_ret_t265 = switch_ret_t266;
      break;
  }
  return switch_ret_t265;
}

tll_ptr lam_fun_t277(tll_ptr ys_v82004, tll_env env) {
  tll_ptr call_ret_t276;
  call_ret_t276 = mergeU_i48(env[0], ys_v82004);
  return call_ret_t276;
}

tll_ptr lam_fun_t279(tll_ptr xs_v82002, tll_env env) {
  tll_ptr lam_clo_t278;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 1, xs_v82002);
  return lam_clo_t278;
}

tll_ptr mergeL_i47(tll_ptr xs_v82005, tll_ptr ys_v82006) {
  tll_ptr call_ret_t284; tll_ptr call_ret_t285; tll_ptr call_ret_t288;
  tll_ptr consUL_t283; tll_ptr consUL_t286; tll_ptr consUL_t287;
  tll_ptr consUL_t289; tll_ptr consUL_t290; tll_ptr ifte_ret_t291;
  tll_ptr switch_ret_t281; tll_ptr switch_ret_t282; tll_ptr x_v82007;
  tll_ptr xs0_v82008; tll_ptr y_v82009; tll_ptr ys0_v82010;
  switch(((tll_node)xs_v82005)->tag) {
    case 11:
      instr_free_struct(xs_v82005);
      switch_ret_t281 = ys_v82006;
      break;
    case 12:
      x_v82007 = ((tll_node)xs_v82005)->data[0];
      xs0_v82008 = ((tll_node)xs_v82005)->data[1];
      instr_free_struct(xs_v82005);
      switch(((tll_node)ys_v82006)->tag) {
        case 11:
          instr_free_struct(ys_v82006);
          instr_struct(&consUL_t283, 12, 2, x_v82007, xs0_v82008);
          switch_ret_t282 = consUL_t283;
          break;
        case 12:
          y_v82009 = ((tll_node)ys_v82006)->data[0];
          ys0_v82010 = ((tll_node)ys_v82006)->data[1];
          instr_free_struct(ys_v82006);
          call_ret_t284 = lten_i4(x_v82007, y_v82009);
          if (call_ret_t284) {
            instr_struct(&consUL_t286, 12, 2, y_v82009, ys0_v82010);
            call_ret_t285 = mergeL_i47(xs0_v82008, consUL_t286);
            instr_struct(&consUL_t287, 12, 2, x_v82007, call_ret_t285);
            ifte_ret_t291 = consUL_t287;
          }
          else {
            instr_struct(&consUL_t289, 12, 2, x_v82007, xs0_v82008);
            call_ret_t288 = mergeL_i47(consUL_t289, ys0_v82010);
            instr_struct(&consUL_t290, 12, 2, y_v82009, call_ret_t288);
            ifte_ret_t291 = consUL_t290;
          }
          switch_ret_t282 = ifte_ret_t291;
          break;
      }
      switch_ret_t281 = switch_ret_t282;
      break;
  }
  return switch_ret_t281;
}

tll_ptr lam_fun_t293(tll_ptr ys_v82013, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = mergeL_i47(env[0], ys_v82013);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v82011, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 1, xs_v82011);
  return lam_clo_t294;
}

tll_ptr msortU_i50(tll_ptr zs_v82014) {
  tll_ptr __v82019; tll_ptr call_ret_t302; tll_ptr call_ret_t306;
  tll_ptr call_ret_t307; tll_ptr call_ret_t308; tll_ptr consUU_t301;
  tll_ptr consUU_t303; tll_ptr consUU_t304; tll_ptr nilUU_t298;
  tll_ptr nilUU_t300; tll_ptr switch_ret_t297; tll_ptr switch_ret_t299;
  tll_ptr switch_ret_t305; tll_ptr x_v82015; tll_ptr xs_v82020;
  tll_ptr y_v82017; tll_ptr ys_v82021; tll_ptr zs_v82016; tll_ptr zs_v82018;
  switch(((tll_node)zs_v82014)->tag) {
    case 13:
      instr_struct(&nilUU_t298, 13, 0);
      switch_ret_t297 = nilUU_t298;
      break;
    case 14:
      x_v82015 = ((tll_node)zs_v82014)->data[0];
      zs_v82016 = ((tll_node)zs_v82014)->data[1];
      switch(((tll_node)zs_v82016)->tag) {
        case 13:
          instr_struct(&nilUU_t300, 13, 0);
          instr_struct(&consUU_t301, 14, 2, x_v82015, nilUU_t300);
          switch_ret_t299 = consUU_t301;
          break;
        case 14:
          y_v82017 = ((tll_node)zs_v82016)->data[0];
          zs_v82018 = ((tll_node)zs_v82016)->data[1];
          instr_struct(&consUU_t303, 14, 2, y_v82017, zs_v82018);
          instr_struct(&consUU_t304, 14, 2, x_v82015, consUU_t303);
          call_ret_t302 = splitU_i46(consUU_t304);
          __v82019 = call_ret_t302;
          switch(((tll_node)__v82019)->tag) {
            case 0:
              xs_v82020 = ((tll_node)__v82019)->data[0];
              ys_v82021 = ((tll_node)__v82019)->data[1];
              instr_free_struct(__v82019);
              call_ret_t307 = msortU_i50(xs_v82020);
              call_ret_t308 = msortU_i50(ys_v82021);
              call_ret_t306 = mergeU_i48(call_ret_t307, call_ret_t308);
              switch_ret_t305 = call_ret_t306;
              break;
          }
          switch_ret_t299 = switch_ret_t305;
          break;
      }
      switch_ret_t297 = switch_ret_t299;
      break;
  }
  return switch_ret_t297;
}

tll_ptr lam_fun_t310(tll_ptr zs_v82022, tll_env env) {
  tll_ptr call_ret_t309;
  call_ret_t309 = msortU_i50(zs_v82022);
  return call_ret_t309;
}

tll_ptr msortL_i49(tll_ptr zs_v82023) {
  tll_ptr __v82028; tll_ptr call_ret_t317; tll_ptr call_ret_t321;
  tll_ptr call_ret_t322; tll_ptr call_ret_t323; tll_ptr consUL_t316;
  tll_ptr consUL_t318; tll_ptr consUL_t319; tll_ptr nilUL_t313;
  tll_ptr nilUL_t315; tll_ptr switch_ret_t312; tll_ptr switch_ret_t314;
  tll_ptr switch_ret_t320; tll_ptr x_v82024; tll_ptr xs_v82029;
  tll_ptr y_v82026; tll_ptr ys_v82030; tll_ptr zs_v82025; tll_ptr zs_v82027;
  switch(((tll_node)zs_v82023)->tag) {
    case 11:
      instr_free_struct(zs_v82023);
      instr_struct(&nilUL_t313, 11, 0);
      switch_ret_t312 = nilUL_t313;
      break;
    case 12:
      x_v82024 = ((tll_node)zs_v82023)->data[0];
      zs_v82025 = ((tll_node)zs_v82023)->data[1];
      instr_free_struct(zs_v82023);
      switch(((tll_node)zs_v82025)->tag) {
        case 11:
          instr_free_struct(zs_v82025);
          instr_struct(&nilUL_t315, 11, 0);
          instr_struct(&consUL_t316, 12, 2, x_v82024, nilUL_t315);
          switch_ret_t314 = consUL_t316;
          break;
        case 12:
          y_v82026 = ((tll_node)zs_v82025)->data[0];
          zs_v82027 = ((tll_node)zs_v82025)->data[1];
          instr_free_struct(zs_v82025);
          instr_struct(&consUL_t318, 12, 2, y_v82026, zs_v82027);
          instr_struct(&consUL_t319, 12, 2, x_v82024, consUL_t318);
          call_ret_t317 = splitL_i45(consUL_t319);
          __v82028 = call_ret_t317;
          switch(((tll_node)__v82028)->tag) {
            case 0:
              xs_v82029 = ((tll_node)__v82028)->data[0];
              ys_v82030 = ((tll_node)__v82028)->data[1];
              instr_free_struct(__v82028);
              call_ret_t322 = msortL_i49(xs_v82029);
              call_ret_t323 = msortL_i49(ys_v82030);
              call_ret_t321 = mergeL_i47(call_ret_t322, call_ret_t323);
              switch_ret_t320 = call_ret_t321;
              break;
          }
          switch_ret_t314 = switch_ret_t320;
          break;
      }
      switch_ret_t312 = switch_ret_t314;
      break;
  }
  return switch_ret_t312;
}

tll_ptr lam_fun_t325(tll_ptr zs_v82031, tll_env env) {
  tll_ptr call_ret_t324;
  call_ret_t324 = msortL_i49(zs_v82031);
  return call_ret_t324;
}

tll_ptr lam_fun_t331(tll_ptr __v82035, tll_env env) {
  tll_ptr UniqU_t330; tll_ptr c_v82037; tll_ptr nilUU_t329;
  tll_ptr send_ch_t328;
  instr_struct(&nilUU_t329, 13, 0);
  instr_struct(&UniqU_t330, 16, 2, nilUU_t329, 0);
  instr_send(&send_ch_t328, env[0], UniqU_t330);
  c_v82037 = send_ch_t328;
  return 0;
}

tll_ptr lam_fun_t338(tll_ptr __v82040, tll_env env) {
  tll_ptr UniqU_t337; tll_ptr c_v82042; tll_ptr consUU_t336;
  tll_ptr nilUU_t335; tll_ptr send_ch_t334;
  instr_struct(&nilUU_t335, 13, 0);
  instr_struct(&consUU_t336, 14, 2, env[0], nilUU_t335);
  instr_struct(&UniqU_t337, 16, 2, consUU_t336, 0);
  instr_send(&send_ch_t334, env[1], UniqU_t337);
  c_v82042 = send_ch_t334;
  return 0;
}

tll_ptr fork_fun_t347(tll_env env) {
  tll_ptr add_ret_t345; tll_ptr app_ret_t346; tll_ptr call_ret_t344;
  tll_ptr fork_ret_t349;
  add_ret_t345 = env[2] - 1;
  call_ret_t344 = cmsort_workerU_i54(add_ret_t345, env[1], env[0]);
  instr_app(&app_ret_t346, call_ret_t344, 0);
  instr_free_clo(call_ret_t344);
  fork_ret_t349 = app_ret_t346;
  instr_free_thread(env);
  return fork_ret_t349;
}

tll_ptr fork_fun_t353(tll_env env) {
  tll_ptr add_ret_t351; tll_ptr app_ret_t352; tll_ptr call_ret_t350;
  tll_ptr fork_ret_t355;
  add_ret_t351 = env[2] - 1;
  call_ret_t350 = cmsort_workerU_i54(add_ret_t351, env[1], env[0]);
  instr_app(&app_ret_t352, call_ret_t350, 0);
  instr_free_clo(call_ret_t350);
  fork_ret_t355 = app_ret_t352;
  instr_free_thread(env);
  return fork_ret_t355;
}

tll_ptr lam_fun_t367(tll_ptr __v82047, tll_env env) {
  tll_ptr UniqU_t364; tll_ptr __v82070; tll_ptr __v82073; tll_ptr __v82082;
  tll_ptr __v82083; tll_ptr c_v82081; tll_ptr call_ret_t362;
  tll_ptr close_tmp_t365; tll_ptr close_tmp_t366; tll_ptr fork_ch_t348;
  tll_ptr fork_ch_t354; tll_ptr msg1_v82071; tll_ptr msg2_v82074;
  tll_ptr pf1_v82077; tll_ptr pf2_v82079; tll_ptr r1_v82066;
  tll_ptr r1_v82072; tll_ptr r2_v82068; tll_ptr r2_v82075;
  tll_ptr recv_msg_t356; tll_ptr recv_msg_t358; tll_ptr send_ch_t363;
  tll_ptr switch_ret_t357; tll_ptr switch_ret_t359; tll_ptr switch_ret_t360;
  tll_ptr switch_ret_t361; tll_ptr xs1_v82076; tll_ptr xs2_v82078;
  tll_ptr zs_v82080;
  instr_fork(&fork_ch_t348, &fork_fun_t347, 2, env[1], env[3]);
  r1_v82066 = fork_ch_t348;
  instr_fork(&fork_ch_t354, &fork_fun_t353, 2, env[0], env[3]);
  r2_v82068 = fork_ch_t354;
  instr_recv(&recv_msg_t356, r1_v82066);
  __v82070 = recv_msg_t356;
  switch(((tll_node)__v82070)->tag) {
    case 0:
      msg1_v82071 = ((tll_node)__v82070)->data[0];
      r1_v82072 = ((tll_node)__v82070)->data[1];
      instr_free_struct(__v82070);
      instr_recv(&recv_msg_t358, r2_v82068);
      __v82073 = recv_msg_t358;
      switch(((tll_node)__v82073)->tag) {
        case 0:
          msg2_v82074 = ((tll_node)__v82073)->data[0];
          r2_v82075 = ((tll_node)__v82073)->data[1];
          instr_free_struct(__v82073);
          switch(((tll_node)msg1_v82071)->tag) {
            case 16:
              xs1_v82076 = ((tll_node)msg1_v82071)->data[0];
              pf1_v82077 = ((tll_node)msg1_v82071)->data[1];
              switch(((tll_node)msg2_v82074)->tag) {
                case 16:
                  xs2_v82078 = ((tll_node)msg2_v82074)->data[0];
                  pf2_v82079 = ((tll_node)msg2_v82074)->data[1];
                  call_ret_t362 = mergeU_i48(xs1_v82076, xs2_v82078);
                  zs_v82080 = call_ret_t362;
                  instr_struct(&UniqU_t364, 16, 2, zs_v82080, 0);
                  instr_send(&send_ch_t363, env[2], UniqU_t364);
                  c_v82081 = send_ch_t363;
                  instr_close(&close_tmp_t365, r1_v82072);
                  __v82082 = close_tmp_t365;
                  instr_close(&close_tmp_t366, r2_v82075);
                  __v82083 = close_tmp_t366;
                  switch_ret_t361 = 0;
                  break;
              }
              switch_ret_t360 = switch_ret_t361;
              break;
          }
          switch_ret_t359 = switch_ret_t360;
          break;
      }
      switch_ret_t357 = switch_ret_t359;
      break;
  }
  return switch_ret_t357;
}

tll_ptr lam_fun_t372(tll_ptr __v82084, tll_env env) {
  tll_ptr UniqU_t371; tll_ptr c_v82086; tll_ptr call_ret_t370;
  tll_ptr send_ch_t369;
  call_ret_t370 = msortU_i50(env[1]);
  instr_struct(&UniqU_t371, 16, 2, call_ret_t370, 0);
  instr_send(&send_ch_t369, env[0], UniqU_t371);
  c_v82086 = send_ch_t369;
  return 0;
}

tll_ptr cmsort_workerU_i54(tll_ptr n_v82032, tll_ptr zs_v82033, tll_ptr c_v82034) {
  tll_ptr call_ret_t340; tll_ptr consUU_t341; tll_ptr consUU_t342;
  tll_ptr ifte_ret_t374; tll_ptr lam_clo_t332; tll_ptr lam_clo_t339;
  tll_ptr lam_clo_t368; tll_ptr lam_clo_t373; tll_ptr switch_ret_t327;
  tll_ptr switch_ret_t333; tll_ptr switch_ret_t343; tll_ptr xs0_v82045;
  tll_ptr ys0_v82046; tll_ptr z0_v82038; tll_ptr z1_v82043;
  tll_ptr zs0_v82039; tll_ptr zs1_v82044;
  if (n_v82032) {
    switch(((tll_node)zs_v82033)->tag) {
      case 13:
        instr_clo(&lam_clo_t332, &lam_fun_t331, 1, c_v82034);
        switch_ret_t327 = lam_clo_t332;
        break;
      case 14:
        z0_v82038 = ((tll_node)zs_v82033)->data[0];
        zs0_v82039 = ((tll_node)zs_v82033)->data[1];
        switch(((tll_node)zs0_v82039)->tag) {
          case 13:
            instr_clo(&lam_clo_t339, &lam_fun_t338, 2, z0_v82038, c_v82034);
            switch_ret_t333 = lam_clo_t339;
            break;
          case 14:
            z1_v82043 = ((tll_node)zs0_v82039)->data[0];
            zs1_v82044 = ((tll_node)zs0_v82039)->data[1];
            instr_struct(&consUU_t341, 14, 2, z1_v82043, zs1_v82044);
            instr_struct(&consUU_t342, 14, 2, z0_v82038, consUU_t341);
            call_ret_t340 = splitU_i46(consUU_t342);
            switch(((tll_node)call_ret_t340)->tag) {
              case 0:
                xs0_v82045 = ((tll_node)call_ret_t340)->data[0];
                ys0_v82046 = ((tll_node)call_ret_t340)->data[1];
                instr_free_struct(call_ret_t340);
                instr_clo(&lam_clo_t368, &lam_fun_t367, 4,
                          ys0_v82046, xs0_v82045, c_v82034, n_v82032);
                switch_ret_t343 = lam_clo_t368;
                break;
            }
            switch_ret_t333 = switch_ret_t343;
            break;
        }
        switch_ret_t327 = switch_ret_t333;
        break;
    }
    ifte_ret_t374 = switch_ret_t327;
  }
  else {
    instr_clo(&lam_clo_t373, &lam_fun_t372, 2, c_v82034, zs_v82033);
    ifte_ret_t374 = lam_clo_t373;
  }
  return ifte_ret_t374;
}

tll_ptr lam_fun_t376(tll_ptr c_v82092, tll_env env) {
  tll_ptr call_ret_t375;
  call_ret_t375 = cmsort_workerU_i54(env[1], env[0], c_v82092);
  return call_ret_t375;
}

tll_ptr lam_fun_t378(tll_ptr zs_v82090, tll_env env) {
  tll_ptr lam_clo_t377;
  instr_clo(&lam_clo_t377, &lam_fun_t376, 2, zs_v82090, env[0]);
  return lam_clo_t377;
}

tll_ptr lam_fun_t380(tll_ptr n_v82087, tll_env env) {
  tll_ptr lam_clo_t379;
  instr_clo(&lam_clo_t379, &lam_fun_t378, 1, n_v82087);
  return lam_clo_t379;
}

tll_ptr lam_fun_t386(tll_ptr __v82096, tll_env env) {
  tll_ptr UniqL_t385; tll_ptr c_v82098; tll_ptr nilUL_t384;
  tll_ptr send_ch_t383;
  instr_struct(&nilUL_t384, 11, 0);
  instr_struct(&UniqL_t385, 15, 2, nilUL_t384, 0);
  instr_send(&send_ch_t383, env[0], UniqL_t385);
  c_v82098 = send_ch_t383;
  return 0;
}

tll_ptr lam_fun_t393(tll_ptr __v82101, tll_env env) {
  tll_ptr UniqL_t392; tll_ptr c_v82103; tll_ptr consUL_t391;
  tll_ptr nilUL_t390; tll_ptr send_ch_t389;
  instr_struct(&nilUL_t390, 11, 0);
  instr_struct(&consUL_t391, 12, 2, env[0], nilUL_t390);
  instr_struct(&UniqL_t392, 15, 2, consUL_t391, 0);
  instr_send(&send_ch_t389, env[1], UniqL_t392);
  c_v82103 = send_ch_t389;
  return 0;
}

tll_ptr fork_fun_t402(tll_env env) {
  tll_ptr add_ret_t400; tll_ptr app_ret_t401; tll_ptr call_ret_t399;
  tll_ptr fork_ret_t404;
  add_ret_t400 = env[2] - 1;
  call_ret_t399 = cmsort_workerL_i53(add_ret_t400, env[1], env[0]);
  instr_app(&app_ret_t401, call_ret_t399, 0);
  instr_free_clo(call_ret_t399);
  fork_ret_t404 = app_ret_t401;
  instr_free_thread(env);
  return fork_ret_t404;
}

tll_ptr fork_fun_t408(tll_env env) {
  tll_ptr add_ret_t406; tll_ptr app_ret_t407; tll_ptr call_ret_t405;
  tll_ptr fork_ret_t410;
  add_ret_t406 = env[2] - 1;
  call_ret_t405 = cmsort_workerL_i53(add_ret_t406, env[1], env[0]);
  instr_app(&app_ret_t407, call_ret_t405, 0);
  instr_free_clo(call_ret_t405);
  fork_ret_t410 = app_ret_t407;
  instr_free_thread(env);
  return fork_ret_t410;
}

tll_ptr lam_fun_t422(tll_ptr __v82108, tll_env env) {
  tll_ptr UniqL_t419; tll_ptr __v82131; tll_ptr __v82134; tll_ptr __v82143;
  tll_ptr __v82144; tll_ptr c_v82142; tll_ptr call_ret_t417;
  tll_ptr close_tmp_t420; tll_ptr close_tmp_t421; tll_ptr fork_ch_t403;
  tll_ptr fork_ch_t409; tll_ptr msg1_v82132; tll_ptr msg2_v82135;
  tll_ptr pf1_v82138; tll_ptr pf2_v82140; tll_ptr r1_v82127;
  tll_ptr r1_v82133; tll_ptr r2_v82129; tll_ptr r2_v82136;
  tll_ptr recv_msg_t411; tll_ptr recv_msg_t413; tll_ptr send_ch_t418;
  tll_ptr switch_ret_t412; tll_ptr switch_ret_t414; tll_ptr switch_ret_t415;
  tll_ptr switch_ret_t416; tll_ptr xs1_v82137; tll_ptr xs2_v82139;
  tll_ptr zs_v82141;
  instr_fork(&fork_ch_t403, &fork_fun_t402, 2, env[1], env[3]);
  r1_v82127 = fork_ch_t403;
  instr_fork(&fork_ch_t409, &fork_fun_t408, 2, env[0], env[3]);
  r2_v82129 = fork_ch_t409;
  instr_recv(&recv_msg_t411, r1_v82127);
  __v82131 = recv_msg_t411;
  switch(((tll_node)__v82131)->tag) {
    case 0:
      msg1_v82132 = ((tll_node)__v82131)->data[0];
      r1_v82133 = ((tll_node)__v82131)->data[1];
      instr_free_struct(__v82131);
      instr_recv(&recv_msg_t413, r2_v82129);
      __v82134 = recv_msg_t413;
      switch(((tll_node)__v82134)->tag) {
        case 0:
          msg2_v82135 = ((tll_node)__v82134)->data[0];
          r2_v82136 = ((tll_node)__v82134)->data[1];
          instr_free_struct(__v82134);
          switch(((tll_node)msg1_v82132)->tag) {
            case 15:
              xs1_v82137 = ((tll_node)msg1_v82132)->data[0];
              pf1_v82138 = ((tll_node)msg1_v82132)->data[1];
              instr_free_struct(msg1_v82132);
              switch(((tll_node)msg2_v82135)->tag) {
                case 15:
                  xs2_v82139 = ((tll_node)msg2_v82135)->data[0];
                  pf2_v82140 = ((tll_node)msg2_v82135)->data[1];
                  instr_free_struct(msg2_v82135);
                  call_ret_t417 = mergeL_i47(xs1_v82137, xs2_v82139);
                  zs_v82141 = call_ret_t417;
                  instr_struct(&UniqL_t419, 15, 2, zs_v82141, 0);
                  instr_send(&send_ch_t418, env[2], UniqL_t419);
                  c_v82142 = send_ch_t418;
                  instr_close(&close_tmp_t420, r1_v82133);
                  __v82143 = close_tmp_t420;
                  instr_close(&close_tmp_t421, r2_v82136);
                  __v82144 = close_tmp_t421;
                  switch_ret_t416 = 0;
                  break;
              }
              switch_ret_t415 = switch_ret_t416;
              break;
          }
          switch_ret_t414 = switch_ret_t415;
          break;
      }
      switch_ret_t412 = switch_ret_t414;
      break;
  }
  return switch_ret_t412;
}

tll_ptr lam_fun_t427(tll_ptr __v82145, tll_env env) {
  tll_ptr UniqL_t426; tll_ptr c_v82147; tll_ptr call_ret_t425;
  tll_ptr send_ch_t424;
  call_ret_t425 = msortL_i49(env[1]);
  instr_struct(&UniqL_t426, 15, 2, call_ret_t425, 0);
  instr_send(&send_ch_t424, env[0], UniqL_t426);
  c_v82147 = send_ch_t424;
  return 0;
}

tll_ptr cmsort_workerL_i53(tll_ptr n_v82093, tll_ptr zs_v82094, tll_ptr c_v82095) {
  tll_ptr call_ret_t395; tll_ptr consUL_t396; tll_ptr consUL_t397;
  tll_ptr ifte_ret_t429; tll_ptr lam_clo_t387; tll_ptr lam_clo_t394;
  tll_ptr lam_clo_t423; tll_ptr lam_clo_t428; tll_ptr switch_ret_t382;
  tll_ptr switch_ret_t388; tll_ptr switch_ret_t398; tll_ptr xs0_v82106;
  tll_ptr ys0_v82107; tll_ptr z0_v82099; tll_ptr z1_v82104;
  tll_ptr zs0_v82100; tll_ptr zs1_v82105;
  if (n_v82093) {
    switch(((tll_node)zs_v82094)->tag) {
      case 11:
        instr_free_struct(zs_v82094);
        instr_clo(&lam_clo_t387, &lam_fun_t386, 1, c_v82095);
        switch_ret_t382 = lam_clo_t387;
        break;
      case 12:
        z0_v82099 = ((tll_node)zs_v82094)->data[0];
        zs0_v82100 = ((tll_node)zs_v82094)->data[1];
        instr_free_struct(zs_v82094);
        switch(((tll_node)zs0_v82100)->tag) {
          case 11:
            instr_free_struct(zs0_v82100);
            instr_clo(&lam_clo_t394, &lam_fun_t393, 2, z0_v82099, c_v82095);
            switch_ret_t388 = lam_clo_t394;
            break;
          case 12:
            z1_v82104 = ((tll_node)zs0_v82100)->data[0];
            zs1_v82105 = ((tll_node)zs0_v82100)->data[1];
            instr_free_struct(zs0_v82100);
            instr_struct(&consUL_t396, 12, 2, z1_v82104, zs1_v82105);
            instr_struct(&consUL_t397, 12, 2, z0_v82099, consUL_t396);
            call_ret_t395 = splitL_i45(consUL_t397);
            switch(((tll_node)call_ret_t395)->tag) {
              case 0:
                xs0_v82106 = ((tll_node)call_ret_t395)->data[0];
                ys0_v82107 = ((tll_node)call_ret_t395)->data[1];
                instr_free_struct(call_ret_t395);
                instr_clo(&lam_clo_t423, &lam_fun_t422, 4,
                          ys0_v82107, xs0_v82106, c_v82095, n_v82093);
                switch_ret_t398 = lam_clo_t423;
                break;
            }
            switch_ret_t388 = switch_ret_t398;
            break;
        }
        switch_ret_t382 = switch_ret_t388;
        break;
    }
    ifte_ret_t429 = switch_ret_t382;
  }
  else {
    instr_clo(&lam_clo_t428, &lam_fun_t427, 2, c_v82095, zs_v82094);
    ifte_ret_t429 = lam_clo_t428;
  }
  return ifte_ret_t429;
}

tll_ptr lam_fun_t431(tll_ptr c_v82153, tll_env env) {
  tll_ptr call_ret_t430;
  call_ret_t430 = cmsort_workerL_i53(env[1], env[0], c_v82153);
  return call_ret_t430;
}

tll_ptr lam_fun_t433(tll_ptr zs_v82151, tll_env env) {
  tll_ptr lam_clo_t432;
  instr_clo(&lam_clo_t432, &lam_fun_t431, 2, zs_v82151, env[0]);
  return lam_clo_t432;
}

tll_ptr lam_fun_t435(tll_ptr n_v82148, tll_env env) {
  tll_ptr lam_clo_t434;
  instr_clo(&lam_clo_t434, &lam_fun_t433, 1, n_v82148);
  return lam_clo_t434;
}

tll_ptr fork_fun_t439(tll_env env) {
  tll_ptr app_ret_t438; tll_ptr call_ret_t437; tll_ptr fork_ret_t441;
  call_ret_t437 = cmsort_workerU_i54((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t438, call_ret_t437, 0);
  instr_free_clo(call_ret_t437);
  fork_ret_t441 = app_ret_t438;
  instr_free_thread(env);
  return fork_ret_t441;
}

tll_ptr lam_fun_t445(tll_ptr __v82155, tll_env env) {
  tll_ptr __v82164; tll_ptr __v82167; tll_ptr c_v82162; tll_ptr c_v82166;
  tll_ptr close_tmp_t444; tll_ptr fork_ch_t440; tll_ptr msg_v82165;
  tll_ptr recv_msg_t442; tll_ptr switch_ret_t443;
  instr_fork(&fork_ch_t440, &fork_fun_t439, 1, env[0]);
  c_v82162 = fork_ch_t440;
  instr_recv(&recv_msg_t442, c_v82162);
  __v82164 = recv_msg_t442;
  switch(((tll_node)__v82164)->tag) {
    case 0:
      msg_v82165 = ((tll_node)__v82164)->data[0];
      c_v82166 = ((tll_node)__v82164)->data[1];
      instr_free_struct(__v82164);
      instr_close(&close_tmp_t444, c_v82166);
      __v82167 = close_tmp_t444;
      switch_ret_t443 = msg_v82165;
      break;
  }
  return switch_ret_t443;
}

tll_ptr cmsortU_i56(tll_ptr zs_v82154) {
  tll_ptr lam_clo_t446;
  instr_clo(&lam_clo_t446, &lam_fun_t445, 1, zs_v82154);
  return lam_clo_t446;
}

tll_ptr lam_fun_t448(tll_ptr zs_v82168, tll_env env) {
  tll_ptr call_ret_t447;
  call_ret_t447 = cmsortU_i56(zs_v82168);
  return call_ret_t447;
}

tll_ptr fork_fun_t452(tll_env env) {
  tll_ptr app_ret_t451; tll_ptr call_ret_t450; tll_ptr fork_ret_t454;
  call_ret_t450 = cmsort_workerL_i53((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t451, call_ret_t450, 0);
  instr_free_clo(call_ret_t450);
  fork_ret_t454 = app_ret_t451;
  instr_free_thread(env);
  return fork_ret_t454;
}

tll_ptr lam_fun_t458(tll_ptr __v82170, tll_env env) {
  tll_ptr __v82179; tll_ptr __v82182; tll_ptr c_v82177; tll_ptr c_v82181;
  tll_ptr close_tmp_t457; tll_ptr fork_ch_t453; tll_ptr msg_v82180;
  tll_ptr recv_msg_t455; tll_ptr switch_ret_t456;
  instr_fork(&fork_ch_t453, &fork_fun_t452, 1, env[0]);
  c_v82177 = fork_ch_t453;
  instr_recv(&recv_msg_t455, c_v82177);
  __v82179 = recv_msg_t455;
  switch(((tll_node)__v82179)->tag) {
    case 0:
      msg_v82180 = ((tll_node)__v82179)->data[0];
      c_v82181 = ((tll_node)__v82179)->data[1];
      instr_free_struct(__v82179);
      instr_close(&close_tmp_t457, c_v82181);
      __v82182 = close_tmp_t457;
      switch_ret_t456 = msg_v82180;
      break;
  }
  return switch_ret_t456;
}

tll_ptr cmsortL_i55(tll_ptr zs_v82169) {
  tll_ptr lam_clo_t459;
  instr_clo(&lam_clo_t459, &lam_fun_t458, 1, zs_v82169);
  return lam_clo_t459;
}

tll_ptr lam_fun_t461(tll_ptr zs_v82183, tll_env env) {
  tll_ptr call_ret_t460;
  call_ret_t460 = cmsortL_i55(zs_v82183);
  return call_ret_t460;
}

tll_ptr mkListU_i58(tll_ptr n_v82184) {
  tll_ptr add_ret_t464; tll_ptr call_ret_t463; tll_ptr consUU_t465;
  tll_ptr ifte_ret_t467; tll_ptr nilUU_t466;
  if (n_v82184) {
    add_ret_t464 = n_v82184 - 1;
    call_ret_t463 = mkListU_i58(add_ret_t464);
    instr_struct(&consUU_t465, 14, 2, n_v82184, call_ret_t463);
    ifte_ret_t467 = consUU_t465;
  }
  else {
    instr_struct(&nilUU_t466, 13, 0);
    ifte_ret_t467 = nilUU_t466;
  }
  return ifte_ret_t467;
}

tll_ptr lam_fun_t469(tll_ptr n_v82185, tll_env env) {
  tll_ptr call_ret_t468;
  call_ret_t468 = mkListU_i58(n_v82185);
  return call_ret_t468;
}

tll_ptr mkListL_i57(tll_ptr n_v82186) {
  tll_ptr add_ret_t472; tll_ptr call_ret_t471; tll_ptr consUL_t473;
  tll_ptr ifte_ret_t475; tll_ptr nilUL_t474;
  if (n_v82186) {
    add_ret_t472 = n_v82186 - 1;
    call_ret_t471 = mkListL_i57(add_ret_t472);
    instr_struct(&consUL_t473, 12, 2, n_v82186, call_ret_t471);
    ifte_ret_t475 = consUL_t473;
  }
  else {
    instr_struct(&nilUL_t474, 11, 0);
    ifte_ret_t475 = nilUL_t474;
  }
  return ifte_ret_t475;
}

tll_ptr lam_fun_t477(tll_ptr n_v82187, tll_env env) {
  tll_ptr call_ret_t476;
  call_ret_t476 = mkListL_i57(n_v82187);
  return call_ret_t476;
}

tll_ptr free_i35(tll_ptr A_v82188, tll_ptr ls_v82189) {
  tll_ptr __v82190; tll_ptr call_ret_t480; tll_ptr ls_v82191;
  tll_ptr switch_ret_t479;
  switch(((tll_node)ls_v82189)->tag) {
    case 11:
      instr_free_struct(ls_v82189);
      switch_ret_t479 = 0;
      break;
    case 12:
      __v82190 = ((tll_node)ls_v82189)->data[0];
      ls_v82191 = ((tll_node)ls_v82189)->data[1];
      instr_free_struct(ls_v82189);
      call_ret_t480 = free_i35(0, ls_v82191);
      switch_ret_t479 = call_ret_t480;
      break;
  }
  return switch_ret_t479;
}

tll_ptr lam_fun_t482(tll_ptr ls_v82194, tll_env env) {
  tll_ptr call_ret_t481;
  call_ret_t481 = free_i35(env[0], ls_v82194);
  return call_ret_t481;
}

tll_ptr lam_fun_t484(tll_ptr A_v82192, tll_env env) {
  tll_ptr lam_clo_t483;
  instr_clo(&lam_clo_t483, &lam_fun_t482, 1, A_v82192);
  return lam_clo_t483;
}

int main() {
  instr_init();
  tll_ptr __v82198; tll_ptr __v82199; tll_ptr app_ret_t488;
  tll_ptr call_ret_t486; tll_ptr call_ret_t487; tll_ptr call_ret_t490;
  tll_ptr lam_clo_t101; tll_ptr lam_clo_t111; tll_ptr lam_clo_t119;
  tll_ptr lam_clo_t12; tll_ptr lam_clo_t127; tll_ptr lam_clo_t133;
  tll_ptr lam_clo_t146; tll_ptr lam_clo_t159; tll_ptr lam_clo_t16;
  tll_ptr lam_clo_t172; tll_ptr lam_clo_t182; tll_ptr lam_clo_t192;
  tll_ptr lam_clo_t202; tll_ptr lam_clo_t212; tll_ptr lam_clo_t221;
  tll_ptr lam_clo_t230; tll_ptr lam_clo_t247; tll_ptr lam_clo_t26;
  tll_ptr lam_clo_t264; tll_ptr lam_clo_t280; tll_ptr lam_clo_t296;
  tll_ptr lam_clo_t311; tll_ptr lam_clo_t326; tll_ptr lam_clo_t37;
  tll_ptr lam_clo_t381; tll_ptr lam_clo_t436; tll_ptr lam_clo_t449;
  tll_ptr lam_clo_t462; tll_ptr lam_clo_t470; tll_ptr lam_clo_t478;
  tll_ptr lam_clo_t48; tll_ptr lam_clo_t485; tll_ptr lam_clo_t58;
  tll_ptr lam_clo_t6; tll_ptr lam_clo_t69; tll_ptr lam_clo_t74;
  tll_ptr lam_clo_t83; tll_ptr lam_clo_t92; tll_ptr msg_v82196;
  tll_ptr sorted_v82197; tll_ptr switch_ret_t489; tll_ptr test_v82195;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i59 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i60 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i61 = lam_clo_t16;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 0);
  ltenclo_i62 = lam_clo_t26;
  instr_clo(&lam_clo_t37, &lam_fun_t36, 0);
  gtenclo_i63 = lam_clo_t37;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  ltnclo_i64 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  gtnclo_i65 = lam_clo_t58;
  instr_clo(&lam_clo_t69, &lam_fun_t68, 0);
  eqnclo_i66 = lam_clo_t69;
  instr_clo(&lam_clo_t74, &lam_fun_t73, 0);
  predclo_i67 = lam_clo_t74;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i68 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i69 = lam_clo_t92;
  instr_clo(&lam_clo_t101, &lam_fun_t100, 0);
  mulnclo_i70 = lam_clo_t101;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 0);
  divnclo_i71 = lam_clo_t111;
  instr_clo(&lam_clo_t119, &lam_fun_t118, 0);
  modnclo_i72 = lam_clo_t119;
  instr_clo(&lam_clo_t127, &lam_fun_t126, 0);
  catsclo_i73 = lam_clo_t127;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 0);
  strlenclo_i74 = lam_clo_t133;
  instr_clo(&lam_clo_t146, &lam_fun_t145, 0);
  lenUUclo_i75 = lam_clo_t146;
  instr_clo(&lam_clo_t159, &lam_fun_t158, 0);
  lenULclo_i76 = lam_clo_t159;
  instr_clo(&lam_clo_t172, &lam_fun_t171, 0);
  lenLLclo_i77 = lam_clo_t172;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 0);
  appendUUclo_i78 = lam_clo_t182;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 0);
  appendULclo_i79 = lam_clo_t192;
  instr_clo(&lam_clo_t202, &lam_fun_t201, 0);
  appendLLclo_i80 = lam_clo_t202;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  readlineclo_i81 = lam_clo_t212;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 0);
  printclo_i82 = lam_clo_t221;
  instr_clo(&lam_clo_t230, &lam_fun_t229, 0);
  prerrclo_i83 = lam_clo_t230;
  instr_clo(&lam_clo_t247, &lam_fun_t246, 0);
  splitUclo_i84 = lam_clo_t247;
  instr_clo(&lam_clo_t264, &lam_fun_t263, 0);
  splitLclo_i85 = lam_clo_t264;
  instr_clo(&lam_clo_t280, &lam_fun_t279, 0);
  mergeUclo_i86 = lam_clo_t280;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 0);
  mergeLclo_i87 = lam_clo_t296;
  instr_clo(&lam_clo_t311, &lam_fun_t310, 0);
  msortUclo_i88 = lam_clo_t311;
  instr_clo(&lam_clo_t326, &lam_fun_t325, 0);
  msortLclo_i89 = lam_clo_t326;
  instr_clo(&lam_clo_t381, &lam_fun_t380, 0);
  cmsort_workerUclo_i90 = lam_clo_t381;
  instr_clo(&lam_clo_t436, &lam_fun_t435, 0);
  cmsort_workerLclo_i91 = lam_clo_t436;
  instr_clo(&lam_clo_t449, &lam_fun_t448, 0);
  cmsortUclo_i92 = lam_clo_t449;
  instr_clo(&lam_clo_t462, &lam_fun_t461, 0);
  cmsortLclo_i93 = lam_clo_t462;
  instr_clo(&lam_clo_t470, &lam_fun_t469, 0);
  mkListUclo_i94 = lam_clo_t470;
  instr_clo(&lam_clo_t478, &lam_fun_t477, 0);
  mkListLclo_i95 = lam_clo_t478;
  instr_clo(&lam_clo_t485, &lam_fun_t484, 0);
  freeclo_i96 = lam_clo_t485;
  call_ret_t486 = mkListL_i57((tll_ptr)400000);
  test_v82195 = call_ret_t486;
  call_ret_t487 = cmsortL_i55(test_v82195);
  instr_app(&app_ret_t488, call_ret_t487, 0);
  instr_free_clo(call_ret_t487);
  msg_v82196 = app_ret_t488;
  switch(((tll_node)msg_v82196)->tag) {
    case 15:
      sorted_v82197 = ((tll_node)msg_v82196)->data[0];
      __v82198 = ((tll_node)msg_v82196)->data[1];
      instr_free_struct(msg_v82196);
      call_ret_t490 = free_i35(0, sorted_v82197);
      __v82199 = call_ret_t490;
      switch_ret_t489 = 0;
      break;
  }
  return 0;
}

