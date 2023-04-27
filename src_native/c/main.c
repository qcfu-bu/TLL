#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v81824, tll_ptr b2_v81825);
tll_ptr orb_i2(tll_ptr b1_v81829, tll_ptr b2_v81830);
tll_ptr notb_i3(tll_ptr b_v81834);
tll_ptr lten_i4(tll_ptr x_v81836, tll_ptr y_v81837);
tll_ptr gten_i5(tll_ptr x_v81841, tll_ptr y_v81842);
tll_ptr ltn_i6(tll_ptr x_v81846, tll_ptr y_v81847);
tll_ptr gtn_i7(tll_ptr x_v81851, tll_ptr y_v81852);
tll_ptr eqn_i8(tll_ptr x_v81856, tll_ptr y_v81857);
tll_ptr pred_i9(tll_ptr x_v81861);
tll_ptr addn_i10(tll_ptr x_v81863, tll_ptr y_v81864);
tll_ptr subn_i11(tll_ptr x_v81868, tll_ptr y_v81869);
tll_ptr muln_i12(tll_ptr x_v81873, tll_ptr y_v81874);
tll_ptr divn_i13(tll_ptr x_v81878, tll_ptr y_v81879);
tll_ptr modn_i14(tll_ptr x_v81883, tll_ptr y_v81884);
tll_ptr cats_i15(tll_ptr s1_v81888, tll_ptr s2_v81889);
tll_ptr strlen_i16(tll_ptr s_v81895);
tll_ptr lenUU_i40(tll_ptr A_v81899, tll_ptr xs_v81900);
tll_ptr lenUL_i39(tll_ptr A_v81908, tll_ptr xs_v81909);
tll_ptr lenLL_i37(tll_ptr A_v81917, tll_ptr xs_v81918);
tll_ptr appendUU_i44(tll_ptr A_v81926, tll_ptr xs_v81927, tll_ptr ys_v81928);
tll_ptr appendUL_i43(tll_ptr A_v81937, tll_ptr xs_v81938, tll_ptr ys_v81939);
tll_ptr appendLL_i41(tll_ptr A_v81948, tll_ptr xs_v81949, tll_ptr ys_v81950);
tll_ptr readline_i25(tll_ptr __v81959);
tll_ptr print_i26(tll_ptr s_v81974);
tll_ptr prerr_i27(tll_ptr s_v81985);
tll_ptr splitU_i46(tll_ptr zs_v81996);
tll_ptr splitL_i45(tll_ptr zs_v82005);
tll_ptr mergeU_i48(tll_ptr xs_v82014, tll_ptr ys_v82015);
tll_ptr mergeL_i47(tll_ptr xs_v82023, tll_ptr ys_v82024);
tll_ptr msortU_i50(tll_ptr zs_v82032);
tll_ptr msortL_i49(tll_ptr zs_v82041);
tll_ptr cmsort_workerU_i54(tll_ptr n_v82050, tll_ptr zs_v82051, tll_ptr c_v82052);
tll_ptr cmsort_workerL_i53(tll_ptr n_v82116, tll_ptr zs_v82117, tll_ptr c_v82118);
tll_ptr cmsortU_i56(tll_ptr zs_v82182);
tll_ptr cmsortL_i55(tll_ptr zs_v82197);
tll_ptr mkListU_i58(tll_ptr n_v82212);
tll_ptr mkListL_i57(tll_ptr n_v82214);
tll_ptr free_i35(tll_ptr A_v82216, tll_ptr ls_v82217);

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

tll_ptr andb_i1(tll_ptr b1_v81824, tll_ptr b2_v81825) {
  tll_ptr ifte_ret_t1;
  if (b1_v81824) {
    ifte_ret_t1 = b2_v81825;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v81828, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v81828);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v81826, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v81826);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v81829, tll_ptr b2_v81830) {
  tll_ptr ifte_ret_t7;
  if (b1_v81829) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v81830;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v81833, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v81833);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v81831, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v81831);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v81834) {
  tll_ptr ifte_ret_t13;
  if (b_v81834) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v81835, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v81835);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v81836, tll_ptr y_v81837) {
  tll_ptr add_ret_t18; tll_ptr add_ret_t19; tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  if (x_v81836) {
    if (y_v81837) {
      add_ret_t18 = x_v81836 - 1;
      add_ret_t19 = y_v81837 - 1;
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

tll_ptr lam_fun_t23(tll_ptr y_v81840, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v81840);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v81838, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v81838);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v81841, tll_ptr y_v81842) {
  tll_ptr add_ret_t28; tll_ptr add_ret_t29; tll_ptr call_ret_t27;
  tll_ptr ifte_ret_t30; tll_ptr ifte_ret_t31; tll_ptr ifte_ret_t32;
  if (x_v81841) {
    if (y_v81842) {
      add_ret_t28 = x_v81841 - 1;
      add_ret_t29 = y_v81842 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v81842) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v81845, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v81845);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v81843, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v81843);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v81846, tll_ptr y_v81847) {
  tll_ptr add_ret_t39; tll_ptr add_ret_t40; tll_ptr call_ret_t38;
  tll_ptr ifte_ret_t41; tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t43;
  if (x_v81846) {
    if (y_v81847) {
      add_ret_t39 = x_v81846 - 1;
      add_ret_t40 = y_v81847 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v81847) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v81850, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v81850);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v81848, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v81848);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v81851, tll_ptr y_v81852) {
  tll_ptr add_ret_t50; tll_ptr add_ret_t51; tll_ptr call_ret_t49;
  tll_ptr ifte_ret_t52; tll_ptr ifte_ret_t53;
  if (x_v81851) {
    if (y_v81852) {
      add_ret_t50 = x_v81851 - 1;
      add_ret_t51 = y_v81852 - 1;
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

tll_ptr lam_fun_t55(tll_ptr y_v81855, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v81855);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v81853, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v81853);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v81856, tll_ptr y_v81857) {
  tll_ptr add_ret_t60; tll_ptr add_ret_t61; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t62; tll_ptr ifte_ret_t63; tll_ptr ifte_ret_t64;
  if (x_v81856) {
    if (y_v81857) {
      add_ret_t60 = x_v81856 - 1;
      add_ret_t61 = y_v81857 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v81857) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v81860, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v81860);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v81858, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v81858);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v81861) {
  tll_ptr add_ret_t70; tll_ptr ifte_ret_t71;
  if (x_v81861) {
    add_ret_t70 = x_v81861 - 1;
    ifte_ret_t71 = add_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v81862, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v81862);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v81863, tll_ptr y_v81864) {
  tll_ptr add_ret_t76; tll_ptr add_ret_t77; tll_ptr call_ret_t75;
  tll_ptr ifte_ret_t78;
  if (x_v81863) {
    add_ret_t76 = x_v81863 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v81864);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v81864;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v81867, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v81867);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v81865, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v81865);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v81868, tll_ptr y_v81869) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v81869) {
    call_ret_t85 = pred_i9(x_v81868);
    add_ret_t86 = y_v81869 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v81868;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v81872, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v81872);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v81870, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v81870);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v81873, tll_ptr y_v81874) {
  tll_ptr add_ret_t95; tll_ptr call_ret_t93; tll_ptr call_ret_t94;
  tll_ptr ifte_ret_t96;
  if (x_v81873) {
    add_ret_t95 = x_v81873 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v81874);
    call_ret_t93 = addn_i10(y_v81874, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v81877, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v81877);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v81875, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v81875);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v81878, tll_ptr y_v81879) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v81878, y_v81879);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v81878, y_v81879);
    call_ret_t103 = divn_i13(call_ret_t104, y_v81879);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v81882, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v81882);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v81880, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v81880);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v81883, tll_ptr y_v81884) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v81883, y_v81884);
  call_ret_t113 = muln_i12(call_ret_t114, y_v81884);
  call_ret_t112 = subn_i11(x_v81883, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v81887, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v81887);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v81885, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v81885);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v81888, tll_ptr s2_v81889) {
  tll_ptr String_t122; tll_ptr c_v81890; tll_ptr call_ret_t121;
  tll_ptr s1_v81891; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v81888)->tag) {
    case 2:
      switch_ret_t120 = s2_v81889;
      break;
    case 3:
      c_v81890 = ((tll_node)s1_v81888)->data[0];
      s1_v81891 = ((tll_node)s1_v81888)->data[1];
      call_ret_t121 = cats_i15(s1_v81891, s2_v81889);
      instr_struct(&String_t122, 3, 2, c_v81890, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v81894, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v81894);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v81892, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v81892);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v81895) {
  tll_ptr __v81896; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v81897; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v81895)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v81896 = ((tll_node)s_v81895)->data[0];
      s_v81897 = ((tll_node)s_v81895)->data[1];
      call_ret_t129 = strlen_i16(s_v81897);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v81898, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v81898);
  return call_ret_t131;
}

tll_ptr lenUU_i40(tll_ptr A_v81899, tll_ptr xs_v81900) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v81903; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v81901; tll_ptr xs_v81902; tll_ptr xs_v81904;
  switch(((tll_node)xs_v81900)->tag) {
    case 13:
      instr_struct(&nilUU_t135, 13, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 14:
      x_v81901 = ((tll_node)xs_v81900)->data[0];
      xs_v81902 = ((tll_node)xs_v81900)->data[1];
      call_ret_t137 = lenUU_i40(0, xs_v81902);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v81903 = ((tll_node)call_ret_t137)->data[0];
          xs_v81904 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v81903 + 1;
          instr_struct(&consUU_t140, 14, 2, x_v81901, xs_v81904);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v81907, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i40(env[0], xs_v81907);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v81905, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v81905);
  return lam_clo_t144;
}

tll_ptr lenUL_i39(tll_ptr A_v81908, tll_ptr xs_v81909) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v81912; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v81910; tll_ptr xs_v81911; tll_ptr xs_v81913;
  switch(((tll_node)xs_v81909)->tag) {
    case 11:
      instr_free_struct(xs_v81909);
      instr_struct(&nilUL_t148, 11, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 12:
      x_v81910 = ((tll_node)xs_v81909)->data[0];
      xs_v81911 = ((tll_node)xs_v81909)->data[1];
      instr_free_struct(xs_v81909);
      call_ret_t150 = lenUL_i39(0, xs_v81911);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v81912 = ((tll_node)call_ret_t150)->data[0];
          xs_v81913 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v81912 + 1;
          instr_struct(&consUL_t153, 12, 2, x_v81910, xs_v81913);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v81916, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i39(env[0], xs_v81916);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v81914, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v81914);
  return lam_clo_t157;
}

tll_ptr lenLL_i37(tll_ptr A_v81917, tll_ptr xs_v81918) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v81921; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v81919; tll_ptr xs_v81920; tll_ptr xs_v81922;
  switch(((tll_node)xs_v81918)->tag) {
    case 7:
      instr_free_struct(xs_v81918);
      instr_struct(&nilLL_t161, 7, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 8:
      x_v81919 = ((tll_node)xs_v81918)->data[0];
      xs_v81920 = ((tll_node)xs_v81918)->data[1];
      instr_free_struct(xs_v81918);
      call_ret_t163 = lenLL_i37(0, xs_v81920);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v81921 = ((tll_node)call_ret_t163)->data[0];
          xs_v81922 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v81921 + 1;
          instr_struct(&consLL_t166, 8, 2, x_v81919, xs_v81922);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v81925, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i37(env[0], xs_v81925);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v81923, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v81923);
  return lam_clo_t170;
}

tll_ptr appendUU_i44(tll_ptr A_v81926, tll_ptr xs_v81927, tll_ptr ys_v81928) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v81929; tll_ptr xs_v81930;
  switch(((tll_node)xs_v81927)->tag) {
    case 13:
      switch_ret_t173 = ys_v81928;
      break;
    case 14:
      x_v81929 = ((tll_node)xs_v81927)->data[0];
      xs_v81930 = ((tll_node)xs_v81927)->data[1];
      call_ret_t174 = appendUU_i44(0, xs_v81930, ys_v81928);
      instr_struct(&consUU_t175, 14, 2, x_v81929, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v81936, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i44(env[1], env[0], ys_v81936);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v81934, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v81934, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v81931, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v81931);
  return lam_clo_t180;
}

tll_ptr appendUL_i43(tll_ptr A_v81937, tll_ptr xs_v81938, tll_ptr ys_v81939) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v81940; tll_ptr xs_v81941;
  switch(((tll_node)xs_v81938)->tag) {
    case 11:
      instr_free_struct(xs_v81938);
      switch_ret_t183 = ys_v81939;
      break;
    case 12:
      x_v81940 = ((tll_node)xs_v81938)->data[0];
      xs_v81941 = ((tll_node)xs_v81938)->data[1];
      instr_free_struct(xs_v81938);
      call_ret_t184 = appendUL_i43(0, xs_v81941, ys_v81939);
      instr_struct(&consUL_t185, 12, 2, x_v81940, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v81947, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i43(env[1], env[0], ys_v81947);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v81945, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v81945, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v81942, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v81942);
  return lam_clo_t190;
}

tll_ptr appendLL_i41(tll_ptr A_v81948, tll_ptr xs_v81949, tll_ptr ys_v81950) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v81951; tll_ptr xs_v81952;
  switch(((tll_node)xs_v81949)->tag) {
    case 7:
      instr_free_struct(xs_v81949);
      switch_ret_t193 = ys_v81950;
      break;
    case 8:
      x_v81951 = ((tll_node)xs_v81949)->data[0];
      xs_v81952 = ((tll_node)xs_v81949)->data[1];
      instr_free_struct(xs_v81949);
      call_ret_t194 = appendLL_i41(0, xs_v81952, ys_v81950);
      instr_struct(&consLL_t195, 8, 2, x_v81951, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v81958, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i41(env[1], env[0], ys_v81958);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v81956, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v81956, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v81953, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v81953);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v81960, tll_env env) {
  tll_ptr __v81969; tll_ptr ch_v81967; tll_ptr ch_v81968; tll_ptr ch_v81971;
  tll_ptr ch_v81972; tll_ptr prim_ch_t203; tll_ptr recv_msg_t205;
  tll_ptr s_v81970; tll_ptr send_ch_t204; tll_ptr send_ch_t207;
  tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v81967 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v81967, (tll_ptr)1);
  ch_v81968 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v81968);
  __v81969 = recv_msg_t205;
  switch(((tll_node)__v81969)->tag) {
    case 0:
      s_v81970 = ((tll_node)__v81969)->data[0];
      ch_v81971 = ((tll_node)__v81969)->data[1];
      instr_free_struct(__v81969);
      instr_send(&send_ch_t207, ch_v81971, (tll_ptr)0);
      ch_v81972 = send_ch_t207;
      switch_ret_t206 = s_v81970;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v81959) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v81973, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v81973);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v81975, tll_env env) {
  tll_ptr ch_v81980; tll_ptr ch_v81981; tll_ptr ch_v81982; tll_ptr ch_v81983;
  tll_ptr prim_ch_t213; tll_ptr send_ch_t214; tll_ptr send_ch_t215;
  tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v81980 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v81980, (tll_ptr)1);
  ch_v81981 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v81981, env[0]);
  ch_v81982 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v81982, (tll_ptr)0);
  ch_v81983 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v81974) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v81974);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v81984, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v81984);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v81986, tll_env env) {
  tll_ptr ch_v81991; tll_ptr ch_v81992; tll_ptr ch_v81993; tll_ptr ch_v81994;
  tll_ptr prim_ch_t222; tll_ptr send_ch_t223; tll_ptr send_ch_t224;
  tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v81991 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v81991, (tll_ptr)1);
  ch_v81992 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v81992, env[0]);
  ch_v81993 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v81993, (tll_ptr)0);
  ch_v81994 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v81985) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v81985);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v81995, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v81995);
  return call_ret_t228;
}

tll_ptr splitU_i46(tll_ptr zs_v81996) {
  tll_ptr __v82001; tll_ptr call_ret_t240; tll_ptr consUU_t237;
  tll_ptr consUU_t242; tll_ptr consUU_t243; tll_ptr nilUU_t232;
  tll_ptr nilUU_t233; tll_ptr nilUU_t236; tll_ptr nilUU_t238;
  tll_ptr pair_struct_t234; tll_ptr pair_struct_t239;
  tll_ptr pair_struct_t244; tll_ptr switch_ret_t231; tll_ptr switch_ret_t235;
  tll_ptr switch_ret_t241; tll_ptr x_v81997; tll_ptr xs_v82002;
  tll_ptr y_v81999; tll_ptr ys_v82003; tll_ptr zs_v81998; tll_ptr zs_v82000;
  switch(((tll_node)zs_v81996)->tag) {
    case 13:
      instr_struct(&nilUU_t232, 13, 0);
      instr_struct(&nilUU_t233, 13, 0);
      instr_struct(&pair_struct_t234, 0, 2, nilUU_t232, nilUU_t233);
      switch_ret_t231 = pair_struct_t234;
      break;
    case 14:
      x_v81997 = ((tll_node)zs_v81996)->data[0];
      zs_v81998 = ((tll_node)zs_v81996)->data[1];
      switch(((tll_node)zs_v81998)->tag) {
        case 13:
          instr_struct(&nilUU_t236, 13, 0);
          instr_struct(&consUU_t237, 14, 2, x_v81997, nilUU_t236);
          instr_struct(&nilUU_t238, 13, 0);
          instr_struct(&pair_struct_t239, 0, 2, consUU_t237, nilUU_t238);
          switch_ret_t235 = pair_struct_t239;
          break;
        case 14:
          y_v81999 = ((tll_node)zs_v81998)->data[0];
          zs_v82000 = ((tll_node)zs_v81998)->data[1];
          call_ret_t240 = splitU_i46(zs_v82000);
          __v82001 = call_ret_t240;
          switch(((tll_node)__v82001)->tag) {
            case 0:
              xs_v82002 = ((tll_node)__v82001)->data[0];
              ys_v82003 = ((tll_node)__v82001)->data[1];
              instr_free_struct(__v82001);
              instr_struct(&consUU_t242, 14, 2, x_v81997, xs_v82002);
              instr_struct(&consUU_t243, 14, 2, y_v81999, ys_v82003);
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

tll_ptr lam_fun_t246(tll_ptr zs_v82004, tll_env env) {
  tll_ptr call_ret_t245;
  call_ret_t245 = splitU_i46(zs_v82004);
  return call_ret_t245;
}

tll_ptr splitL_i45(tll_ptr zs_v82005) {
  tll_ptr __v82010; tll_ptr call_ret_t257; tll_ptr consUL_t254;
  tll_ptr consUL_t259; tll_ptr consUL_t260; tll_ptr nilUL_t249;
  tll_ptr nilUL_t250; tll_ptr nilUL_t253; tll_ptr nilUL_t255;
  tll_ptr pair_struct_t251; tll_ptr pair_struct_t256;
  tll_ptr pair_struct_t261; tll_ptr switch_ret_t248; tll_ptr switch_ret_t252;
  tll_ptr switch_ret_t258; tll_ptr x_v82006; tll_ptr xs_v82011;
  tll_ptr y_v82008; tll_ptr ys_v82012; tll_ptr zs_v82007; tll_ptr zs_v82009;
  switch(((tll_node)zs_v82005)->tag) {
    case 11:
      instr_free_struct(zs_v82005);
      instr_struct(&nilUL_t249, 11, 0);
      instr_struct(&nilUL_t250, 11, 0);
      instr_struct(&pair_struct_t251, 0, 2, nilUL_t249, nilUL_t250);
      switch_ret_t248 = pair_struct_t251;
      break;
    case 12:
      x_v82006 = ((tll_node)zs_v82005)->data[0];
      zs_v82007 = ((tll_node)zs_v82005)->data[1];
      instr_free_struct(zs_v82005);
      switch(((tll_node)zs_v82007)->tag) {
        case 11:
          instr_free_struct(zs_v82007);
          instr_struct(&nilUL_t253, 11, 0);
          instr_struct(&consUL_t254, 12, 2, x_v82006, nilUL_t253);
          instr_struct(&nilUL_t255, 11, 0);
          instr_struct(&pair_struct_t256, 0, 2, consUL_t254, nilUL_t255);
          switch_ret_t252 = pair_struct_t256;
          break;
        case 12:
          y_v82008 = ((tll_node)zs_v82007)->data[0];
          zs_v82009 = ((tll_node)zs_v82007)->data[1];
          instr_free_struct(zs_v82007);
          call_ret_t257 = splitL_i45(zs_v82009);
          __v82010 = call_ret_t257;
          switch(((tll_node)__v82010)->tag) {
            case 0:
              xs_v82011 = ((tll_node)__v82010)->data[0];
              ys_v82012 = ((tll_node)__v82010)->data[1];
              instr_free_struct(__v82010);
              instr_struct(&consUL_t259, 12, 2, x_v82006, xs_v82011);
              instr_struct(&consUL_t260, 12, 2, y_v82008, ys_v82012);
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

tll_ptr lam_fun_t263(tll_ptr zs_v82013, tll_env env) {
  tll_ptr call_ret_t262;
  call_ret_t262 = splitL_i45(zs_v82013);
  return call_ret_t262;
}

tll_ptr mergeU_i48(tll_ptr xs_v82014, tll_ptr ys_v82015) {
  tll_ptr call_ret_t268; tll_ptr call_ret_t269; tll_ptr call_ret_t272;
  tll_ptr consUU_t267; tll_ptr consUU_t270; tll_ptr consUU_t271;
  tll_ptr consUU_t273; tll_ptr consUU_t274; tll_ptr ifte_ret_t275;
  tll_ptr switch_ret_t265; tll_ptr switch_ret_t266; tll_ptr x_v82016;
  tll_ptr xs0_v82017; tll_ptr y_v82018; tll_ptr ys0_v82019;
  switch(((tll_node)xs_v82014)->tag) {
    case 13:
      switch_ret_t265 = ys_v82015;
      break;
    case 14:
      x_v82016 = ((tll_node)xs_v82014)->data[0];
      xs0_v82017 = ((tll_node)xs_v82014)->data[1];
      switch(((tll_node)ys_v82015)->tag) {
        case 13:
          instr_struct(&consUU_t267, 14, 2, x_v82016, xs0_v82017);
          switch_ret_t266 = consUU_t267;
          break;
        case 14:
          y_v82018 = ((tll_node)ys_v82015)->data[0];
          ys0_v82019 = ((tll_node)ys_v82015)->data[1];
          call_ret_t268 = lten_i4(x_v82016, y_v82018);
          if (call_ret_t268) {
            instr_struct(&consUU_t270, 14, 2, y_v82018, ys0_v82019);
            call_ret_t269 = mergeU_i48(xs0_v82017, consUU_t270);
            instr_struct(&consUU_t271, 14, 2, x_v82016, call_ret_t269);
            ifte_ret_t275 = consUU_t271;
          }
          else {
            instr_struct(&consUU_t273, 14, 2, x_v82016, xs0_v82017);
            call_ret_t272 = mergeU_i48(consUU_t273, ys0_v82019);
            instr_struct(&consUU_t274, 14, 2, y_v82018, call_ret_t272);
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

tll_ptr lam_fun_t277(tll_ptr ys_v82022, tll_env env) {
  tll_ptr call_ret_t276;
  call_ret_t276 = mergeU_i48(env[0], ys_v82022);
  return call_ret_t276;
}

tll_ptr lam_fun_t279(tll_ptr xs_v82020, tll_env env) {
  tll_ptr lam_clo_t278;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 1, xs_v82020);
  return lam_clo_t278;
}

tll_ptr mergeL_i47(tll_ptr xs_v82023, tll_ptr ys_v82024) {
  tll_ptr call_ret_t284; tll_ptr call_ret_t285; tll_ptr call_ret_t288;
  tll_ptr consUL_t283; tll_ptr consUL_t286; tll_ptr consUL_t287;
  tll_ptr consUL_t289; tll_ptr consUL_t290; tll_ptr ifte_ret_t291;
  tll_ptr switch_ret_t281; tll_ptr switch_ret_t282; tll_ptr x_v82025;
  tll_ptr xs0_v82026; tll_ptr y_v82027; tll_ptr ys0_v82028;
  switch(((tll_node)xs_v82023)->tag) {
    case 11:
      instr_free_struct(xs_v82023);
      switch_ret_t281 = ys_v82024;
      break;
    case 12:
      x_v82025 = ((tll_node)xs_v82023)->data[0];
      xs0_v82026 = ((tll_node)xs_v82023)->data[1];
      instr_free_struct(xs_v82023);
      switch(((tll_node)ys_v82024)->tag) {
        case 11:
          instr_free_struct(ys_v82024);
          instr_struct(&consUL_t283, 12, 2, x_v82025, xs0_v82026);
          switch_ret_t282 = consUL_t283;
          break;
        case 12:
          y_v82027 = ((tll_node)ys_v82024)->data[0];
          ys0_v82028 = ((tll_node)ys_v82024)->data[1];
          instr_free_struct(ys_v82024);
          call_ret_t284 = lten_i4(x_v82025, y_v82027);
          if (call_ret_t284) {
            instr_struct(&consUL_t286, 12, 2, y_v82027, ys0_v82028);
            call_ret_t285 = mergeL_i47(xs0_v82026, consUL_t286);
            instr_struct(&consUL_t287, 12, 2, x_v82025, call_ret_t285);
            ifte_ret_t291 = consUL_t287;
          }
          else {
            instr_struct(&consUL_t289, 12, 2, x_v82025, xs0_v82026);
            call_ret_t288 = mergeL_i47(consUL_t289, ys0_v82028);
            instr_struct(&consUL_t290, 12, 2, y_v82027, call_ret_t288);
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

tll_ptr lam_fun_t293(tll_ptr ys_v82031, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = mergeL_i47(env[0], ys_v82031);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v82029, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 1, xs_v82029);
  return lam_clo_t294;
}

tll_ptr msortU_i50(tll_ptr zs_v82032) {
  tll_ptr __v82037; tll_ptr call_ret_t302; tll_ptr call_ret_t306;
  tll_ptr call_ret_t307; tll_ptr call_ret_t308; tll_ptr consUU_t301;
  tll_ptr consUU_t303; tll_ptr consUU_t304; tll_ptr nilUU_t298;
  tll_ptr nilUU_t300; tll_ptr switch_ret_t297; tll_ptr switch_ret_t299;
  tll_ptr switch_ret_t305; tll_ptr x_v82033; tll_ptr xs_v82038;
  tll_ptr y_v82035; tll_ptr ys_v82039; tll_ptr zs_v82034; tll_ptr zs_v82036;
  switch(((tll_node)zs_v82032)->tag) {
    case 13:
      instr_struct(&nilUU_t298, 13, 0);
      switch_ret_t297 = nilUU_t298;
      break;
    case 14:
      x_v82033 = ((tll_node)zs_v82032)->data[0];
      zs_v82034 = ((tll_node)zs_v82032)->data[1];
      switch(((tll_node)zs_v82034)->tag) {
        case 13:
          instr_struct(&nilUU_t300, 13, 0);
          instr_struct(&consUU_t301, 14, 2, x_v82033, nilUU_t300);
          switch_ret_t299 = consUU_t301;
          break;
        case 14:
          y_v82035 = ((tll_node)zs_v82034)->data[0];
          zs_v82036 = ((tll_node)zs_v82034)->data[1];
          instr_struct(&consUU_t303, 14, 2, y_v82035, zs_v82036);
          instr_struct(&consUU_t304, 14, 2, x_v82033, consUU_t303);
          call_ret_t302 = splitU_i46(consUU_t304);
          __v82037 = call_ret_t302;
          switch(((tll_node)__v82037)->tag) {
            case 0:
              xs_v82038 = ((tll_node)__v82037)->data[0];
              ys_v82039 = ((tll_node)__v82037)->data[1];
              instr_free_struct(__v82037);
              call_ret_t307 = msortU_i50(xs_v82038);
              call_ret_t308 = msortU_i50(ys_v82039);
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

tll_ptr lam_fun_t310(tll_ptr zs_v82040, tll_env env) {
  tll_ptr call_ret_t309;
  call_ret_t309 = msortU_i50(zs_v82040);
  return call_ret_t309;
}

tll_ptr msortL_i49(tll_ptr zs_v82041) {
  tll_ptr __v82046; tll_ptr call_ret_t317; tll_ptr call_ret_t321;
  tll_ptr call_ret_t322; tll_ptr call_ret_t323; tll_ptr consUL_t316;
  tll_ptr consUL_t318; tll_ptr consUL_t319; tll_ptr nilUL_t313;
  tll_ptr nilUL_t315; tll_ptr switch_ret_t312; tll_ptr switch_ret_t314;
  tll_ptr switch_ret_t320; tll_ptr x_v82042; tll_ptr xs_v82047;
  tll_ptr y_v82044; tll_ptr ys_v82048; tll_ptr zs_v82043; tll_ptr zs_v82045;
  switch(((tll_node)zs_v82041)->tag) {
    case 11:
      instr_free_struct(zs_v82041);
      instr_struct(&nilUL_t313, 11, 0);
      switch_ret_t312 = nilUL_t313;
      break;
    case 12:
      x_v82042 = ((tll_node)zs_v82041)->data[0];
      zs_v82043 = ((tll_node)zs_v82041)->data[1];
      instr_free_struct(zs_v82041);
      switch(((tll_node)zs_v82043)->tag) {
        case 11:
          instr_free_struct(zs_v82043);
          instr_struct(&nilUL_t315, 11, 0);
          instr_struct(&consUL_t316, 12, 2, x_v82042, nilUL_t315);
          switch_ret_t314 = consUL_t316;
          break;
        case 12:
          y_v82044 = ((tll_node)zs_v82043)->data[0];
          zs_v82045 = ((tll_node)zs_v82043)->data[1];
          instr_free_struct(zs_v82043);
          instr_struct(&consUL_t318, 12, 2, y_v82044, zs_v82045);
          instr_struct(&consUL_t319, 12, 2, x_v82042, consUL_t318);
          call_ret_t317 = splitL_i45(consUL_t319);
          __v82046 = call_ret_t317;
          switch(((tll_node)__v82046)->tag) {
            case 0:
              xs_v82047 = ((tll_node)__v82046)->data[0];
              ys_v82048 = ((tll_node)__v82046)->data[1];
              instr_free_struct(__v82046);
              call_ret_t322 = msortL_i49(xs_v82047);
              call_ret_t323 = msortL_i49(ys_v82048);
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

tll_ptr lam_fun_t325(tll_ptr zs_v82049, tll_env env) {
  tll_ptr call_ret_t324;
  call_ret_t324 = msortL_i49(zs_v82049);
  return call_ret_t324;
}

tll_ptr lam_fun_t331(tll_ptr __v82053, tll_env env) {
  tll_ptr UniqU_t330; tll_ptr c_v82055; tll_ptr nilUU_t329;
  tll_ptr send_ch_t328;
  instr_struct(&nilUU_t329, 13, 0);
  instr_struct(&UniqU_t330, 16, 2, nilUU_t329, 0);
  instr_send(&send_ch_t328, env[0], UniqU_t330);
  c_v82055 = send_ch_t328;
  return 0;
}

tll_ptr lam_fun_t338(tll_ptr __v82058, tll_env env) {
  tll_ptr UniqU_t337; tll_ptr c_v82060; tll_ptr consUU_t336;
  tll_ptr nilUU_t335; tll_ptr send_ch_t334;
  instr_struct(&nilUU_t335, 13, 0);
  instr_struct(&consUU_t336, 14, 2, env[0], nilUU_t335);
  instr_struct(&UniqU_t337, 16, 2, consUU_t336, 0);
  instr_send(&send_ch_t334, env[1], UniqU_t337);
  c_v82060 = send_ch_t334;
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

tll_ptr lam_fun_t367(tll_ptr __v82065, tll_env env) {
  tll_ptr UniqU_t364; tll_ptr __v82088; tll_ptr __v82091; tll_ptr __v82100;
  tll_ptr __v82101; tll_ptr c_v82099; tll_ptr call_ret_t362;
  tll_ptr close_tmp_t365; tll_ptr close_tmp_t366; tll_ptr fork_ch_t348;
  tll_ptr fork_ch_t354; tll_ptr msg1_v82089; tll_ptr msg2_v82092;
  tll_ptr pf1_v82095; tll_ptr pf2_v82097; tll_ptr r1_v82084;
  tll_ptr r1_v82090; tll_ptr r2_v82086; tll_ptr r2_v82093;
  tll_ptr recv_msg_t356; tll_ptr recv_msg_t358; tll_ptr send_ch_t363;
  tll_ptr switch_ret_t357; tll_ptr switch_ret_t359; tll_ptr switch_ret_t360;
  tll_ptr switch_ret_t361; tll_ptr xs1_v82094; tll_ptr xs2_v82096;
  tll_ptr zs_v82098;
  instr_fork(&fork_ch_t348, &fork_fun_t347, 2, env[1], env[3]);
  r1_v82084 = fork_ch_t348;
  instr_fork(&fork_ch_t354, &fork_fun_t353, 2, env[0], env[3]);
  r2_v82086 = fork_ch_t354;
  instr_recv(&recv_msg_t356, r1_v82084);
  __v82088 = recv_msg_t356;
  switch(((tll_node)__v82088)->tag) {
    case 0:
      msg1_v82089 = ((tll_node)__v82088)->data[0];
      r1_v82090 = ((tll_node)__v82088)->data[1];
      instr_free_struct(__v82088);
      instr_recv(&recv_msg_t358, r2_v82086);
      __v82091 = recv_msg_t358;
      switch(((tll_node)__v82091)->tag) {
        case 0:
          msg2_v82092 = ((tll_node)__v82091)->data[0];
          r2_v82093 = ((tll_node)__v82091)->data[1];
          instr_free_struct(__v82091);
          switch(((tll_node)msg1_v82089)->tag) {
            case 16:
              xs1_v82094 = ((tll_node)msg1_v82089)->data[0];
              pf1_v82095 = ((tll_node)msg1_v82089)->data[1];
              switch(((tll_node)msg2_v82092)->tag) {
                case 16:
                  xs2_v82096 = ((tll_node)msg2_v82092)->data[0];
                  pf2_v82097 = ((tll_node)msg2_v82092)->data[1];
                  call_ret_t362 = mergeU_i48(xs1_v82094, xs2_v82096);
                  zs_v82098 = call_ret_t362;
                  instr_struct(&UniqU_t364, 16, 2, zs_v82098, 0);
                  instr_send(&send_ch_t363, env[2], UniqU_t364);
                  c_v82099 = send_ch_t363;
                  instr_close(&close_tmp_t365, r1_v82090);
                  __v82100 = close_tmp_t365;
                  instr_close(&close_tmp_t366, r2_v82093);
                  __v82101 = close_tmp_t366;
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

tll_ptr lam_fun_t370(tll_ptr __v82109, tll_env env) {
  tll_ptr send_ch_t369;
  instr_send(&send_ch_t369, env[1], env[0]);
  return send_ch_t369;
}

tll_ptr lam_fun_t372(tll_ptr x_v82107, tll_env env) {
  tll_ptr lam_clo_t371;
  instr_clo(&lam_clo_t371, &lam_fun_t370, 2, x_v82107, env[0]);
  return lam_clo_t371;
}

tll_ptr lam_fun_t378(tll_ptr __v82102, tll_env env) {
  tll_ptr UniqU_t375; tll_ptr app_ret_t376; tll_ptr app_ret_t377;
  tll_ptr c_v82106; tll_ptr call_ret_t374; tll_ptr lam_clo_t373;
  instr_clo(&lam_clo_t373, &lam_fun_t372, 1, env[0]);
  call_ret_t374 = msortU_i50(env[1]);
  instr_struct(&UniqU_t375, 16, 2, call_ret_t374, 0);
  instr_app(&app_ret_t376, lam_clo_t373, UniqU_t375);
  instr_free_clo(lam_clo_t373);
  instr_app(&app_ret_t377, app_ret_t376, 0);
  instr_free_clo(app_ret_t376);
  c_v82106 = app_ret_t377;
  return 0;
}

tll_ptr cmsort_workerU_i54(tll_ptr n_v82050, tll_ptr zs_v82051, tll_ptr c_v82052) {
  tll_ptr call_ret_t340; tll_ptr consUU_t341; tll_ptr consUU_t342;
  tll_ptr ifte_ret_t380; tll_ptr lam_clo_t332; tll_ptr lam_clo_t339;
  tll_ptr lam_clo_t368; tll_ptr lam_clo_t379; tll_ptr switch_ret_t327;
  tll_ptr switch_ret_t333; tll_ptr switch_ret_t343; tll_ptr xs0_v82063;
  tll_ptr ys0_v82064; tll_ptr z0_v82056; tll_ptr z1_v82061;
  tll_ptr zs0_v82057; tll_ptr zs1_v82062;
  if (n_v82050) {
    switch(((tll_node)zs_v82051)->tag) {
      case 13:
        instr_clo(&lam_clo_t332, &lam_fun_t331, 1, c_v82052);
        switch_ret_t327 = lam_clo_t332;
        break;
      case 14:
        z0_v82056 = ((tll_node)zs_v82051)->data[0];
        zs0_v82057 = ((tll_node)zs_v82051)->data[1];
        switch(((tll_node)zs0_v82057)->tag) {
          case 13:
            instr_clo(&lam_clo_t339, &lam_fun_t338, 2, z0_v82056, c_v82052);
            switch_ret_t333 = lam_clo_t339;
            break;
          case 14:
            z1_v82061 = ((tll_node)zs0_v82057)->data[0];
            zs1_v82062 = ((tll_node)zs0_v82057)->data[1];
            instr_struct(&consUU_t341, 14, 2, z1_v82061, zs1_v82062);
            instr_struct(&consUU_t342, 14, 2, z0_v82056, consUU_t341);
            call_ret_t340 = splitU_i46(consUU_t342);
            switch(((tll_node)call_ret_t340)->tag) {
              case 0:
                xs0_v82063 = ((tll_node)call_ret_t340)->data[0];
                ys0_v82064 = ((tll_node)call_ret_t340)->data[1];
                instr_free_struct(call_ret_t340);
                instr_clo(&lam_clo_t368, &lam_fun_t367, 4,
                          ys0_v82064, xs0_v82063, c_v82052, n_v82050);
                switch_ret_t343 = lam_clo_t368;
                break;
            }
            switch_ret_t333 = switch_ret_t343;
            break;
        }
        switch_ret_t327 = switch_ret_t333;
        break;
    }
    ifte_ret_t380 = switch_ret_t327;
  }
  else {
    instr_clo(&lam_clo_t379, &lam_fun_t378, 2, c_v82052, zs_v82051);
    ifte_ret_t380 = lam_clo_t379;
  }
  return ifte_ret_t380;
}

tll_ptr lam_fun_t382(tll_ptr c_v82115, tll_env env) {
  tll_ptr call_ret_t381;
  call_ret_t381 = cmsort_workerU_i54(env[1], env[0], c_v82115);
  return call_ret_t381;
}

tll_ptr lam_fun_t384(tll_ptr zs_v82113, tll_env env) {
  tll_ptr lam_clo_t383;
  instr_clo(&lam_clo_t383, &lam_fun_t382, 2, zs_v82113, env[0]);
  return lam_clo_t383;
}

tll_ptr lam_fun_t386(tll_ptr n_v82110, tll_env env) {
  tll_ptr lam_clo_t385;
  instr_clo(&lam_clo_t385, &lam_fun_t384, 1, n_v82110);
  return lam_clo_t385;
}

tll_ptr lam_fun_t392(tll_ptr __v82119, tll_env env) {
  tll_ptr UniqL_t391; tll_ptr c_v82121; tll_ptr nilUL_t390;
  tll_ptr send_ch_t389;
  instr_struct(&nilUL_t390, 11, 0);
  instr_struct(&UniqL_t391, 15, 2, nilUL_t390, 0);
  instr_send(&send_ch_t389, env[0], UniqL_t391);
  c_v82121 = send_ch_t389;
  return 0;
}

tll_ptr lam_fun_t399(tll_ptr __v82124, tll_env env) {
  tll_ptr UniqL_t398; tll_ptr c_v82126; tll_ptr consUL_t397;
  tll_ptr nilUL_t396; tll_ptr send_ch_t395;
  instr_struct(&nilUL_t396, 11, 0);
  instr_struct(&consUL_t397, 12, 2, env[0], nilUL_t396);
  instr_struct(&UniqL_t398, 15, 2, consUL_t397, 0);
  instr_send(&send_ch_t395, env[1], UniqL_t398);
  c_v82126 = send_ch_t395;
  return 0;
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

tll_ptr fork_fun_t414(tll_env env) {
  tll_ptr add_ret_t412; tll_ptr app_ret_t413; tll_ptr call_ret_t411;
  tll_ptr fork_ret_t416;
  add_ret_t412 = env[2] - 1;
  call_ret_t411 = cmsort_workerL_i53(add_ret_t412, env[1], env[0]);
  instr_app(&app_ret_t413, call_ret_t411, 0);
  instr_free_clo(call_ret_t411);
  fork_ret_t416 = app_ret_t413;
  instr_free_thread(env);
  return fork_ret_t416;
}

tll_ptr lam_fun_t428(tll_ptr __v82131, tll_env env) {
  tll_ptr UniqL_t425; tll_ptr __v82154; tll_ptr __v82157; tll_ptr __v82166;
  tll_ptr __v82167; tll_ptr c_v82165; tll_ptr call_ret_t423;
  tll_ptr close_tmp_t426; tll_ptr close_tmp_t427; tll_ptr fork_ch_t409;
  tll_ptr fork_ch_t415; tll_ptr msg1_v82155; tll_ptr msg2_v82158;
  tll_ptr pf1_v82161; tll_ptr pf2_v82163; tll_ptr r1_v82150;
  tll_ptr r1_v82156; tll_ptr r2_v82152; tll_ptr r2_v82159;
  tll_ptr recv_msg_t417; tll_ptr recv_msg_t419; tll_ptr send_ch_t424;
  tll_ptr switch_ret_t418; tll_ptr switch_ret_t420; tll_ptr switch_ret_t421;
  tll_ptr switch_ret_t422; tll_ptr xs1_v82160; tll_ptr xs2_v82162;
  tll_ptr zs_v82164;
  instr_fork(&fork_ch_t409, &fork_fun_t408, 2, env[1], env[3]);
  r1_v82150 = fork_ch_t409;
  instr_fork(&fork_ch_t415, &fork_fun_t414, 2, env[0], env[3]);
  r2_v82152 = fork_ch_t415;
  instr_recv(&recv_msg_t417, r1_v82150);
  __v82154 = recv_msg_t417;
  switch(((tll_node)__v82154)->tag) {
    case 0:
      msg1_v82155 = ((tll_node)__v82154)->data[0];
      r1_v82156 = ((tll_node)__v82154)->data[1];
      instr_free_struct(__v82154);
      instr_recv(&recv_msg_t419, r2_v82152);
      __v82157 = recv_msg_t419;
      switch(((tll_node)__v82157)->tag) {
        case 0:
          msg2_v82158 = ((tll_node)__v82157)->data[0];
          r2_v82159 = ((tll_node)__v82157)->data[1];
          instr_free_struct(__v82157);
          switch(((tll_node)msg1_v82155)->tag) {
            case 15:
              xs1_v82160 = ((tll_node)msg1_v82155)->data[0];
              pf1_v82161 = ((tll_node)msg1_v82155)->data[1];
              instr_free_struct(msg1_v82155);
              switch(((tll_node)msg2_v82158)->tag) {
                case 15:
                  xs2_v82162 = ((tll_node)msg2_v82158)->data[0];
                  pf2_v82163 = ((tll_node)msg2_v82158)->data[1];
                  instr_free_struct(msg2_v82158);
                  call_ret_t423 = mergeL_i47(xs1_v82160, xs2_v82162);
                  zs_v82164 = call_ret_t423;
                  instr_struct(&UniqL_t425, 15, 2, zs_v82164, 0);
                  instr_send(&send_ch_t424, env[2], UniqL_t425);
                  c_v82165 = send_ch_t424;
                  instr_close(&close_tmp_t426, r1_v82156);
                  __v82166 = close_tmp_t426;
                  instr_close(&close_tmp_t427, r2_v82159);
                  __v82167 = close_tmp_t427;
                  switch_ret_t422 = 0;
                  break;
              }
              switch_ret_t421 = switch_ret_t422;
              break;
          }
          switch_ret_t420 = switch_ret_t421;
          break;
      }
      switch_ret_t418 = switch_ret_t420;
      break;
  }
  return switch_ret_t418;
}

tll_ptr lam_fun_t431(tll_ptr __v82175, tll_env env) {
  tll_ptr send_ch_t430;
  instr_send(&send_ch_t430, env[1], env[0]);
  return send_ch_t430;
}

tll_ptr lam_fun_t433(tll_ptr x_v82173, tll_env env) {
  tll_ptr lam_clo_t432;
  instr_clo(&lam_clo_t432, &lam_fun_t431, 2, x_v82173, env[0]);
  return lam_clo_t432;
}

tll_ptr lam_fun_t439(tll_ptr __v82168, tll_env env) {
  tll_ptr UniqL_t436; tll_ptr app_ret_t437; tll_ptr app_ret_t438;
  tll_ptr c_v82172; tll_ptr call_ret_t435; tll_ptr lam_clo_t434;
  instr_clo(&lam_clo_t434, &lam_fun_t433, 1, env[0]);
  call_ret_t435 = msortL_i49(env[1]);
  instr_struct(&UniqL_t436, 15, 2, call_ret_t435, 0);
  instr_app(&app_ret_t437, lam_clo_t434, UniqL_t436);
  instr_free_clo(lam_clo_t434);
  instr_app(&app_ret_t438, app_ret_t437, 0);
  instr_free_clo(app_ret_t437);
  c_v82172 = app_ret_t438;
  return 0;
}

tll_ptr cmsort_workerL_i53(tll_ptr n_v82116, tll_ptr zs_v82117, tll_ptr c_v82118) {
  tll_ptr call_ret_t401; tll_ptr consUL_t402; tll_ptr consUL_t403;
  tll_ptr ifte_ret_t441; tll_ptr lam_clo_t393; tll_ptr lam_clo_t400;
  tll_ptr lam_clo_t429; tll_ptr lam_clo_t440; tll_ptr switch_ret_t388;
  tll_ptr switch_ret_t394; tll_ptr switch_ret_t404; tll_ptr xs0_v82129;
  tll_ptr ys0_v82130; tll_ptr z0_v82122; tll_ptr z1_v82127;
  tll_ptr zs0_v82123; tll_ptr zs1_v82128;
  if (n_v82116) {
    switch(((tll_node)zs_v82117)->tag) {
      case 11:
        instr_free_struct(zs_v82117);
        instr_clo(&lam_clo_t393, &lam_fun_t392, 1, c_v82118);
        switch_ret_t388 = lam_clo_t393;
        break;
      case 12:
        z0_v82122 = ((tll_node)zs_v82117)->data[0];
        zs0_v82123 = ((tll_node)zs_v82117)->data[1];
        instr_free_struct(zs_v82117);
        switch(((tll_node)zs0_v82123)->tag) {
          case 11:
            instr_free_struct(zs0_v82123);
            instr_clo(&lam_clo_t400, &lam_fun_t399, 2, z0_v82122, c_v82118);
            switch_ret_t394 = lam_clo_t400;
            break;
          case 12:
            z1_v82127 = ((tll_node)zs0_v82123)->data[0];
            zs1_v82128 = ((tll_node)zs0_v82123)->data[1];
            instr_free_struct(zs0_v82123);
            instr_struct(&consUL_t402, 12, 2, z1_v82127, zs1_v82128);
            instr_struct(&consUL_t403, 12, 2, z0_v82122, consUL_t402);
            call_ret_t401 = splitL_i45(consUL_t403);
            switch(((tll_node)call_ret_t401)->tag) {
              case 0:
                xs0_v82129 = ((tll_node)call_ret_t401)->data[0];
                ys0_v82130 = ((tll_node)call_ret_t401)->data[1];
                instr_free_struct(call_ret_t401);
                instr_clo(&lam_clo_t429, &lam_fun_t428, 4,
                          ys0_v82130, xs0_v82129, c_v82118, n_v82116);
                switch_ret_t404 = lam_clo_t429;
                break;
            }
            switch_ret_t394 = switch_ret_t404;
            break;
        }
        switch_ret_t388 = switch_ret_t394;
        break;
    }
    ifte_ret_t441 = switch_ret_t388;
  }
  else {
    instr_clo(&lam_clo_t440, &lam_fun_t439, 2, c_v82118, zs_v82117);
    ifte_ret_t441 = lam_clo_t440;
  }
  return ifte_ret_t441;
}

tll_ptr lam_fun_t443(tll_ptr c_v82181, tll_env env) {
  tll_ptr call_ret_t442;
  call_ret_t442 = cmsort_workerL_i53(env[1], env[0], c_v82181);
  return call_ret_t442;
}

tll_ptr lam_fun_t445(tll_ptr zs_v82179, tll_env env) {
  tll_ptr lam_clo_t444;
  instr_clo(&lam_clo_t444, &lam_fun_t443, 2, zs_v82179, env[0]);
  return lam_clo_t444;
}

tll_ptr lam_fun_t447(tll_ptr n_v82176, tll_env env) {
  tll_ptr lam_clo_t446;
  instr_clo(&lam_clo_t446, &lam_fun_t445, 1, n_v82176);
  return lam_clo_t446;
}

tll_ptr fork_fun_t451(tll_env env) {
  tll_ptr app_ret_t450; tll_ptr call_ret_t449; tll_ptr fork_ret_t453;
  call_ret_t449 = cmsort_workerU_i54((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t450, call_ret_t449, 0);
  instr_free_clo(call_ret_t449);
  fork_ret_t453 = app_ret_t450;
  instr_free_thread(env);
  return fork_ret_t453;
}

tll_ptr lam_fun_t457(tll_ptr __v82183, tll_env env) {
  tll_ptr __v82192; tll_ptr __v82195; tll_ptr c_v82190; tll_ptr c_v82194;
  tll_ptr close_tmp_t456; tll_ptr fork_ch_t452; tll_ptr msg_v82193;
  tll_ptr recv_msg_t454; tll_ptr switch_ret_t455;
  instr_fork(&fork_ch_t452, &fork_fun_t451, 1, env[0]);
  c_v82190 = fork_ch_t452;
  instr_recv(&recv_msg_t454, c_v82190);
  __v82192 = recv_msg_t454;
  switch(((tll_node)__v82192)->tag) {
    case 0:
      msg_v82193 = ((tll_node)__v82192)->data[0];
      c_v82194 = ((tll_node)__v82192)->data[1];
      instr_free_struct(__v82192);
      instr_close(&close_tmp_t456, c_v82194);
      __v82195 = close_tmp_t456;
      switch_ret_t455 = msg_v82193;
      break;
  }
  return switch_ret_t455;
}

tll_ptr cmsortU_i56(tll_ptr zs_v82182) {
  tll_ptr lam_clo_t458;
  instr_clo(&lam_clo_t458, &lam_fun_t457, 1, zs_v82182);
  return lam_clo_t458;
}

tll_ptr lam_fun_t460(tll_ptr zs_v82196, tll_env env) {
  tll_ptr call_ret_t459;
  call_ret_t459 = cmsortU_i56(zs_v82196);
  return call_ret_t459;
}

tll_ptr fork_fun_t464(tll_env env) {
  tll_ptr app_ret_t463; tll_ptr call_ret_t462; tll_ptr fork_ret_t466;
  call_ret_t462 = cmsort_workerL_i53((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t463, call_ret_t462, 0);
  instr_free_clo(call_ret_t462);
  fork_ret_t466 = app_ret_t463;
  instr_free_thread(env);
  return fork_ret_t466;
}

tll_ptr lam_fun_t470(tll_ptr __v82198, tll_env env) {
  tll_ptr __v82207; tll_ptr __v82210; tll_ptr c_v82205; tll_ptr c_v82209;
  tll_ptr close_tmp_t469; tll_ptr fork_ch_t465; tll_ptr msg_v82208;
  tll_ptr recv_msg_t467; tll_ptr switch_ret_t468;
  instr_fork(&fork_ch_t465, &fork_fun_t464, 1, env[0]);
  c_v82205 = fork_ch_t465;
  instr_recv(&recv_msg_t467, c_v82205);
  __v82207 = recv_msg_t467;
  switch(((tll_node)__v82207)->tag) {
    case 0:
      msg_v82208 = ((tll_node)__v82207)->data[0];
      c_v82209 = ((tll_node)__v82207)->data[1];
      instr_free_struct(__v82207);
      instr_close(&close_tmp_t469, c_v82209);
      __v82210 = close_tmp_t469;
      switch_ret_t468 = msg_v82208;
      break;
  }
  return switch_ret_t468;
}

tll_ptr cmsortL_i55(tll_ptr zs_v82197) {
  tll_ptr lam_clo_t471;
  instr_clo(&lam_clo_t471, &lam_fun_t470, 1, zs_v82197);
  return lam_clo_t471;
}

tll_ptr lam_fun_t473(tll_ptr zs_v82211, tll_env env) {
  tll_ptr call_ret_t472;
  call_ret_t472 = cmsortL_i55(zs_v82211);
  return call_ret_t472;
}

tll_ptr mkListU_i58(tll_ptr n_v82212) {
  tll_ptr add_ret_t476; tll_ptr call_ret_t475; tll_ptr consUU_t477;
  tll_ptr ifte_ret_t479; tll_ptr nilUU_t478;
  if (n_v82212) {
    add_ret_t476 = n_v82212 - 1;
    call_ret_t475 = mkListU_i58(add_ret_t476);
    instr_struct(&consUU_t477, 14, 2, n_v82212, call_ret_t475);
    ifte_ret_t479 = consUU_t477;
  }
  else {
    instr_struct(&nilUU_t478, 13, 0);
    ifte_ret_t479 = nilUU_t478;
  }
  return ifte_ret_t479;
}

tll_ptr lam_fun_t481(tll_ptr n_v82213, tll_env env) {
  tll_ptr call_ret_t480;
  call_ret_t480 = mkListU_i58(n_v82213);
  return call_ret_t480;
}

tll_ptr mkListL_i57(tll_ptr n_v82214) {
  tll_ptr add_ret_t484; tll_ptr call_ret_t483; tll_ptr consUL_t485;
  tll_ptr ifte_ret_t487; tll_ptr nilUL_t486;
  if (n_v82214) {
    add_ret_t484 = n_v82214 - 1;
    call_ret_t483 = mkListL_i57(add_ret_t484);
    instr_struct(&consUL_t485, 12, 2, n_v82214, call_ret_t483);
    ifte_ret_t487 = consUL_t485;
  }
  else {
    instr_struct(&nilUL_t486, 11, 0);
    ifte_ret_t487 = nilUL_t486;
  }
  return ifte_ret_t487;
}

tll_ptr lam_fun_t489(tll_ptr n_v82215, tll_env env) {
  tll_ptr call_ret_t488;
  call_ret_t488 = mkListL_i57(n_v82215);
  return call_ret_t488;
}

tll_ptr free_i35(tll_ptr A_v82216, tll_ptr ls_v82217) {
  tll_ptr __v82218; tll_ptr call_ret_t492; tll_ptr ls_v82219;
  tll_ptr switch_ret_t491;
  switch(((tll_node)ls_v82217)->tag) {
    case 11:
      instr_free_struct(ls_v82217);
      switch_ret_t491 = 0;
      break;
    case 12:
      __v82218 = ((tll_node)ls_v82217)->data[0];
      ls_v82219 = ((tll_node)ls_v82217)->data[1];
      instr_free_struct(ls_v82217);
      call_ret_t492 = free_i35(0, ls_v82219);
      switch_ret_t491 = call_ret_t492;
      break;
  }
  return switch_ret_t491;
}

tll_ptr lam_fun_t494(tll_ptr ls_v82222, tll_env env) {
  tll_ptr call_ret_t493;
  call_ret_t493 = free_i35(env[0], ls_v82222);
  return call_ret_t493;
}

tll_ptr lam_fun_t496(tll_ptr A_v82220, tll_env env) {
  tll_ptr lam_clo_t495;
  instr_clo(&lam_clo_t495, &lam_fun_t494, 1, A_v82220);
  return lam_clo_t495;
}

int main() {
  instr_init();
  tll_ptr __v82226; tll_ptr __v82227; tll_ptr app_ret_t500;
  tll_ptr call_ret_t498; tll_ptr call_ret_t499; tll_ptr call_ret_t502;
  tll_ptr lam_clo_t101; tll_ptr lam_clo_t111; tll_ptr lam_clo_t119;
  tll_ptr lam_clo_t12; tll_ptr lam_clo_t127; tll_ptr lam_clo_t133;
  tll_ptr lam_clo_t146; tll_ptr lam_clo_t159; tll_ptr lam_clo_t16;
  tll_ptr lam_clo_t172; tll_ptr lam_clo_t182; tll_ptr lam_clo_t192;
  tll_ptr lam_clo_t202; tll_ptr lam_clo_t212; tll_ptr lam_clo_t221;
  tll_ptr lam_clo_t230; tll_ptr lam_clo_t247; tll_ptr lam_clo_t26;
  tll_ptr lam_clo_t264; tll_ptr lam_clo_t280; tll_ptr lam_clo_t296;
  tll_ptr lam_clo_t311; tll_ptr lam_clo_t326; tll_ptr lam_clo_t37;
  tll_ptr lam_clo_t387; tll_ptr lam_clo_t448; tll_ptr lam_clo_t461;
  tll_ptr lam_clo_t474; tll_ptr lam_clo_t48; tll_ptr lam_clo_t482;
  tll_ptr lam_clo_t490; tll_ptr lam_clo_t497; tll_ptr lam_clo_t58;
  tll_ptr lam_clo_t6; tll_ptr lam_clo_t69; tll_ptr lam_clo_t74;
  tll_ptr lam_clo_t83; tll_ptr lam_clo_t92; tll_ptr msg_v82224;
  tll_ptr sorted_v82225; tll_ptr switch_ret_t501; tll_ptr test_v82223;
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
  instr_clo(&lam_clo_t387, &lam_fun_t386, 0);
  cmsort_workerUclo_i90 = lam_clo_t387;
  instr_clo(&lam_clo_t448, &lam_fun_t447, 0);
  cmsort_workerLclo_i91 = lam_clo_t448;
  instr_clo(&lam_clo_t461, &lam_fun_t460, 0);
  cmsortUclo_i92 = lam_clo_t461;
  instr_clo(&lam_clo_t474, &lam_fun_t473, 0);
  cmsortLclo_i93 = lam_clo_t474;
  instr_clo(&lam_clo_t482, &lam_fun_t481, 0);
  mkListUclo_i94 = lam_clo_t482;
  instr_clo(&lam_clo_t490, &lam_fun_t489, 0);
  mkListLclo_i95 = lam_clo_t490;
  instr_clo(&lam_clo_t497, &lam_fun_t496, 0);
  freeclo_i96 = lam_clo_t497;
  call_ret_t498 = mkListL_i57((tll_ptr)2000000);
  test_v82223 = call_ret_t498;
  call_ret_t499 = cmsortL_i55(test_v82223);
  instr_app(&app_ret_t500, call_ret_t499, 0);
  instr_free_clo(call_ret_t499);
  msg_v82224 = app_ret_t500;
  switch(((tll_node)msg_v82224)->tag) {
    case 15:
      sorted_v82225 = ((tll_node)msg_v82224)->data[0];
      __v82226 = ((tll_node)msg_v82224)->data[1];
      instr_free_struct(msg_v82224);
      call_ret_t502 = free_i35(0, sorted_v82225);
      __v82227 = call_ret_t502;
      switch_ret_t501 = 0;
      break;
  }
  return 0;
}

