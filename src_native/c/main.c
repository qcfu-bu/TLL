#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v15824, tll_ptr b2_v15825);
tll_ptr orb_i2(tll_ptr b1_v15829, tll_ptr b2_v15830);
tll_ptr notb_i3(tll_ptr b_v15834);
tll_ptr lten_i4(tll_ptr x_v15836, tll_ptr y_v15837);
tll_ptr gten_i5(tll_ptr x_v15841, tll_ptr y_v15842);
tll_ptr ltn_i6(tll_ptr x_v15846, tll_ptr y_v15847);
tll_ptr gtn_i7(tll_ptr x_v15851, tll_ptr y_v15852);
tll_ptr eqn_i8(tll_ptr x_v15856, tll_ptr y_v15857);
tll_ptr pred_i9(tll_ptr x_v15861);
tll_ptr addn_i10(tll_ptr x_v15863, tll_ptr y_v15864);
tll_ptr subn_i11(tll_ptr x_v15868, tll_ptr y_v15869);
tll_ptr muln_i12(tll_ptr x_v15873, tll_ptr y_v15874);
tll_ptr divn_i13(tll_ptr x_v15878, tll_ptr y_v15879);
tll_ptr modn_i14(tll_ptr x_v15883, tll_ptr y_v15884);
tll_ptr cats_i15(tll_ptr s1_v15888, tll_ptr s2_v15889);
tll_ptr strlen_i16(tll_ptr s_v15895);
tll_ptr lenUU_i40(tll_ptr A_v15899, tll_ptr xs_v15900);
tll_ptr lenUL_i39(tll_ptr A_v15908, tll_ptr xs_v15909);
tll_ptr lenLL_i37(tll_ptr A_v15917, tll_ptr xs_v15918);
tll_ptr appendUU_i44(tll_ptr A_v15926, tll_ptr xs_v15927, tll_ptr ys_v15928);
tll_ptr appendUL_i43(tll_ptr A_v15937, tll_ptr xs_v15938, tll_ptr ys_v15939);
tll_ptr appendLL_i41(tll_ptr A_v15948, tll_ptr xs_v15949, tll_ptr ys_v15950);
tll_ptr readline_i25(tll_ptr __v15959);
tll_ptr print_i26(tll_ptr s_v15974);
tll_ptr prerr_i27(tll_ptr s_v15985);
tll_ptr splitU_i46(tll_ptr zs_v15996);
tll_ptr splitL_i45(tll_ptr zs_v16005);
tll_ptr mergeU_i48(tll_ptr xs_v16014, tll_ptr ys_v16015);
tll_ptr mergeL_i47(tll_ptr xs_v16023, tll_ptr ys_v16024);
tll_ptr msortU_i50(tll_ptr zs_v16032);
tll_ptr msortL_i49(tll_ptr zs_v16041);
tll_ptr cmsort_workerU_i54(tll_ptr n_v16050, tll_ptr zs_v16051, tll_ptr c_v16052);
tll_ptr cmsort_workerL_i53(tll_ptr n_v16109, tll_ptr zs_v16110, tll_ptr c_v16111);
tll_ptr cmsortU_i56(tll_ptr zs0_v16168);
tll_ptr cmsortL_i55(tll_ptr zs0_v16183);
tll_ptr mkListU_i58(tll_ptr n_v16198);
tll_ptr mkListL_i57(tll_ptr n_v16200);
tll_ptr free_i35(tll_ptr A_v16202, tll_ptr ls_v16203);

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

tll_ptr andb_i1(tll_ptr b1_v15824, tll_ptr b2_v15825) {
  tll_ptr ifte_ret_t1;
  if (b1_v15824) {
    ifte_ret_t1 = b2_v15825;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v15828, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v15828);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v15826, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v15826);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v15829, tll_ptr b2_v15830) {
  tll_ptr ifte_ret_t7;
  if (b1_v15829) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v15830;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v15833, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v15833);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v15831, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v15831);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v15834) {
  tll_ptr ifte_ret_t13;
  if (b_v15834) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v15835, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v15835);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v15836, tll_ptr y_v15837) {
  tll_ptr add_ret_t18; tll_ptr add_ret_t19; tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  if (x_v15836) {
    if (y_v15837) {
      add_ret_t18 = x_v15836 - 1;
      add_ret_t19 = y_v15837 - 1;
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

tll_ptr lam_fun_t23(tll_ptr y_v15840, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v15840);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v15838, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v15838);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v15841, tll_ptr y_v15842) {
  tll_ptr add_ret_t28; tll_ptr add_ret_t29; tll_ptr call_ret_t27;
  tll_ptr ifte_ret_t30; tll_ptr ifte_ret_t31; tll_ptr ifte_ret_t32;
  if (x_v15841) {
    if (y_v15842) {
      add_ret_t28 = x_v15841 - 1;
      add_ret_t29 = y_v15842 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v15842) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v15845, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v15845);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v15843, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v15843);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v15846, tll_ptr y_v15847) {
  tll_ptr add_ret_t39; tll_ptr add_ret_t40; tll_ptr call_ret_t38;
  tll_ptr ifte_ret_t41; tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t43;
  if (x_v15846) {
    if (y_v15847) {
      add_ret_t39 = x_v15846 - 1;
      add_ret_t40 = y_v15847 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v15847) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v15850, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v15850);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v15848, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v15848);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v15851, tll_ptr y_v15852) {
  tll_ptr add_ret_t50; tll_ptr add_ret_t51; tll_ptr call_ret_t49;
  tll_ptr ifte_ret_t52; tll_ptr ifte_ret_t53;
  if (x_v15851) {
    if (y_v15852) {
      add_ret_t50 = x_v15851 - 1;
      add_ret_t51 = y_v15852 - 1;
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

tll_ptr lam_fun_t55(tll_ptr y_v15855, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v15855);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v15853, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v15853);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v15856, tll_ptr y_v15857) {
  tll_ptr add_ret_t60; tll_ptr add_ret_t61; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t62; tll_ptr ifte_ret_t63; tll_ptr ifte_ret_t64;
  if (x_v15856) {
    if (y_v15857) {
      add_ret_t60 = x_v15856 - 1;
      add_ret_t61 = y_v15857 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v15857) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v15860, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v15860);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v15858, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v15858);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v15861) {
  tll_ptr add_ret_t70; tll_ptr ifte_ret_t71;
  if (x_v15861) {
    add_ret_t70 = x_v15861 - 1;
    ifte_ret_t71 = add_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v15862, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v15862);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v15863, tll_ptr y_v15864) {
  tll_ptr add_ret_t76; tll_ptr add_ret_t77; tll_ptr call_ret_t75;
  tll_ptr ifte_ret_t78;
  if (x_v15863) {
    add_ret_t76 = x_v15863 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v15864);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v15864;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v15867, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v15867);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v15865, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v15865);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v15868, tll_ptr y_v15869) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v15869) {
    call_ret_t85 = pred_i9(x_v15868);
    add_ret_t86 = y_v15869 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v15868;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v15872, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v15872);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v15870, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v15870);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v15873, tll_ptr y_v15874) {
  tll_ptr add_ret_t95; tll_ptr call_ret_t93; tll_ptr call_ret_t94;
  tll_ptr ifte_ret_t96;
  if (x_v15873) {
    add_ret_t95 = x_v15873 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v15874);
    call_ret_t93 = addn_i10(y_v15874, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v15877, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v15877);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v15875, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v15875);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v15878, tll_ptr y_v15879) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v15878, y_v15879);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v15878, y_v15879);
    call_ret_t103 = divn_i13(call_ret_t104, y_v15879);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v15882, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v15882);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v15880, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v15880);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v15883, tll_ptr y_v15884) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v15883, y_v15884);
  call_ret_t113 = muln_i12(call_ret_t114, y_v15884);
  call_ret_t112 = subn_i11(x_v15883, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v15887, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v15887);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v15885, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v15885);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v15888, tll_ptr s2_v15889) {
  tll_ptr String_t122; tll_ptr c_v15890; tll_ptr call_ret_t121;
  tll_ptr s1_v15891; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v15888)->tag) {
    case 2:
      switch_ret_t120 = s2_v15889;
      break;
    case 3:
      c_v15890 = ((tll_node)s1_v15888)->data[0];
      s1_v15891 = ((tll_node)s1_v15888)->data[1];
      call_ret_t121 = cats_i15(s1_v15891, s2_v15889);
      instr_struct(&String_t122, 3, 2, c_v15890, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v15894, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v15894);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v15892, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v15892);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v15895) {
  tll_ptr __v15896; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v15897; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v15895)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v15896 = ((tll_node)s_v15895)->data[0];
      s_v15897 = ((tll_node)s_v15895)->data[1];
      call_ret_t129 = strlen_i16(s_v15897);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v15898, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v15898);
  return call_ret_t131;
}

tll_ptr lenUU_i40(tll_ptr A_v15899, tll_ptr xs_v15900) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v15903; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v15901; tll_ptr xs_v15902; tll_ptr xs_v15904;
  switch(((tll_node)xs_v15900)->tag) {
    case 12:
      instr_struct(&nilUU_t135, 12, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 13:
      x_v15901 = ((tll_node)xs_v15900)->data[0];
      xs_v15902 = ((tll_node)xs_v15900)->data[1];
      call_ret_t137 = lenUU_i40(0, xs_v15902);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v15903 = ((tll_node)call_ret_t137)->data[0];
          xs_v15904 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v15903 + 1;
          instr_struct(&consUU_t140, 13, 2, x_v15901, xs_v15904);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v15907, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i40(env[0], xs_v15907);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v15905, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v15905);
  return lam_clo_t144;
}

tll_ptr lenUL_i39(tll_ptr A_v15908, tll_ptr xs_v15909) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v15912; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v15910; tll_ptr xs_v15911; tll_ptr xs_v15913;
  switch(((tll_node)xs_v15909)->tag) {
    case 10:
      instr_free_struct(xs_v15909);
      instr_struct(&nilUL_t148, 10, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 11:
      x_v15910 = ((tll_node)xs_v15909)->data[0];
      xs_v15911 = ((tll_node)xs_v15909)->data[1];
      instr_free_struct(xs_v15909);
      call_ret_t150 = lenUL_i39(0, xs_v15911);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v15912 = ((tll_node)call_ret_t150)->data[0];
          xs_v15913 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v15912 + 1;
          instr_struct(&consUL_t153, 11, 2, x_v15910, xs_v15913);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v15916, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i39(env[0], xs_v15916);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v15914, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v15914);
  return lam_clo_t157;
}

tll_ptr lenLL_i37(tll_ptr A_v15917, tll_ptr xs_v15918) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v15921; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v15919; tll_ptr xs_v15920; tll_ptr xs_v15922;
  switch(((tll_node)xs_v15918)->tag) {
    case 6:
      instr_free_struct(xs_v15918);
      instr_struct(&nilLL_t161, 6, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 7:
      x_v15919 = ((tll_node)xs_v15918)->data[0];
      xs_v15920 = ((tll_node)xs_v15918)->data[1];
      instr_free_struct(xs_v15918);
      call_ret_t163 = lenLL_i37(0, xs_v15920);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v15921 = ((tll_node)call_ret_t163)->data[0];
          xs_v15922 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v15921 + 1;
          instr_struct(&consLL_t166, 7, 2, x_v15919, xs_v15922);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v15925, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i37(env[0], xs_v15925);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v15923, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v15923);
  return lam_clo_t170;
}

tll_ptr appendUU_i44(tll_ptr A_v15926, tll_ptr xs_v15927, tll_ptr ys_v15928) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v15929; tll_ptr xs_v15930;
  switch(((tll_node)xs_v15927)->tag) {
    case 12:
      switch_ret_t173 = ys_v15928;
      break;
    case 13:
      x_v15929 = ((tll_node)xs_v15927)->data[0];
      xs_v15930 = ((tll_node)xs_v15927)->data[1];
      call_ret_t174 = appendUU_i44(0, xs_v15930, ys_v15928);
      instr_struct(&consUU_t175, 13, 2, x_v15929, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v15936, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i44(env[1], env[0], ys_v15936);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v15934, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v15934, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v15931, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v15931);
  return lam_clo_t180;
}

tll_ptr appendUL_i43(tll_ptr A_v15937, tll_ptr xs_v15938, tll_ptr ys_v15939) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v15940; tll_ptr xs_v15941;
  switch(((tll_node)xs_v15938)->tag) {
    case 10:
      instr_free_struct(xs_v15938);
      switch_ret_t183 = ys_v15939;
      break;
    case 11:
      x_v15940 = ((tll_node)xs_v15938)->data[0];
      xs_v15941 = ((tll_node)xs_v15938)->data[1];
      instr_free_struct(xs_v15938);
      call_ret_t184 = appendUL_i43(0, xs_v15941, ys_v15939);
      instr_struct(&consUL_t185, 11, 2, x_v15940, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v15947, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i43(env[1], env[0], ys_v15947);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v15945, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v15945, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v15942, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v15942);
  return lam_clo_t190;
}

tll_ptr appendLL_i41(tll_ptr A_v15948, tll_ptr xs_v15949, tll_ptr ys_v15950) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v15951; tll_ptr xs_v15952;
  switch(((tll_node)xs_v15949)->tag) {
    case 6:
      instr_free_struct(xs_v15949);
      switch_ret_t193 = ys_v15950;
      break;
    case 7:
      x_v15951 = ((tll_node)xs_v15949)->data[0];
      xs_v15952 = ((tll_node)xs_v15949)->data[1];
      instr_free_struct(xs_v15949);
      call_ret_t194 = appendLL_i41(0, xs_v15952, ys_v15950);
      instr_struct(&consLL_t195, 7, 2, x_v15951, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v15958, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i41(env[1], env[0], ys_v15958);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v15956, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v15956, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v15953, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v15953);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v15960, tll_env env) {
  tll_ptr __v15969; tll_ptr ch_v15967; tll_ptr ch_v15968; tll_ptr ch_v15971;
  tll_ptr ch_v15972; tll_ptr prim_ch_t203; tll_ptr recv_msg_t205;
  tll_ptr s_v15970; tll_ptr send_ch_t204; tll_ptr send_ch_t207;
  tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v15967 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v15967, (tll_ptr)1);
  ch_v15968 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v15968);
  __v15969 = recv_msg_t205;
  switch(((tll_node)__v15969)->tag) {
    case 0:
      s_v15970 = ((tll_node)__v15969)->data[0];
      ch_v15971 = ((tll_node)__v15969)->data[1];
      instr_free_struct(__v15969);
      instr_send(&send_ch_t207, ch_v15971, (tll_ptr)0);
      ch_v15972 = send_ch_t207;
      switch_ret_t206 = s_v15970;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v15959) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v15973, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v15973);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v15975, tll_env env) {
  tll_ptr ch_v15980; tll_ptr ch_v15981; tll_ptr ch_v15982; tll_ptr ch_v15983;
  tll_ptr prim_ch_t213; tll_ptr send_ch_t214; tll_ptr send_ch_t215;
  tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v15980 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v15980, (tll_ptr)1);
  ch_v15981 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v15981, env[0]);
  ch_v15982 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v15982, (tll_ptr)0);
  ch_v15983 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v15974) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v15974);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v15984, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v15984);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v15986, tll_env env) {
  tll_ptr ch_v15991; tll_ptr ch_v15992; tll_ptr ch_v15993; tll_ptr ch_v15994;
  tll_ptr prim_ch_t222; tll_ptr send_ch_t223; tll_ptr send_ch_t224;
  tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v15991 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v15991, (tll_ptr)1);
  ch_v15992 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v15992, env[0]);
  ch_v15993 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v15993, (tll_ptr)0);
  ch_v15994 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v15985) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v15985);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v15995, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v15995);
  return call_ret_t228;
}

tll_ptr splitU_i46(tll_ptr zs_v15996) {
  tll_ptr __v16001; tll_ptr call_ret_t240; tll_ptr consUU_t237;
  tll_ptr consUU_t242; tll_ptr consUU_t243; tll_ptr nilUU_t232;
  tll_ptr nilUU_t233; tll_ptr nilUU_t236; tll_ptr nilUU_t238;
  tll_ptr pair_struct_t234; tll_ptr pair_struct_t239;
  tll_ptr pair_struct_t244; tll_ptr switch_ret_t231; tll_ptr switch_ret_t235;
  tll_ptr switch_ret_t241; tll_ptr x_v15997; tll_ptr xs_v16002;
  tll_ptr y_v15999; tll_ptr ys_v16003; tll_ptr zs_v15998; tll_ptr zs_v16000;
  switch(((tll_node)zs_v15996)->tag) {
    case 12:
      instr_struct(&nilUU_t232, 12, 0);
      instr_struct(&nilUU_t233, 12, 0);
      instr_struct(&pair_struct_t234, 0, 2, nilUU_t232, nilUU_t233);
      switch_ret_t231 = pair_struct_t234;
      break;
    case 13:
      x_v15997 = ((tll_node)zs_v15996)->data[0];
      zs_v15998 = ((tll_node)zs_v15996)->data[1];
      switch(((tll_node)zs_v15998)->tag) {
        case 12:
          instr_struct(&nilUU_t236, 12, 0);
          instr_struct(&consUU_t237, 13, 2, x_v15997, nilUU_t236);
          instr_struct(&nilUU_t238, 12, 0);
          instr_struct(&pair_struct_t239, 0, 2, consUU_t237, nilUU_t238);
          switch_ret_t235 = pair_struct_t239;
          break;
        case 13:
          y_v15999 = ((tll_node)zs_v15998)->data[0];
          zs_v16000 = ((tll_node)zs_v15998)->data[1];
          call_ret_t240 = splitU_i46(zs_v16000);
          __v16001 = call_ret_t240;
          switch(((tll_node)__v16001)->tag) {
            case 0:
              xs_v16002 = ((tll_node)__v16001)->data[0];
              ys_v16003 = ((tll_node)__v16001)->data[1];
              instr_free_struct(__v16001);
              instr_struct(&consUU_t242, 13, 2, x_v15997, xs_v16002);
              instr_struct(&consUU_t243, 13, 2, y_v15999, ys_v16003);
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

tll_ptr lam_fun_t246(tll_ptr zs_v16004, tll_env env) {
  tll_ptr call_ret_t245;
  call_ret_t245 = splitU_i46(zs_v16004);
  return call_ret_t245;
}

tll_ptr splitL_i45(tll_ptr zs_v16005) {
  tll_ptr __v16010; tll_ptr call_ret_t257; tll_ptr consUL_t254;
  tll_ptr consUL_t259; tll_ptr consUL_t260; tll_ptr nilUL_t249;
  tll_ptr nilUL_t250; tll_ptr nilUL_t253; tll_ptr nilUL_t255;
  tll_ptr pair_struct_t251; tll_ptr pair_struct_t256;
  tll_ptr pair_struct_t261; tll_ptr switch_ret_t248; tll_ptr switch_ret_t252;
  tll_ptr switch_ret_t258; tll_ptr x_v16006; tll_ptr xs_v16011;
  tll_ptr y_v16008; tll_ptr ys_v16012; tll_ptr zs_v16007; tll_ptr zs_v16009;
  switch(((tll_node)zs_v16005)->tag) {
    case 10:
      instr_free_struct(zs_v16005);
      instr_struct(&nilUL_t249, 10, 0);
      instr_struct(&nilUL_t250, 10, 0);
      instr_struct(&pair_struct_t251, 0, 2, nilUL_t249, nilUL_t250);
      switch_ret_t248 = pair_struct_t251;
      break;
    case 11:
      x_v16006 = ((tll_node)zs_v16005)->data[0];
      zs_v16007 = ((tll_node)zs_v16005)->data[1];
      instr_free_struct(zs_v16005);
      switch(((tll_node)zs_v16007)->tag) {
        case 10:
          instr_free_struct(zs_v16007);
          instr_struct(&nilUL_t253, 10, 0);
          instr_struct(&consUL_t254, 11, 2, x_v16006, nilUL_t253);
          instr_struct(&nilUL_t255, 10, 0);
          instr_struct(&pair_struct_t256, 0, 2, consUL_t254, nilUL_t255);
          switch_ret_t252 = pair_struct_t256;
          break;
        case 11:
          y_v16008 = ((tll_node)zs_v16007)->data[0];
          zs_v16009 = ((tll_node)zs_v16007)->data[1];
          instr_free_struct(zs_v16007);
          call_ret_t257 = splitL_i45(zs_v16009);
          __v16010 = call_ret_t257;
          switch(((tll_node)__v16010)->tag) {
            case 0:
              xs_v16011 = ((tll_node)__v16010)->data[0];
              ys_v16012 = ((tll_node)__v16010)->data[1];
              instr_free_struct(__v16010);
              instr_struct(&consUL_t259, 11, 2, x_v16006, xs_v16011);
              instr_struct(&consUL_t260, 11, 2, y_v16008, ys_v16012);
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

tll_ptr lam_fun_t263(tll_ptr zs_v16013, tll_env env) {
  tll_ptr call_ret_t262;
  call_ret_t262 = splitL_i45(zs_v16013);
  return call_ret_t262;
}

tll_ptr mergeU_i48(tll_ptr xs_v16014, tll_ptr ys_v16015) {
  tll_ptr call_ret_t268; tll_ptr call_ret_t269; tll_ptr call_ret_t272;
  tll_ptr consUU_t267; tll_ptr consUU_t270; tll_ptr consUU_t271;
  tll_ptr consUU_t273; tll_ptr consUU_t274; tll_ptr ifte_ret_t275;
  tll_ptr switch_ret_t265; tll_ptr switch_ret_t266; tll_ptr x_v16016;
  tll_ptr xs0_v16017; tll_ptr y_v16018; tll_ptr ys0_v16019;
  switch(((tll_node)xs_v16014)->tag) {
    case 12:
      switch_ret_t265 = ys_v16015;
      break;
    case 13:
      x_v16016 = ((tll_node)xs_v16014)->data[0];
      xs0_v16017 = ((tll_node)xs_v16014)->data[1];
      switch(((tll_node)ys_v16015)->tag) {
        case 12:
          instr_struct(&consUU_t267, 13, 2, x_v16016, xs0_v16017);
          switch_ret_t266 = consUU_t267;
          break;
        case 13:
          y_v16018 = ((tll_node)ys_v16015)->data[0];
          ys0_v16019 = ((tll_node)ys_v16015)->data[1];
          call_ret_t268 = lten_i4(x_v16016, y_v16018);
          if (call_ret_t268) {
            instr_struct(&consUU_t270, 13, 2, y_v16018, ys0_v16019);
            call_ret_t269 = mergeU_i48(xs0_v16017, consUU_t270);
            instr_struct(&consUU_t271, 13, 2, x_v16016, call_ret_t269);
            ifte_ret_t275 = consUU_t271;
          }
          else {
            instr_struct(&consUU_t273, 13, 2, x_v16016, xs0_v16017);
            call_ret_t272 = mergeU_i48(consUU_t273, ys0_v16019);
            instr_struct(&consUU_t274, 13, 2, y_v16018, call_ret_t272);
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

tll_ptr lam_fun_t277(tll_ptr ys_v16022, tll_env env) {
  tll_ptr call_ret_t276;
  call_ret_t276 = mergeU_i48(env[0], ys_v16022);
  return call_ret_t276;
}

tll_ptr lam_fun_t279(tll_ptr xs_v16020, tll_env env) {
  tll_ptr lam_clo_t278;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 1, xs_v16020);
  return lam_clo_t278;
}

tll_ptr mergeL_i47(tll_ptr xs_v16023, tll_ptr ys_v16024) {
  tll_ptr call_ret_t284; tll_ptr call_ret_t285; tll_ptr call_ret_t288;
  tll_ptr consUL_t283; tll_ptr consUL_t286; tll_ptr consUL_t287;
  tll_ptr consUL_t289; tll_ptr consUL_t290; tll_ptr ifte_ret_t291;
  tll_ptr switch_ret_t281; tll_ptr switch_ret_t282; tll_ptr x_v16025;
  tll_ptr xs0_v16026; tll_ptr y_v16027; tll_ptr ys0_v16028;
  switch(((tll_node)xs_v16023)->tag) {
    case 10:
      instr_free_struct(xs_v16023);
      switch_ret_t281 = ys_v16024;
      break;
    case 11:
      x_v16025 = ((tll_node)xs_v16023)->data[0];
      xs0_v16026 = ((tll_node)xs_v16023)->data[1];
      instr_free_struct(xs_v16023);
      switch(((tll_node)ys_v16024)->tag) {
        case 10:
          instr_free_struct(ys_v16024);
          instr_struct(&consUL_t283, 11, 2, x_v16025, xs0_v16026);
          switch_ret_t282 = consUL_t283;
          break;
        case 11:
          y_v16027 = ((tll_node)ys_v16024)->data[0];
          ys0_v16028 = ((tll_node)ys_v16024)->data[1];
          instr_free_struct(ys_v16024);
          call_ret_t284 = lten_i4(x_v16025, y_v16027);
          if (call_ret_t284) {
            instr_struct(&consUL_t286, 11, 2, y_v16027, ys0_v16028);
            call_ret_t285 = mergeL_i47(xs0_v16026, consUL_t286);
            instr_struct(&consUL_t287, 11, 2, x_v16025, call_ret_t285);
            ifte_ret_t291 = consUL_t287;
          }
          else {
            instr_struct(&consUL_t289, 11, 2, x_v16025, xs0_v16026);
            call_ret_t288 = mergeL_i47(consUL_t289, ys0_v16028);
            instr_struct(&consUL_t290, 11, 2, y_v16027, call_ret_t288);
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

tll_ptr lam_fun_t293(tll_ptr ys_v16031, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = mergeL_i47(env[0], ys_v16031);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v16029, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 1, xs_v16029);
  return lam_clo_t294;
}

tll_ptr msortU_i50(tll_ptr zs_v16032) {
  tll_ptr __v16037; tll_ptr call_ret_t302; tll_ptr call_ret_t306;
  tll_ptr call_ret_t307; tll_ptr call_ret_t308; tll_ptr consUU_t301;
  tll_ptr consUU_t303; tll_ptr consUU_t304; tll_ptr nilUU_t298;
  tll_ptr nilUU_t300; tll_ptr switch_ret_t297; tll_ptr switch_ret_t299;
  tll_ptr switch_ret_t305; tll_ptr x_v16033; tll_ptr xs_v16038;
  tll_ptr y_v16035; tll_ptr ys_v16039; tll_ptr zs_v16034; tll_ptr zs_v16036;
  switch(((tll_node)zs_v16032)->tag) {
    case 12:
      instr_struct(&nilUU_t298, 12, 0);
      switch_ret_t297 = nilUU_t298;
      break;
    case 13:
      x_v16033 = ((tll_node)zs_v16032)->data[0];
      zs_v16034 = ((tll_node)zs_v16032)->data[1];
      switch(((tll_node)zs_v16034)->tag) {
        case 12:
          instr_struct(&nilUU_t300, 12, 0);
          instr_struct(&consUU_t301, 13, 2, x_v16033, nilUU_t300);
          switch_ret_t299 = consUU_t301;
          break;
        case 13:
          y_v16035 = ((tll_node)zs_v16034)->data[0];
          zs_v16036 = ((tll_node)zs_v16034)->data[1];
          instr_struct(&consUU_t303, 13, 2, y_v16035, zs_v16036);
          instr_struct(&consUU_t304, 13, 2, x_v16033, consUU_t303);
          call_ret_t302 = splitU_i46(consUU_t304);
          __v16037 = call_ret_t302;
          switch(((tll_node)__v16037)->tag) {
            case 0:
              xs_v16038 = ((tll_node)__v16037)->data[0];
              ys_v16039 = ((tll_node)__v16037)->data[1];
              instr_free_struct(__v16037);
              call_ret_t307 = msortU_i50(xs_v16038);
              call_ret_t308 = msortU_i50(ys_v16039);
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

tll_ptr lam_fun_t310(tll_ptr zs_v16040, tll_env env) {
  tll_ptr call_ret_t309;
  call_ret_t309 = msortU_i50(zs_v16040);
  return call_ret_t309;
}

tll_ptr msortL_i49(tll_ptr zs_v16041) {
  tll_ptr __v16046; tll_ptr call_ret_t317; tll_ptr call_ret_t321;
  tll_ptr call_ret_t322; tll_ptr call_ret_t323; tll_ptr consUL_t316;
  tll_ptr consUL_t318; tll_ptr consUL_t319; tll_ptr nilUL_t313;
  tll_ptr nilUL_t315; tll_ptr switch_ret_t312; tll_ptr switch_ret_t314;
  tll_ptr switch_ret_t320; tll_ptr x_v16042; tll_ptr xs_v16047;
  tll_ptr y_v16044; tll_ptr ys_v16048; tll_ptr zs_v16043; tll_ptr zs_v16045;
  switch(((tll_node)zs_v16041)->tag) {
    case 10:
      instr_free_struct(zs_v16041);
      instr_struct(&nilUL_t313, 10, 0);
      switch_ret_t312 = nilUL_t313;
      break;
    case 11:
      x_v16042 = ((tll_node)zs_v16041)->data[0];
      zs_v16043 = ((tll_node)zs_v16041)->data[1];
      instr_free_struct(zs_v16041);
      switch(((tll_node)zs_v16043)->tag) {
        case 10:
          instr_free_struct(zs_v16043);
          instr_struct(&nilUL_t315, 10, 0);
          instr_struct(&consUL_t316, 11, 2, x_v16042, nilUL_t315);
          switch_ret_t314 = consUL_t316;
          break;
        case 11:
          y_v16044 = ((tll_node)zs_v16043)->data[0];
          zs_v16045 = ((tll_node)zs_v16043)->data[1];
          instr_free_struct(zs_v16043);
          instr_struct(&consUL_t318, 11, 2, y_v16044, zs_v16045);
          instr_struct(&consUL_t319, 11, 2, x_v16042, consUL_t318);
          call_ret_t317 = splitL_i45(consUL_t319);
          __v16046 = call_ret_t317;
          switch(((tll_node)__v16046)->tag) {
            case 0:
              xs_v16047 = ((tll_node)__v16046)->data[0];
              ys_v16048 = ((tll_node)__v16046)->data[1];
              instr_free_struct(__v16046);
              call_ret_t322 = msortL_i49(xs_v16047);
              call_ret_t323 = msortL_i49(ys_v16048);
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

tll_ptr lam_fun_t325(tll_ptr zs_v16049, tll_env env) {
  tll_ptr call_ret_t324;
  call_ret_t324 = msortL_i49(zs_v16049);
  return call_ret_t324;
}

tll_ptr lam_fun_t330(tll_ptr __v16053, tll_env env) {
  tll_ptr c_v16055; tll_ptr nilUU_t329; tll_ptr send_ch_t328;
  instr_struct(&nilUU_t329, 12, 0);
  instr_send(&send_ch_t328, env[0], nilUU_t329);
  c_v16055 = send_ch_t328;
  return 0;
}

tll_ptr lam_fun_t335(tll_ptr __v16058, tll_env env) {
  tll_ptr c_v16060; tll_ptr nilUU_t334; tll_ptr send_ch_t333;
  instr_struct(&nilUU_t334, 12, 0);
  instr_send(&send_ch_t333, env[0], nilUU_t334);
  c_v16060 = send_ch_t333;
  return 0;
}

tll_ptr fork_fun_t344(tll_env env) {
  tll_ptr add_ret_t342; tll_ptr app_ret_t343; tll_ptr call_ret_t341;
  tll_ptr fork_ret_t346;
  add_ret_t342 = env[2] - 1;
  call_ret_t341 = cmsort_workerU_i54(add_ret_t342, env[1], env[0]);
  instr_app(&app_ret_t343, call_ret_t341, 0);
  instr_free_clo(call_ret_t341);
  fork_ret_t346 = app_ret_t343;
  instr_free_thread(env);
  return fork_ret_t346;
}

tll_ptr fork_fun_t350(tll_env env) {
  tll_ptr add_ret_t348; tll_ptr app_ret_t349; tll_ptr call_ret_t347;
  tll_ptr fork_ret_t352;
  add_ret_t348 = env[2] - 1;
  call_ret_t347 = cmsort_workerU_i54(add_ret_t348, env[1], env[0]);
  instr_app(&app_ret_t349, call_ret_t347, 0);
  instr_free_clo(call_ret_t347);
  fork_ret_t352 = app_ret_t349;
  instr_free_thread(env);
  return fork_ret_t352;
}

tll_ptr lam_fun_t361(tll_ptr __v16066, tll_env env) {
  tll_ptr __v16085; tll_ptr __v16088; tll_ptr __v16093; tll_ptr __v16094;
  tll_ptr c_v16092; tll_ptr call_ret_t357; tll_ptr close_tmp_t359;
  tll_ptr close_tmp_t360; tll_ptr fork_ch_t345; tll_ptr fork_ch_t351;
  tll_ptr r1_v16081; tll_ptr r1_v16087; tll_ptr r2_v16083; tll_ptr r2_v16090;
  tll_ptr recv_msg_t353; tll_ptr recv_msg_t355; tll_ptr send_ch_t358;
  tll_ptr switch_ret_t354; tll_ptr switch_ret_t356; tll_ptr xs1_v16086;
  tll_ptr ys1_v16089; tll_ptr zs_v16091;
  instr_fork(&fork_ch_t345, &fork_fun_t344, 2, env[1], env[3]);
  r1_v16081 = fork_ch_t345;
  instr_fork(&fork_ch_t351, &fork_fun_t350, 2, env[0], env[3]);
  r2_v16083 = fork_ch_t351;
  instr_recv(&recv_msg_t353, r1_v16081);
  __v16085 = recv_msg_t353;
  switch(((tll_node)__v16085)->tag) {
    case 0:
      xs1_v16086 = ((tll_node)__v16085)->data[0];
      r1_v16087 = ((tll_node)__v16085)->data[1];
      instr_free_struct(__v16085);
      instr_recv(&recv_msg_t355, r2_v16083);
      __v16088 = recv_msg_t355;
      switch(((tll_node)__v16088)->tag) {
        case 0:
          ys1_v16089 = ((tll_node)__v16088)->data[0];
          r2_v16090 = ((tll_node)__v16088)->data[1];
          instr_free_struct(__v16088);
          call_ret_t357 = mergeU_i48(xs1_v16086, ys1_v16089);
          zs_v16091 = call_ret_t357;
          instr_send(&send_ch_t358, env[2], zs_v16091);
          c_v16092 = send_ch_t358;
          instr_close(&close_tmp_t359, r1_v16087);
          __v16093 = close_tmp_t359;
          instr_close(&close_tmp_t360, r2_v16090);
          __v16094 = close_tmp_t360;
          switch_ret_t356 = 0;
          break;
      }
      switch_ret_t354 = switch_ret_t356;
      break;
  }
  return switch_ret_t354;
}

tll_ptr lam_fun_t364(tll_ptr __v16102, tll_env env) {
  tll_ptr send_ch_t363;
  instr_send(&send_ch_t363, env[1], env[0]);
  return send_ch_t363;
}

tll_ptr lam_fun_t366(tll_ptr x_v16100, tll_env env) {
  tll_ptr lam_clo_t365;
  instr_clo(&lam_clo_t365, &lam_fun_t364, 2, x_v16100, env[0]);
  return lam_clo_t365;
}

tll_ptr lam_fun_t371(tll_ptr __v16095, tll_env env) {
  tll_ptr app_ret_t369; tll_ptr app_ret_t370; tll_ptr c_v16099;
  tll_ptr call_ret_t368; tll_ptr lam_clo_t367;
  instr_clo(&lam_clo_t367, &lam_fun_t366, 1, env[0]);
  call_ret_t368 = msortU_i50(env[1]);
  instr_app(&app_ret_t369, lam_clo_t367, call_ret_t368);
  instr_free_clo(lam_clo_t367);
  instr_app(&app_ret_t370, app_ret_t369, 0);
  instr_free_clo(app_ret_t369);
  c_v16099 = app_ret_t370;
  return 0;
}

tll_ptr cmsort_workerU_i54(tll_ptr n_v16050, tll_ptr zs_v16051, tll_ptr c_v16052) {
  tll_ptr __v16063; tll_ptr call_ret_t337; tll_ptr consUU_t338;
  tll_ptr consUU_t339; tll_ptr ifte_ret_t373; tll_ptr lam_clo_t331;
  tll_ptr lam_clo_t336; tll_ptr lam_clo_t362; tll_ptr lam_clo_t372;
  tll_ptr switch_ret_t327; tll_ptr switch_ret_t332; tll_ptr switch_ret_t340;
  tll_ptr xs0_v16064; tll_ptr ys0_v16065; tll_ptr z0_v16056;
  tll_ptr z1_v16061; tll_ptr zs0_v16057; tll_ptr zs1_v16062;
  if (n_v16050) {
    switch(((tll_node)zs_v16051)->tag) {
      case 12:
        instr_clo(&lam_clo_t331, &lam_fun_t330, 1, c_v16052);
        switch_ret_t327 = lam_clo_t331;
        break;
      case 13:
        z0_v16056 = ((tll_node)zs_v16051)->data[0];
        zs0_v16057 = ((tll_node)zs_v16051)->data[1];
        switch(((tll_node)zs0_v16057)->tag) {
          case 12:
            instr_clo(&lam_clo_t336, &lam_fun_t335, 1, c_v16052);
            switch_ret_t332 = lam_clo_t336;
            break;
          case 13:
            z1_v16061 = ((tll_node)zs0_v16057)->data[0];
            zs1_v16062 = ((tll_node)zs0_v16057)->data[1];
            instr_struct(&consUU_t338, 13, 2, z1_v16061, zs1_v16062);
            instr_struct(&consUU_t339, 13, 2, z0_v16056, consUU_t338);
            call_ret_t337 = splitU_i46(consUU_t339);
            __v16063 = call_ret_t337;
            switch(((tll_node)__v16063)->tag) {
              case 0:
                xs0_v16064 = ((tll_node)__v16063)->data[0];
                ys0_v16065 = ((tll_node)__v16063)->data[1];
                instr_free_struct(__v16063);
                instr_clo(&lam_clo_t362, &lam_fun_t361, 4,
                          ys0_v16065, xs0_v16064, c_v16052, n_v16050);
                switch_ret_t340 = lam_clo_t362;
                break;
            }
            switch_ret_t332 = switch_ret_t340;
            break;
        }
        switch_ret_t327 = switch_ret_t332;
        break;
    }
    ifte_ret_t373 = switch_ret_t327;
  }
  else {
    instr_clo(&lam_clo_t372, &lam_fun_t371, 2, c_v16052, zs_v16051);
    ifte_ret_t373 = lam_clo_t372;
  }
  return ifte_ret_t373;
}

tll_ptr lam_fun_t375(tll_ptr c_v16108, tll_env env) {
  tll_ptr call_ret_t374;
  call_ret_t374 = cmsort_workerU_i54(env[1], env[0], c_v16108);
  return call_ret_t374;
}

tll_ptr lam_fun_t377(tll_ptr zs_v16106, tll_env env) {
  tll_ptr lam_clo_t376;
  instr_clo(&lam_clo_t376, &lam_fun_t375, 2, zs_v16106, env[0]);
  return lam_clo_t376;
}

tll_ptr lam_fun_t379(tll_ptr n_v16103, tll_env env) {
  tll_ptr lam_clo_t378;
  instr_clo(&lam_clo_t378, &lam_fun_t377, 1, n_v16103);
  return lam_clo_t378;
}

tll_ptr lam_fun_t384(tll_ptr __v16112, tll_env env) {
  tll_ptr c_v16114; tll_ptr nilUL_t383; tll_ptr send_ch_t382;
  instr_struct(&nilUL_t383, 10, 0);
  instr_send(&send_ch_t382, env[0], nilUL_t383);
  c_v16114 = send_ch_t382;
  return 0;
}

tll_ptr lam_fun_t389(tll_ptr __v16117, tll_env env) {
  tll_ptr c_v16119; tll_ptr nilUL_t388; tll_ptr send_ch_t387;
  instr_struct(&nilUL_t388, 10, 0);
  instr_send(&send_ch_t387, env[0], nilUL_t388);
  c_v16119 = send_ch_t387;
  return 0;
}

tll_ptr fork_fun_t398(tll_env env) {
  tll_ptr add_ret_t396; tll_ptr app_ret_t397; tll_ptr call_ret_t395;
  tll_ptr fork_ret_t400;
  add_ret_t396 = env[2] - 1;
  call_ret_t395 = cmsort_workerL_i53(add_ret_t396, env[1], env[0]);
  instr_app(&app_ret_t397, call_ret_t395, 0);
  instr_free_clo(call_ret_t395);
  fork_ret_t400 = app_ret_t397;
  instr_free_thread(env);
  return fork_ret_t400;
}

tll_ptr fork_fun_t404(tll_env env) {
  tll_ptr add_ret_t402; tll_ptr app_ret_t403; tll_ptr call_ret_t401;
  tll_ptr fork_ret_t406;
  add_ret_t402 = env[2] - 1;
  call_ret_t401 = cmsort_workerL_i53(add_ret_t402, env[1], env[0]);
  instr_app(&app_ret_t403, call_ret_t401, 0);
  instr_free_clo(call_ret_t401);
  fork_ret_t406 = app_ret_t403;
  instr_free_thread(env);
  return fork_ret_t406;
}

tll_ptr lam_fun_t415(tll_ptr __v16125, tll_env env) {
  tll_ptr __v16144; tll_ptr __v16147; tll_ptr __v16152; tll_ptr __v16153;
  tll_ptr c_v16151; tll_ptr call_ret_t411; tll_ptr close_tmp_t413;
  tll_ptr close_tmp_t414; tll_ptr fork_ch_t399; tll_ptr fork_ch_t405;
  tll_ptr r1_v16140; tll_ptr r1_v16146; tll_ptr r2_v16142; tll_ptr r2_v16149;
  tll_ptr recv_msg_t407; tll_ptr recv_msg_t409; tll_ptr send_ch_t412;
  tll_ptr switch_ret_t408; tll_ptr switch_ret_t410; tll_ptr xs1_v16145;
  tll_ptr ys1_v16148; tll_ptr zs_v16150;
  instr_fork(&fork_ch_t399, &fork_fun_t398, 2, env[1], env[3]);
  r1_v16140 = fork_ch_t399;
  instr_fork(&fork_ch_t405, &fork_fun_t404, 2, env[0], env[3]);
  r2_v16142 = fork_ch_t405;
  instr_recv(&recv_msg_t407, r1_v16140);
  __v16144 = recv_msg_t407;
  switch(((tll_node)__v16144)->tag) {
    case 0:
      xs1_v16145 = ((tll_node)__v16144)->data[0];
      r1_v16146 = ((tll_node)__v16144)->data[1];
      instr_free_struct(__v16144);
      instr_recv(&recv_msg_t409, r2_v16142);
      __v16147 = recv_msg_t409;
      switch(((tll_node)__v16147)->tag) {
        case 0:
          ys1_v16148 = ((tll_node)__v16147)->data[0];
          r2_v16149 = ((tll_node)__v16147)->data[1];
          instr_free_struct(__v16147);
          call_ret_t411 = mergeL_i47(xs1_v16145, ys1_v16148);
          zs_v16150 = call_ret_t411;
          instr_send(&send_ch_t412, env[2], zs_v16150);
          c_v16151 = send_ch_t412;
          instr_close(&close_tmp_t413, r1_v16146);
          __v16152 = close_tmp_t413;
          instr_close(&close_tmp_t414, r2_v16149);
          __v16153 = close_tmp_t414;
          switch_ret_t410 = 0;
          break;
      }
      switch_ret_t408 = switch_ret_t410;
      break;
  }
  return switch_ret_t408;
}

tll_ptr lam_fun_t418(tll_ptr __v16161, tll_env env) {
  tll_ptr send_ch_t417;
  instr_send(&send_ch_t417, env[1], env[0]);
  return send_ch_t417;
}

tll_ptr lam_fun_t420(tll_ptr x_v16159, tll_env env) {
  tll_ptr lam_clo_t419;
  instr_clo(&lam_clo_t419, &lam_fun_t418, 2, x_v16159, env[0]);
  return lam_clo_t419;
}

tll_ptr lam_fun_t425(tll_ptr __v16154, tll_env env) {
  tll_ptr app_ret_t423; tll_ptr app_ret_t424; tll_ptr c_v16158;
  tll_ptr call_ret_t422; tll_ptr lam_clo_t421;
  instr_clo(&lam_clo_t421, &lam_fun_t420, 1, env[0]);
  call_ret_t422 = msortL_i49(env[1]);
  instr_app(&app_ret_t423, lam_clo_t421, call_ret_t422);
  instr_free_clo(lam_clo_t421);
  instr_app(&app_ret_t424, app_ret_t423, 0);
  instr_free_clo(app_ret_t423);
  c_v16158 = app_ret_t424;
  return 0;
}

tll_ptr cmsort_workerL_i53(tll_ptr n_v16109, tll_ptr zs_v16110, tll_ptr c_v16111) {
  tll_ptr __v16122; tll_ptr call_ret_t391; tll_ptr consUL_t392;
  tll_ptr consUL_t393; tll_ptr ifte_ret_t427; tll_ptr lam_clo_t385;
  tll_ptr lam_clo_t390; tll_ptr lam_clo_t416; tll_ptr lam_clo_t426;
  tll_ptr switch_ret_t381; tll_ptr switch_ret_t386; tll_ptr switch_ret_t394;
  tll_ptr xs0_v16123; tll_ptr ys0_v16124; tll_ptr z0_v16115;
  tll_ptr z1_v16120; tll_ptr zs0_v16116; tll_ptr zs1_v16121;
  if (n_v16109) {
    switch(((tll_node)zs_v16110)->tag) {
      case 10:
        instr_free_struct(zs_v16110);
        instr_clo(&lam_clo_t385, &lam_fun_t384, 1, c_v16111);
        switch_ret_t381 = lam_clo_t385;
        break;
      case 11:
        z0_v16115 = ((tll_node)zs_v16110)->data[0];
        zs0_v16116 = ((tll_node)zs_v16110)->data[1];
        instr_free_struct(zs_v16110);
        switch(((tll_node)zs0_v16116)->tag) {
          case 10:
            instr_free_struct(zs0_v16116);
            instr_clo(&lam_clo_t390, &lam_fun_t389, 1, c_v16111);
            switch_ret_t386 = lam_clo_t390;
            break;
          case 11:
            z1_v16120 = ((tll_node)zs0_v16116)->data[0];
            zs1_v16121 = ((tll_node)zs0_v16116)->data[1];
            instr_free_struct(zs0_v16116);
            instr_struct(&consUL_t392, 11, 2, z1_v16120, zs1_v16121);
            instr_struct(&consUL_t393, 11, 2, z0_v16115, consUL_t392);
            call_ret_t391 = splitL_i45(consUL_t393);
            __v16122 = call_ret_t391;
            switch(((tll_node)__v16122)->tag) {
              case 0:
                xs0_v16123 = ((tll_node)__v16122)->data[0];
                ys0_v16124 = ((tll_node)__v16122)->data[1];
                instr_free_struct(__v16122);
                instr_clo(&lam_clo_t416, &lam_fun_t415, 4,
                          ys0_v16124, xs0_v16123, c_v16111, n_v16109);
                switch_ret_t394 = lam_clo_t416;
                break;
            }
            switch_ret_t386 = switch_ret_t394;
            break;
        }
        switch_ret_t381 = switch_ret_t386;
        break;
    }
    ifte_ret_t427 = switch_ret_t381;
  }
  else {
    instr_clo(&lam_clo_t426, &lam_fun_t425, 2, c_v16111, zs_v16110);
    ifte_ret_t427 = lam_clo_t426;
  }
  return ifte_ret_t427;
}

tll_ptr lam_fun_t429(tll_ptr c_v16167, tll_env env) {
  tll_ptr call_ret_t428;
  call_ret_t428 = cmsort_workerL_i53(env[1], env[0], c_v16167);
  return call_ret_t428;
}

tll_ptr lam_fun_t431(tll_ptr zs_v16165, tll_env env) {
  tll_ptr lam_clo_t430;
  instr_clo(&lam_clo_t430, &lam_fun_t429, 2, zs_v16165, env[0]);
  return lam_clo_t430;
}

tll_ptr lam_fun_t433(tll_ptr n_v16162, tll_env env) {
  tll_ptr lam_clo_t432;
  instr_clo(&lam_clo_t432, &lam_fun_t431, 1, n_v16162);
  return lam_clo_t432;
}

tll_ptr fork_fun_t437(tll_env env) {
  tll_ptr app_ret_t436; tll_ptr call_ret_t435; tll_ptr fork_ret_t439;
  call_ret_t435 = cmsort_workerU_i54((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t436, call_ret_t435, 0);
  instr_free_clo(call_ret_t435);
  fork_ret_t439 = app_ret_t436;
  instr_free_thread(env);
  return fork_ret_t439;
}

tll_ptr lam_fun_t443(tll_ptr __v16169, tll_env env) {
  tll_ptr __v16178; tll_ptr __v16181; tll_ptr c_v16176; tll_ptr c_v16180;
  tll_ptr close_tmp_t442; tll_ptr fork_ch_t438; tll_ptr recv_msg_t440;
  tll_ptr switch_ret_t441; tll_ptr zs1_v16179;
  instr_fork(&fork_ch_t438, &fork_fun_t437, 1, env[0]);
  c_v16176 = fork_ch_t438;
  instr_recv(&recv_msg_t440, c_v16176);
  __v16178 = recv_msg_t440;
  switch(((tll_node)__v16178)->tag) {
    case 0:
      zs1_v16179 = ((tll_node)__v16178)->data[0];
      c_v16180 = ((tll_node)__v16178)->data[1];
      instr_free_struct(__v16178);
      instr_close(&close_tmp_t442, c_v16180);
      __v16181 = close_tmp_t442;
      switch_ret_t441 = zs1_v16179;
      break;
  }
  return switch_ret_t441;
}

tll_ptr cmsortU_i56(tll_ptr zs0_v16168) {
  tll_ptr lam_clo_t444;
  instr_clo(&lam_clo_t444, &lam_fun_t443, 1, zs0_v16168);
  return lam_clo_t444;
}

tll_ptr lam_fun_t446(tll_ptr zs0_v16182, tll_env env) {
  tll_ptr call_ret_t445;
  call_ret_t445 = cmsortU_i56(zs0_v16182);
  return call_ret_t445;
}

tll_ptr fork_fun_t450(tll_env env) {
  tll_ptr app_ret_t449; tll_ptr call_ret_t448; tll_ptr fork_ret_t452;
  call_ret_t448 = cmsort_workerL_i53((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t449, call_ret_t448, 0);
  instr_free_clo(call_ret_t448);
  fork_ret_t452 = app_ret_t449;
  instr_free_thread(env);
  return fork_ret_t452;
}

tll_ptr lam_fun_t456(tll_ptr __v16184, tll_env env) {
  tll_ptr __v16193; tll_ptr __v16196; tll_ptr c_v16191; tll_ptr c_v16195;
  tll_ptr close_tmp_t455; tll_ptr fork_ch_t451; tll_ptr recv_msg_t453;
  tll_ptr switch_ret_t454; tll_ptr zs1_v16194;
  instr_fork(&fork_ch_t451, &fork_fun_t450, 1, env[0]);
  c_v16191 = fork_ch_t451;
  instr_recv(&recv_msg_t453, c_v16191);
  __v16193 = recv_msg_t453;
  switch(((tll_node)__v16193)->tag) {
    case 0:
      zs1_v16194 = ((tll_node)__v16193)->data[0];
      c_v16195 = ((tll_node)__v16193)->data[1];
      instr_free_struct(__v16193);
      instr_close(&close_tmp_t455, c_v16195);
      __v16196 = close_tmp_t455;
      switch_ret_t454 = zs1_v16194;
      break;
  }
  return switch_ret_t454;
}

tll_ptr cmsortL_i55(tll_ptr zs0_v16183) {
  tll_ptr lam_clo_t457;
  instr_clo(&lam_clo_t457, &lam_fun_t456, 1, zs0_v16183);
  return lam_clo_t457;
}

tll_ptr lam_fun_t459(tll_ptr zs0_v16197, tll_env env) {
  tll_ptr call_ret_t458;
  call_ret_t458 = cmsortL_i55(zs0_v16197);
  return call_ret_t458;
}

tll_ptr mkListU_i58(tll_ptr n_v16198) {
  tll_ptr add_ret_t462; tll_ptr call_ret_t461; tll_ptr consUU_t463;
  tll_ptr ifte_ret_t465; tll_ptr nilUU_t464;
  if (n_v16198) {
    add_ret_t462 = n_v16198 - 1;
    call_ret_t461 = mkListU_i58(add_ret_t462);
    instr_struct(&consUU_t463, 13, 2, n_v16198, call_ret_t461);
    ifte_ret_t465 = consUU_t463;
  }
  else {
    instr_struct(&nilUU_t464, 12, 0);
    ifte_ret_t465 = nilUU_t464;
  }
  return ifte_ret_t465;
}

tll_ptr lam_fun_t467(tll_ptr n_v16199, tll_env env) {
  tll_ptr call_ret_t466;
  call_ret_t466 = mkListU_i58(n_v16199);
  return call_ret_t466;
}

tll_ptr mkListL_i57(tll_ptr n_v16200) {
  tll_ptr add_ret_t470; tll_ptr call_ret_t469; tll_ptr consUL_t471;
  tll_ptr ifte_ret_t473; tll_ptr nilUL_t472;
  if (n_v16200) {
    add_ret_t470 = n_v16200 - 1;
    call_ret_t469 = mkListL_i57(add_ret_t470);
    instr_struct(&consUL_t471, 11, 2, n_v16200, call_ret_t469);
    ifte_ret_t473 = consUL_t471;
  }
  else {
    instr_struct(&nilUL_t472, 10, 0);
    ifte_ret_t473 = nilUL_t472;
  }
  return ifte_ret_t473;
}

tll_ptr lam_fun_t475(tll_ptr n_v16201, tll_env env) {
  tll_ptr call_ret_t474;
  call_ret_t474 = mkListL_i57(n_v16201);
  return call_ret_t474;
}

tll_ptr free_i35(tll_ptr A_v16202, tll_ptr ls_v16203) {
  tll_ptr __v16204; tll_ptr call_ret_t478; tll_ptr ls_v16205;
  tll_ptr switch_ret_t477;
  switch(((tll_node)ls_v16203)->tag) {
    case 10:
      instr_free_struct(ls_v16203);
      switch_ret_t477 = 0;
      break;
    case 11:
      __v16204 = ((tll_node)ls_v16203)->data[0];
      ls_v16205 = ((tll_node)ls_v16203)->data[1];
      instr_free_struct(ls_v16203);
      call_ret_t478 = free_i35(0, ls_v16205);
      switch_ret_t477 = call_ret_t478;
      break;
  }
  return switch_ret_t477;
}

tll_ptr lam_fun_t480(tll_ptr ls_v16208, tll_env env) {
  tll_ptr call_ret_t479;
  call_ret_t479 = free_i35(env[0], ls_v16208);
  return call_ret_t479;
}

tll_ptr lam_fun_t482(tll_ptr A_v16206, tll_env env) {
  tll_ptr lam_clo_t481;
  instr_clo(&lam_clo_t481, &lam_fun_t480, 1, A_v16206);
  return lam_clo_t481;
}

int main() {
  instr_init();
  tll_ptr __v16211; tll_ptr call_ret_t484; tll_ptr call_ret_t485;
  tll_ptr call_ret_t486; tll_ptr lam_clo_t101; tll_ptr lam_clo_t111;
  tll_ptr lam_clo_t119; tll_ptr lam_clo_t12; tll_ptr lam_clo_t127;
  tll_ptr lam_clo_t133; tll_ptr lam_clo_t146; tll_ptr lam_clo_t159;
  tll_ptr lam_clo_t16; tll_ptr lam_clo_t172; tll_ptr lam_clo_t182;
  tll_ptr lam_clo_t192; tll_ptr lam_clo_t202; tll_ptr lam_clo_t212;
  tll_ptr lam_clo_t221; tll_ptr lam_clo_t230; tll_ptr lam_clo_t247;
  tll_ptr lam_clo_t26; tll_ptr lam_clo_t264; tll_ptr lam_clo_t280;
  tll_ptr lam_clo_t296; tll_ptr lam_clo_t311; tll_ptr lam_clo_t326;
  tll_ptr lam_clo_t37; tll_ptr lam_clo_t380; tll_ptr lam_clo_t434;
  tll_ptr lam_clo_t447; tll_ptr lam_clo_t460; tll_ptr lam_clo_t468;
  tll_ptr lam_clo_t476; tll_ptr lam_clo_t48; tll_ptr lam_clo_t483;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t6; tll_ptr lam_clo_t69;
  tll_ptr lam_clo_t74; tll_ptr lam_clo_t83; tll_ptr lam_clo_t92;
  tll_ptr sorted_v16210; tll_ptr test_v16209;
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
  instr_clo(&lam_clo_t380, &lam_fun_t379, 0);
  cmsort_workerUclo_i90 = lam_clo_t380;
  instr_clo(&lam_clo_t434, &lam_fun_t433, 0);
  cmsort_workerLclo_i91 = lam_clo_t434;
  instr_clo(&lam_clo_t447, &lam_fun_t446, 0);
  cmsortUclo_i92 = lam_clo_t447;
  instr_clo(&lam_clo_t460, &lam_fun_t459, 0);
  cmsortLclo_i93 = lam_clo_t460;
  instr_clo(&lam_clo_t468, &lam_fun_t467, 0);
  mkListUclo_i94 = lam_clo_t468;
  instr_clo(&lam_clo_t476, &lam_fun_t475, 0);
  mkListLclo_i95 = lam_clo_t476;
  instr_clo(&lam_clo_t483, &lam_fun_t482, 0);
  freeclo_i96 = lam_clo_t483;
  call_ret_t484 = mkListL_i57((tll_ptr)400000);
  test_v16209 = call_ret_t484;
  call_ret_t485 = msortL_i49(test_v16209);
  sorted_v16210 = call_ret_t485;
  call_ret_t486 = free_i35(0, sorted_v16210);
  __v16211 = call_ret_t486;
  return 0;
}

