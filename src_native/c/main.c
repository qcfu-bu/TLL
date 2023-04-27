#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v81097, tll_ptr b2_v81098);
tll_ptr orb_i2(tll_ptr b1_v81102, tll_ptr b2_v81103);
tll_ptr notb_i3(tll_ptr b_v81107);
tll_ptr lten_i4(tll_ptr x_v81109, tll_ptr y_v81110);
tll_ptr gten_i5(tll_ptr x_v81114, tll_ptr y_v81115);
tll_ptr ltn_i6(tll_ptr x_v81119, tll_ptr y_v81120);
tll_ptr gtn_i7(tll_ptr x_v81124, tll_ptr y_v81125);
tll_ptr eqn_i8(tll_ptr x_v81129, tll_ptr y_v81130);
tll_ptr pred_i9(tll_ptr x_v81134);
tll_ptr addn_i10(tll_ptr x_v81136, tll_ptr y_v81137);
tll_ptr subn_i11(tll_ptr x_v81141, tll_ptr y_v81142);
tll_ptr muln_i12(tll_ptr x_v81146, tll_ptr y_v81147);
tll_ptr divn_i13(tll_ptr x_v81151, tll_ptr y_v81152);
tll_ptr modn_i14(tll_ptr x_v81156, tll_ptr y_v81157);
tll_ptr cats_i15(tll_ptr s1_v81161, tll_ptr s2_v81162);
tll_ptr strlen_i16(tll_ptr s_v81168);
tll_ptr lenUU_i40(tll_ptr A_v81172, tll_ptr xs_v81173);
tll_ptr lenUL_i39(tll_ptr A_v81181, tll_ptr xs_v81182);
tll_ptr lenLL_i37(tll_ptr A_v81190, tll_ptr xs_v81191);
tll_ptr appendUU_i44(tll_ptr A_v81199, tll_ptr xs_v81200, tll_ptr ys_v81201);
tll_ptr appendUL_i43(tll_ptr A_v81210, tll_ptr xs_v81211, tll_ptr ys_v81212);
tll_ptr appendLL_i41(tll_ptr A_v81221, tll_ptr xs_v81222, tll_ptr ys_v81223);
tll_ptr readline_i25(tll_ptr __v81232);
tll_ptr print_i26(tll_ptr s_v81239);
tll_ptr prerr_i27(tll_ptr s_v81242);
tll_ptr splitU_i46(tll_ptr zs_v81245);
tll_ptr splitL_i45(tll_ptr zs_v81253);
tll_ptr mergeU_i48(tll_ptr xs_v81261, tll_ptr ys_v81262);
tll_ptr mergeL_i47(tll_ptr xs_v81270, tll_ptr ys_v81271);
tll_ptr msortU_i50(tll_ptr zs_v81279);
tll_ptr msortL_i49(tll_ptr zs_v81287);
tll_ptr cmsort_workerU_i54(tll_ptr n_v81295, tll_ptr zs_v81296, tll_ptr c_v81297);
tll_ptr cmsort_workerL_i53(tll_ptr n_v81335, tll_ptr zs_v81336, tll_ptr c_v81337);
tll_ptr cmsortU_i56(tll_ptr zs_v81375);
tll_ptr cmsortL_i55(tll_ptr zs_v81384);
tll_ptr mkListU_i58(tll_ptr n_v81393);
tll_ptr mkListL_i57(tll_ptr n_v81395);
tll_ptr free_i35(tll_ptr A_v81397, tll_ptr ls_v81398);

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

tll_ptr andb_i1(tll_ptr b1_v81097, tll_ptr b2_v81098) {
  tll_ptr ifte_ret_t1;
  if (b1_v81097) {
    ifte_ret_t1 = b2_v81098;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v81101, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v81101);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v81099, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v81099);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v81102, tll_ptr b2_v81103) {
  tll_ptr ifte_ret_t7;
  if (b1_v81102) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v81103;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v81106, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v81106);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v81104, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v81104);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v81107) {
  tll_ptr ifte_ret_t13;
  if (b_v81107) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v81108, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v81108);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v81109, tll_ptr y_v81110) {
  tll_ptr add_ret_t18; tll_ptr add_ret_t19; tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  if (x_v81109) {
    if (y_v81110) {
      add_ret_t18 = x_v81109 - 1;
      add_ret_t19 = y_v81110 - 1;
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

tll_ptr lam_fun_t23(tll_ptr y_v81113, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v81113);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v81111, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v81111);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v81114, tll_ptr y_v81115) {
  tll_ptr add_ret_t28; tll_ptr add_ret_t29; tll_ptr call_ret_t27;
  tll_ptr ifte_ret_t30; tll_ptr ifte_ret_t31; tll_ptr ifte_ret_t32;
  if (x_v81114) {
    if (y_v81115) {
      add_ret_t28 = x_v81114 - 1;
      add_ret_t29 = y_v81115 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v81115) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v81118, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v81118);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v81116, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v81116);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v81119, tll_ptr y_v81120) {
  tll_ptr add_ret_t39; tll_ptr add_ret_t40; tll_ptr call_ret_t38;
  tll_ptr ifte_ret_t41; tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t43;
  if (x_v81119) {
    if (y_v81120) {
      add_ret_t39 = x_v81119 - 1;
      add_ret_t40 = y_v81120 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v81120) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v81123, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v81123);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v81121, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v81121);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v81124, tll_ptr y_v81125) {
  tll_ptr add_ret_t50; tll_ptr add_ret_t51; tll_ptr call_ret_t49;
  tll_ptr ifte_ret_t52; tll_ptr ifte_ret_t53;
  if (x_v81124) {
    if (y_v81125) {
      add_ret_t50 = x_v81124 - 1;
      add_ret_t51 = y_v81125 - 1;
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

tll_ptr lam_fun_t55(tll_ptr y_v81128, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v81128);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v81126, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v81126);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v81129, tll_ptr y_v81130) {
  tll_ptr add_ret_t60; tll_ptr add_ret_t61; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t62; tll_ptr ifte_ret_t63; tll_ptr ifte_ret_t64;
  if (x_v81129) {
    if (y_v81130) {
      add_ret_t60 = x_v81129 - 1;
      add_ret_t61 = y_v81130 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v81130) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v81133, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v81133);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v81131, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v81131);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v81134) {
  tll_ptr add_ret_t70; tll_ptr ifte_ret_t71;
  if (x_v81134) {
    add_ret_t70 = x_v81134 - 1;
    ifte_ret_t71 = add_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v81135, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v81135);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v81136, tll_ptr y_v81137) {
  tll_ptr add_ret_t76; tll_ptr add_ret_t77; tll_ptr call_ret_t75;
  tll_ptr ifte_ret_t78;
  if (x_v81136) {
    add_ret_t76 = x_v81136 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v81137);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v81137;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v81140, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v81140);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v81138, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v81138);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v81141, tll_ptr y_v81142) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v81142) {
    call_ret_t85 = pred_i9(x_v81141);
    add_ret_t86 = y_v81142 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v81141;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v81145, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v81145);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v81143, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v81143);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v81146, tll_ptr y_v81147) {
  tll_ptr add_ret_t95; tll_ptr call_ret_t93; tll_ptr call_ret_t94;
  tll_ptr ifte_ret_t96;
  if (x_v81146) {
    add_ret_t95 = x_v81146 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v81147);
    call_ret_t93 = addn_i10(y_v81147, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v81150, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v81150);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v81148, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v81148);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v81151, tll_ptr y_v81152) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v81151, y_v81152);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v81151, y_v81152);
    call_ret_t103 = divn_i13(call_ret_t104, y_v81152);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v81155, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v81155);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v81153, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v81153);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v81156, tll_ptr y_v81157) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v81156, y_v81157);
  call_ret_t113 = muln_i12(call_ret_t114, y_v81157);
  call_ret_t112 = subn_i11(x_v81156, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v81160, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v81160);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v81158, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v81158);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v81161, tll_ptr s2_v81162) {
  tll_ptr String_t122; tll_ptr c_v81163; tll_ptr call_ret_t121;
  tll_ptr s1_v81164; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v81161)->tag) {
    case 2:
      switch_ret_t120 = s2_v81162;
      break;
    case 3:
      c_v81163 = ((tll_node)s1_v81161)->data[0];
      s1_v81164 = ((tll_node)s1_v81161)->data[1];
      call_ret_t121 = cats_i15(s1_v81164, s2_v81162);
      instr_struct(&String_t122, 3, 2, c_v81163, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v81167, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v81167);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v81165, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v81165);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v81168) {
  tll_ptr __v81169; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v81170; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v81168)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v81169 = ((tll_node)s_v81168)->data[0];
      s_v81170 = ((tll_node)s_v81168)->data[1];
      call_ret_t129 = strlen_i16(s_v81170);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v81171, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v81171);
  return call_ret_t131;
}

tll_ptr lenUU_i40(tll_ptr A_v81172, tll_ptr xs_v81173) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v81176; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v81174; tll_ptr xs_v81175; tll_ptr xs_v81177;
  switch(((tll_node)xs_v81173)->tag) {
    case 13:
      instr_struct(&nilUU_t135, 13, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 14:
      x_v81174 = ((tll_node)xs_v81173)->data[0];
      xs_v81175 = ((tll_node)xs_v81173)->data[1];
      call_ret_t137 = lenUU_i40(0, xs_v81175);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v81176 = ((tll_node)call_ret_t137)->data[0];
          xs_v81177 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v81176 + 1;
          instr_struct(&consUU_t140, 14, 2, x_v81174, xs_v81177);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v81180, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i40(env[0], xs_v81180);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v81178, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v81178);
  return lam_clo_t144;
}

tll_ptr lenUL_i39(tll_ptr A_v81181, tll_ptr xs_v81182) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v81185; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v81183; tll_ptr xs_v81184; tll_ptr xs_v81186;
  switch(((tll_node)xs_v81182)->tag) {
    case 11:
      instr_free_struct(xs_v81182);
      instr_struct(&nilUL_t148, 11, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 12:
      x_v81183 = ((tll_node)xs_v81182)->data[0];
      xs_v81184 = ((tll_node)xs_v81182)->data[1];
      instr_free_struct(xs_v81182);
      call_ret_t150 = lenUL_i39(0, xs_v81184);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v81185 = ((tll_node)call_ret_t150)->data[0];
          xs_v81186 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v81185 + 1;
          instr_struct(&consUL_t153, 12, 2, x_v81183, xs_v81186);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v81189, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i39(env[0], xs_v81189);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v81187, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v81187);
  return lam_clo_t157;
}

tll_ptr lenLL_i37(tll_ptr A_v81190, tll_ptr xs_v81191) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v81194; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v81192; tll_ptr xs_v81193; tll_ptr xs_v81195;
  switch(((tll_node)xs_v81191)->tag) {
    case 7:
      instr_free_struct(xs_v81191);
      instr_struct(&nilLL_t161, 7, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 8:
      x_v81192 = ((tll_node)xs_v81191)->data[0];
      xs_v81193 = ((tll_node)xs_v81191)->data[1];
      instr_free_struct(xs_v81191);
      call_ret_t163 = lenLL_i37(0, xs_v81193);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v81194 = ((tll_node)call_ret_t163)->data[0];
          xs_v81195 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v81194 + 1;
          instr_struct(&consLL_t166, 8, 2, x_v81192, xs_v81195);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v81198, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i37(env[0], xs_v81198);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v81196, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v81196);
  return lam_clo_t170;
}

tll_ptr appendUU_i44(tll_ptr A_v81199, tll_ptr xs_v81200, tll_ptr ys_v81201) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v81202; tll_ptr xs_v81203;
  switch(((tll_node)xs_v81200)->tag) {
    case 13:
      switch_ret_t173 = ys_v81201;
      break;
    case 14:
      x_v81202 = ((tll_node)xs_v81200)->data[0];
      xs_v81203 = ((tll_node)xs_v81200)->data[1];
      call_ret_t174 = appendUU_i44(0, xs_v81203, ys_v81201);
      instr_struct(&consUU_t175, 14, 2, x_v81202, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v81209, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i44(env[1], env[0], ys_v81209);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v81207, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v81207, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v81204, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v81204);
  return lam_clo_t180;
}

tll_ptr appendUL_i43(tll_ptr A_v81210, tll_ptr xs_v81211, tll_ptr ys_v81212) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v81213; tll_ptr xs_v81214;
  switch(((tll_node)xs_v81211)->tag) {
    case 11:
      instr_free_struct(xs_v81211);
      switch_ret_t183 = ys_v81212;
      break;
    case 12:
      x_v81213 = ((tll_node)xs_v81211)->data[0];
      xs_v81214 = ((tll_node)xs_v81211)->data[1];
      instr_free_struct(xs_v81211);
      call_ret_t184 = appendUL_i43(0, xs_v81214, ys_v81212);
      instr_struct(&consUL_t185, 12, 2, x_v81213, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v81220, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i43(env[1], env[0], ys_v81220);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v81218, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v81218, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v81215, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v81215);
  return lam_clo_t190;
}

tll_ptr appendLL_i41(tll_ptr A_v81221, tll_ptr xs_v81222, tll_ptr ys_v81223) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v81224; tll_ptr xs_v81225;
  switch(((tll_node)xs_v81222)->tag) {
    case 7:
      instr_free_struct(xs_v81222);
      switch_ret_t193 = ys_v81223;
      break;
    case 8:
      x_v81224 = ((tll_node)xs_v81222)->data[0];
      xs_v81225 = ((tll_node)xs_v81222)->data[1];
      instr_free_struct(xs_v81222);
      call_ret_t194 = appendLL_i41(0, xs_v81225, ys_v81223);
      instr_struct(&consLL_t195, 8, 2, x_v81224, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v81231, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i41(env[1], env[0], ys_v81231);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v81229, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v81229, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v81226, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v81226);
  return lam_clo_t200;
}

tll_ptr lam_fun_t207(tll_ptr __v81233, tll_env env) {
  tll_ptr ch_v81237; tll_ptr prim_ch_t205; tll_ptr recv_msg_t203;
  tll_ptr s_v81236; tll_ptr send_ch_t204; tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t205, &proc_stdin);
  instr_send(&send_ch_t204, prim_ch_t205, (tll_ptr)1);
  instr_recv(&recv_msg_t203, send_ch_t204);
  switch(((tll_node)recv_msg_t203)->tag) {
    case 0:
      s_v81236 = ((tll_node)recv_msg_t203)->data[0];
      ch_v81237 = ((tll_node)recv_msg_t203)->data[1];
      instr_free_struct(recv_msg_t203);
      switch_ret_t206 = s_v81236;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v81232) {
  tll_ptr lam_clo_t208;
  instr_clo(&lam_clo_t208, &lam_fun_t207, 0);
  return lam_clo_t208;
}

tll_ptr lam_fun_t210(tll_ptr __v81238, tll_env env) {
  tll_ptr call_ret_t209;
  call_ret_t209 = readline_i25(__v81238);
  return call_ret_t209;
}

tll_ptr lam_fun_t212(tll_ptr __v81240, tll_env env) {
  
  
  return 0;
}

tll_ptr print_i26(tll_ptr s_v81239) {
  tll_ptr lam_clo_t213;
  instr_clo(&lam_clo_t213, &lam_fun_t212, 0);
  return lam_clo_t213;
}

tll_ptr lam_fun_t215(tll_ptr s_v81241, tll_env env) {
  tll_ptr call_ret_t214;
  call_ret_t214 = print_i26(s_v81241);
  return call_ret_t214;
}

tll_ptr lam_fun_t217(tll_ptr __v81243, tll_env env) {
  
  
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v81242) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 0);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v81244, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = prerr_i27(s_v81244);
  return call_ret_t219;
}

tll_ptr splitU_i46(tll_ptr zs_v81245) {
  tll_ptr call_ret_t231; tll_ptr consUU_t228; tll_ptr consUU_t233;
  tll_ptr consUU_t234; tll_ptr nilUU_t223; tll_ptr nilUU_t224;
  tll_ptr nilUU_t227; tll_ptr nilUU_t229; tll_ptr pair_struct_t225;
  tll_ptr pair_struct_t230; tll_ptr pair_struct_t235;
  tll_ptr switch_ret_t222; tll_ptr switch_ret_t226; tll_ptr switch_ret_t232;
  tll_ptr x_v81246; tll_ptr xs_v81250; tll_ptr y_v81248; tll_ptr ys_v81251;
  tll_ptr zs_v81247; tll_ptr zs_v81249;
  switch(((tll_node)zs_v81245)->tag) {
    case 13:
      instr_struct(&nilUU_t223, 13, 0);
      instr_struct(&nilUU_t224, 13, 0);
      instr_struct(&pair_struct_t225, 0, 2, nilUU_t223, nilUU_t224);
      switch_ret_t222 = pair_struct_t225;
      break;
    case 14:
      x_v81246 = ((tll_node)zs_v81245)->data[0];
      zs_v81247 = ((tll_node)zs_v81245)->data[1];
      switch(((tll_node)zs_v81247)->tag) {
        case 13:
          instr_struct(&nilUU_t227, 13, 0);
          instr_struct(&consUU_t228, 14, 2, x_v81246, nilUU_t227);
          instr_struct(&nilUU_t229, 13, 0);
          instr_struct(&pair_struct_t230, 0, 2, consUU_t228, nilUU_t229);
          switch_ret_t226 = pair_struct_t230;
          break;
        case 14:
          y_v81248 = ((tll_node)zs_v81247)->data[0];
          zs_v81249 = ((tll_node)zs_v81247)->data[1];
          call_ret_t231 = splitU_i46(zs_v81249);
          switch(((tll_node)call_ret_t231)->tag) {
            case 0:
              xs_v81250 = ((tll_node)call_ret_t231)->data[0];
              ys_v81251 = ((tll_node)call_ret_t231)->data[1];
              instr_free_struct(call_ret_t231);
              instr_struct(&consUU_t233, 14, 2, x_v81246, xs_v81250);
              instr_struct(&consUU_t234, 14, 2, y_v81248, ys_v81251);
              instr_struct(&pair_struct_t235, 0, 2, consUU_t233, consUU_t234);
              switch_ret_t232 = pair_struct_t235;
              break;
          }
          switch_ret_t226 = switch_ret_t232;
          break;
      }
      switch_ret_t222 = switch_ret_t226;
      break;
  }
  return switch_ret_t222;
}

tll_ptr lam_fun_t237(tll_ptr zs_v81252, tll_env env) {
  tll_ptr call_ret_t236;
  call_ret_t236 = splitU_i46(zs_v81252);
  return call_ret_t236;
}

tll_ptr splitL_i45(tll_ptr zs_v81253) {
  tll_ptr call_ret_t248; tll_ptr consUL_t245; tll_ptr consUL_t250;
  tll_ptr consUL_t251; tll_ptr nilUL_t240; tll_ptr nilUL_t241;
  tll_ptr nilUL_t244; tll_ptr nilUL_t246; tll_ptr pair_struct_t242;
  tll_ptr pair_struct_t247; tll_ptr pair_struct_t252;
  tll_ptr switch_ret_t239; tll_ptr switch_ret_t243; tll_ptr switch_ret_t249;
  tll_ptr x_v81254; tll_ptr xs_v81258; tll_ptr y_v81256; tll_ptr ys_v81259;
  tll_ptr zs_v81255; tll_ptr zs_v81257;
  switch(((tll_node)zs_v81253)->tag) {
    case 11:
      instr_free_struct(zs_v81253);
      instr_struct(&nilUL_t240, 11, 0);
      instr_struct(&nilUL_t241, 11, 0);
      instr_struct(&pair_struct_t242, 0, 2, nilUL_t240, nilUL_t241);
      switch_ret_t239 = pair_struct_t242;
      break;
    case 12:
      x_v81254 = ((tll_node)zs_v81253)->data[0];
      zs_v81255 = ((tll_node)zs_v81253)->data[1];
      instr_free_struct(zs_v81253);
      switch(((tll_node)zs_v81255)->tag) {
        case 11:
          instr_free_struct(zs_v81255);
          instr_struct(&nilUL_t244, 11, 0);
          instr_struct(&consUL_t245, 12, 2, x_v81254, nilUL_t244);
          instr_struct(&nilUL_t246, 11, 0);
          instr_struct(&pair_struct_t247, 0, 2, consUL_t245, nilUL_t246);
          switch_ret_t243 = pair_struct_t247;
          break;
        case 12:
          y_v81256 = ((tll_node)zs_v81255)->data[0];
          zs_v81257 = ((tll_node)zs_v81255)->data[1];
          instr_free_struct(zs_v81255);
          call_ret_t248 = splitL_i45(zs_v81257);
          switch(((tll_node)call_ret_t248)->tag) {
            case 0:
              xs_v81258 = ((tll_node)call_ret_t248)->data[0];
              ys_v81259 = ((tll_node)call_ret_t248)->data[1];
              instr_free_struct(call_ret_t248);
              instr_struct(&consUL_t250, 12, 2, x_v81254, xs_v81258);
              instr_struct(&consUL_t251, 12, 2, y_v81256, ys_v81259);
              instr_struct(&pair_struct_t252, 0, 2, consUL_t250, consUL_t251);
              switch_ret_t249 = pair_struct_t252;
              break;
          }
          switch_ret_t243 = switch_ret_t249;
          break;
      }
      switch_ret_t239 = switch_ret_t243;
      break;
  }
  return switch_ret_t239;
}

tll_ptr lam_fun_t254(tll_ptr zs_v81260, tll_env env) {
  tll_ptr call_ret_t253;
  call_ret_t253 = splitL_i45(zs_v81260);
  return call_ret_t253;
}

tll_ptr mergeU_i48(tll_ptr xs_v81261, tll_ptr ys_v81262) {
  tll_ptr call_ret_t259; tll_ptr call_ret_t260; tll_ptr call_ret_t263;
  tll_ptr consUU_t258; tll_ptr consUU_t261; tll_ptr consUU_t262;
  tll_ptr consUU_t264; tll_ptr consUU_t265; tll_ptr ifte_ret_t266;
  tll_ptr switch_ret_t256; tll_ptr switch_ret_t257; tll_ptr x_v81263;
  tll_ptr xs0_v81264; tll_ptr y_v81265; tll_ptr ys0_v81266;
  switch(((tll_node)xs_v81261)->tag) {
    case 13:
      switch_ret_t256 = ys_v81262;
      break;
    case 14:
      x_v81263 = ((tll_node)xs_v81261)->data[0];
      xs0_v81264 = ((tll_node)xs_v81261)->data[1];
      switch(((tll_node)ys_v81262)->tag) {
        case 13:
          instr_struct(&consUU_t258, 14, 2, x_v81263, xs0_v81264);
          switch_ret_t257 = consUU_t258;
          break;
        case 14:
          y_v81265 = ((tll_node)ys_v81262)->data[0];
          ys0_v81266 = ((tll_node)ys_v81262)->data[1];
          call_ret_t259 = lten_i4(x_v81263, y_v81265);
          if (call_ret_t259) {
            instr_struct(&consUU_t261, 14, 2, y_v81265, ys0_v81266);
            call_ret_t260 = mergeU_i48(xs0_v81264, consUU_t261);
            instr_struct(&consUU_t262, 14, 2, x_v81263, call_ret_t260);
            ifte_ret_t266 = consUU_t262;
          }
          else {
            instr_struct(&consUU_t264, 14, 2, x_v81263, xs0_v81264);
            call_ret_t263 = mergeU_i48(consUU_t264, ys0_v81266);
            instr_struct(&consUU_t265, 14, 2, y_v81265, call_ret_t263);
            ifte_ret_t266 = consUU_t265;
          }
          switch_ret_t257 = ifte_ret_t266;
          break;
      }
      switch_ret_t256 = switch_ret_t257;
      break;
  }
  return switch_ret_t256;
}

tll_ptr lam_fun_t268(tll_ptr ys_v81269, tll_env env) {
  tll_ptr call_ret_t267;
  call_ret_t267 = mergeU_i48(env[0], ys_v81269);
  return call_ret_t267;
}

tll_ptr lam_fun_t270(tll_ptr xs_v81267, tll_env env) {
  tll_ptr lam_clo_t269;
  instr_clo(&lam_clo_t269, &lam_fun_t268, 1, xs_v81267);
  return lam_clo_t269;
}

tll_ptr mergeL_i47(tll_ptr xs_v81270, tll_ptr ys_v81271) {
  tll_ptr call_ret_t275; tll_ptr call_ret_t276; tll_ptr call_ret_t279;
  tll_ptr consUL_t274; tll_ptr consUL_t277; tll_ptr consUL_t278;
  tll_ptr consUL_t280; tll_ptr consUL_t281; tll_ptr ifte_ret_t282;
  tll_ptr switch_ret_t272; tll_ptr switch_ret_t273; tll_ptr x_v81272;
  tll_ptr xs0_v81273; tll_ptr y_v81274; tll_ptr ys0_v81275;
  switch(((tll_node)xs_v81270)->tag) {
    case 11:
      instr_free_struct(xs_v81270);
      switch_ret_t272 = ys_v81271;
      break;
    case 12:
      x_v81272 = ((tll_node)xs_v81270)->data[0];
      xs0_v81273 = ((tll_node)xs_v81270)->data[1];
      instr_free_struct(xs_v81270);
      switch(((tll_node)ys_v81271)->tag) {
        case 11:
          instr_free_struct(ys_v81271);
          instr_struct(&consUL_t274, 12, 2, x_v81272, xs0_v81273);
          switch_ret_t273 = consUL_t274;
          break;
        case 12:
          y_v81274 = ((tll_node)ys_v81271)->data[0];
          ys0_v81275 = ((tll_node)ys_v81271)->data[1];
          instr_free_struct(ys_v81271);
          call_ret_t275 = lten_i4(x_v81272, y_v81274);
          if (call_ret_t275) {
            instr_struct(&consUL_t277, 12, 2, y_v81274, ys0_v81275);
            call_ret_t276 = mergeL_i47(xs0_v81273, consUL_t277);
            instr_struct(&consUL_t278, 12, 2, x_v81272, call_ret_t276);
            ifte_ret_t282 = consUL_t278;
          }
          else {
            instr_struct(&consUL_t280, 12, 2, x_v81272, xs0_v81273);
            call_ret_t279 = mergeL_i47(consUL_t280, ys0_v81275);
            instr_struct(&consUL_t281, 12, 2, y_v81274, call_ret_t279);
            ifte_ret_t282 = consUL_t281;
          }
          switch_ret_t273 = ifte_ret_t282;
          break;
      }
      switch_ret_t272 = switch_ret_t273;
      break;
  }
  return switch_ret_t272;
}

tll_ptr lam_fun_t284(tll_ptr ys_v81278, tll_env env) {
  tll_ptr call_ret_t283;
  call_ret_t283 = mergeL_i47(env[0], ys_v81278);
  return call_ret_t283;
}

tll_ptr lam_fun_t286(tll_ptr xs_v81276, tll_env env) {
  tll_ptr lam_clo_t285;
  instr_clo(&lam_clo_t285, &lam_fun_t284, 1, xs_v81276);
  return lam_clo_t285;
}

tll_ptr msortU_i50(tll_ptr zs_v81279) {
  tll_ptr call_ret_t293; tll_ptr call_ret_t297; tll_ptr call_ret_t298;
  tll_ptr call_ret_t299; tll_ptr consUU_t292; tll_ptr consUU_t294;
  tll_ptr consUU_t295; tll_ptr nilUU_t289; tll_ptr nilUU_t291;
  tll_ptr switch_ret_t288; tll_ptr switch_ret_t290; tll_ptr switch_ret_t296;
  tll_ptr x_v81280; tll_ptr xs_v81284; tll_ptr y_v81282; tll_ptr ys_v81285;
  tll_ptr zs_v81281; tll_ptr zs_v81283;
  switch(((tll_node)zs_v81279)->tag) {
    case 13:
      instr_struct(&nilUU_t289, 13, 0);
      switch_ret_t288 = nilUU_t289;
      break;
    case 14:
      x_v81280 = ((tll_node)zs_v81279)->data[0];
      zs_v81281 = ((tll_node)zs_v81279)->data[1];
      switch(((tll_node)zs_v81281)->tag) {
        case 13:
          instr_struct(&nilUU_t291, 13, 0);
          instr_struct(&consUU_t292, 14, 2, x_v81280, nilUU_t291);
          switch_ret_t290 = consUU_t292;
          break;
        case 14:
          y_v81282 = ((tll_node)zs_v81281)->data[0];
          zs_v81283 = ((tll_node)zs_v81281)->data[1];
          instr_struct(&consUU_t294, 14, 2, y_v81282, zs_v81283);
          instr_struct(&consUU_t295, 14, 2, x_v81280, consUU_t294);
          call_ret_t293 = splitU_i46(consUU_t295);
          switch(((tll_node)call_ret_t293)->tag) {
            case 0:
              xs_v81284 = ((tll_node)call_ret_t293)->data[0];
              ys_v81285 = ((tll_node)call_ret_t293)->data[1];
              instr_free_struct(call_ret_t293);
              call_ret_t298 = msortU_i50(xs_v81284);
              call_ret_t299 = msortU_i50(ys_v81285);
              call_ret_t297 = mergeU_i48(call_ret_t298, call_ret_t299);
              switch_ret_t296 = call_ret_t297;
              break;
          }
          switch_ret_t290 = switch_ret_t296;
          break;
      }
      switch_ret_t288 = switch_ret_t290;
      break;
  }
  return switch_ret_t288;
}

tll_ptr lam_fun_t301(tll_ptr zs_v81286, tll_env env) {
  tll_ptr call_ret_t300;
  call_ret_t300 = msortU_i50(zs_v81286);
  return call_ret_t300;
}

tll_ptr msortL_i49(tll_ptr zs_v81287) {
  tll_ptr call_ret_t308; tll_ptr call_ret_t312; tll_ptr call_ret_t313;
  tll_ptr call_ret_t314; tll_ptr consUL_t307; tll_ptr consUL_t309;
  tll_ptr consUL_t310; tll_ptr nilUL_t304; tll_ptr nilUL_t306;
  tll_ptr switch_ret_t303; tll_ptr switch_ret_t305; tll_ptr switch_ret_t311;
  tll_ptr x_v81288; tll_ptr xs_v81292; tll_ptr y_v81290; tll_ptr ys_v81293;
  tll_ptr zs_v81289; tll_ptr zs_v81291;
  switch(((tll_node)zs_v81287)->tag) {
    case 11:
      instr_free_struct(zs_v81287);
      instr_struct(&nilUL_t304, 11, 0);
      switch_ret_t303 = nilUL_t304;
      break;
    case 12:
      x_v81288 = ((tll_node)zs_v81287)->data[0];
      zs_v81289 = ((tll_node)zs_v81287)->data[1];
      instr_free_struct(zs_v81287);
      switch(((tll_node)zs_v81289)->tag) {
        case 11:
          instr_free_struct(zs_v81289);
          instr_struct(&nilUL_t306, 11, 0);
          instr_struct(&consUL_t307, 12, 2, x_v81288, nilUL_t306);
          switch_ret_t305 = consUL_t307;
          break;
        case 12:
          y_v81290 = ((tll_node)zs_v81289)->data[0];
          zs_v81291 = ((tll_node)zs_v81289)->data[1];
          instr_free_struct(zs_v81289);
          instr_struct(&consUL_t309, 12, 2, y_v81290, zs_v81291);
          instr_struct(&consUL_t310, 12, 2, x_v81288, consUL_t309);
          call_ret_t308 = splitL_i45(consUL_t310);
          switch(((tll_node)call_ret_t308)->tag) {
            case 0:
              xs_v81292 = ((tll_node)call_ret_t308)->data[0];
              ys_v81293 = ((tll_node)call_ret_t308)->data[1];
              instr_free_struct(call_ret_t308);
              call_ret_t313 = msortL_i49(xs_v81292);
              call_ret_t314 = msortL_i49(ys_v81293);
              call_ret_t312 = mergeL_i47(call_ret_t313, call_ret_t314);
              switch_ret_t311 = call_ret_t312;
              break;
          }
          switch_ret_t305 = switch_ret_t311;
          break;
      }
      switch_ret_t303 = switch_ret_t305;
      break;
  }
  return switch_ret_t303;
}

tll_ptr lam_fun_t316(tll_ptr zs_v81294, tll_env env) {
  tll_ptr call_ret_t315;
  call_ret_t315 = msortL_i49(zs_v81294);
  return call_ret_t315;
}

tll_ptr lam_fun_t320(tll_ptr __v81299, tll_env env) {
  
  
  return 0;
}

tll_ptr lam_fun_t323(tll_ptr __v81302, tll_env env) {
  
  
  return 0;
}

tll_ptr fork_fun_t332(tll_env env) {
  tll_ptr app_ret_t331; tll_ptr call_ret_t330; tll_ptr fork_ret_t334;
  call_ret_t330 = cmsort_workerU_i54(env[2], env[1], env[0]);
  instr_app(&app_ret_t331, call_ret_t330, 0);
  instr_free_clo(call_ret_t330);
  fork_ret_t334 = app_ret_t331;
  instr_free_thread(env);
  return fork_ret_t334;
}

tll_ptr fork_fun_t339(tll_env env) {
  tll_ptr app_ret_t338; tll_ptr call_ret_t337; tll_ptr fork_ret_t341;
  call_ret_t337 = cmsort_workerU_i54(env[2], env[1], env[0]);
  instr_app(&app_ret_t338, call_ret_t337, 0);
  instr_free_clo(call_ret_t337);
  fork_ret_t341 = app_ret_t338;
  instr_free_thread(env);
  return fork_ret_t341;
}

tll_ptr lam_fun_t345(tll_ptr __v81307, tll_env env) {
  tll_ptr fork_ch_t333; tll_ptr fork_ch_t340; tll_ptr msg1_v81319;
  tll_ptr msg2_v81322; tll_ptr pf1_v81325; tll_ptr pf2_v81327;
  tll_ptr r1_v81320; tll_ptr r2_v81323; tll_ptr recv_msg_t329;
  tll_ptr recv_msg_t336; tll_ptr switch_ret_t335; tll_ptr switch_ret_t342;
  tll_ptr switch_ret_t343; tll_ptr switch_ret_t344; tll_ptr xs1_v81324;
  tll_ptr xs2_v81326;
  instr_fork(&fork_ch_t333, &fork_fun_t332, 2, env[1], env[2]);
  instr_recv(&recv_msg_t329, fork_ch_t333);
  switch(((tll_node)recv_msg_t329)->tag) {
    case 0:
      msg1_v81319 = ((tll_node)recv_msg_t329)->data[0];
      r1_v81320 = ((tll_node)recv_msg_t329)->data[1];
      instr_free_struct(recv_msg_t329);
      instr_fork(&fork_ch_t340, &fork_fun_t339, 2, env[0], env[2]);
      instr_recv(&recv_msg_t336, fork_ch_t340);
      switch(((tll_node)recv_msg_t336)->tag) {
        case 0:
          msg2_v81322 = ((tll_node)recv_msg_t336)->data[0];
          r2_v81323 = ((tll_node)recv_msg_t336)->data[1];
          instr_free_struct(recv_msg_t336);
          switch(((tll_node)msg1_v81319)->tag) {
            case 16:
              xs1_v81324 = ((tll_node)msg1_v81319)->data[0];
              pf1_v81325 = ((tll_node)msg1_v81319)->data[1];
              switch(((tll_node)msg2_v81322)->tag) {
                case 16:
                  xs2_v81326 = ((tll_node)msg2_v81322)->data[0];
                  pf2_v81327 = ((tll_node)msg2_v81322)->data[1];
                  switch_ret_t344 = 0;
                  break;
              }
              switch_ret_t343 = switch_ret_t344;
              break;
          }
          switch_ret_t342 = switch_ret_t343;
          break;
      }
      switch_ret_t335 = switch_ret_t342;
      break;
  }
  return switch_ret_t335;
}

tll_ptr lam_fun_t347(tll_ptr __v81328, tll_env env) {
  
  
  return 0;
}

tll_ptr cmsort_workerU_i54(tll_ptr n_v81295, tll_ptr zs_v81296, tll_ptr c_v81297) {
  tll_ptr add_ret_t318; tll_ptr call_ret_t325; tll_ptr consUU_t326;
  tll_ptr consUU_t327; tll_ptr ifte_ret_t349; tll_ptr lam_clo_t321;
  tll_ptr lam_clo_t324; tll_ptr lam_clo_t346; tll_ptr lam_clo_t348;
  tll_ptr n0_v81298; tll_ptr switch_ret_t319; tll_ptr switch_ret_t322;
  tll_ptr switch_ret_t328; tll_ptr xs0_v81305; tll_ptr ys0_v81306;
  tll_ptr z0_v81300; tll_ptr z1_v81303; tll_ptr zs0_v81301;
  tll_ptr zs1_v81304;
  if (n_v81295) {
    add_ret_t318 = n_v81295 - 1;
    n0_v81298 = add_ret_t318;
    switch(((tll_node)zs_v81296)->tag) {
      case 13:
        instr_clo(&lam_clo_t321, &lam_fun_t320, 0);
        switch_ret_t319 = lam_clo_t321;
        break;
      case 14:
        z0_v81300 = ((tll_node)zs_v81296)->data[0];
        zs0_v81301 = ((tll_node)zs_v81296)->data[1];
        switch(((tll_node)zs0_v81301)->tag) {
          case 13:
            instr_clo(&lam_clo_t324, &lam_fun_t323, 0);
            switch_ret_t322 = lam_clo_t324;
            break;
          case 14:
            z1_v81303 = ((tll_node)zs0_v81301)->data[0];
            zs1_v81304 = ((tll_node)zs0_v81301)->data[1];
            instr_struct(&consUU_t326, 14, 2, z1_v81303, zs1_v81304);
            instr_struct(&consUU_t327, 14, 2, z0_v81300, consUU_t326);
            call_ret_t325 = splitU_i46(consUU_t327);
            switch(((tll_node)call_ret_t325)->tag) {
              case 0:
                xs0_v81305 = ((tll_node)call_ret_t325)->data[0];
                ys0_v81306 = ((tll_node)call_ret_t325)->data[1];
                instr_free_struct(call_ret_t325);
                instr_clo(&lam_clo_t346, &lam_fun_t345, 3,
                          ys0_v81306, xs0_v81305, n0_v81298);
                switch_ret_t328 = lam_clo_t346;
                break;
            }
            switch_ret_t322 = switch_ret_t328;
            break;
        }
        switch_ret_t319 = switch_ret_t322;
        break;
    }
    ifte_ret_t349 = switch_ret_t319;
  }
  else {
    instr_clo(&lam_clo_t348, &lam_fun_t347, 0);
    ifte_ret_t349 = lam_clo_t348;
  }
  return ifte_ret_t349;
}

tll_ptr lam_fun_t351(tll_ptr c_v81334, tll_env env) {
  tll_ptr call_ret_t350;
  call_ret_t350 = cmsort_workerU_i54(env[1], env[0], c_v81334);
  return call_ret_t350;
}

tll_ptr lam_fun_t353(tll_ptr zs_v81332, tll_env env) {
  tll_ptr lam_clo_t352;
  instr_clo(&lam_clo_t352, &lam_fun_t351, 2, zs_v81332, env[0]);
  return lam_clo_t352;
}

tll_ptr lam_fun_t355(tll_ptr n_v81329, tll_env env) {
  tll_ptr lam_clo_t354;
  instr_clo(&lam_clo_t354, &lam_fun_t353, 1, n_v81329);
  return lam_clo_t354;
}

tll_ptr lam_fun_t359(tll_ptr __v81339, tll_env env) {
  
  
  return 0;
}

tll_ptr lam_fun_t362(tll_ptr __v81342, tll_env env) {
  
  
  return 0;
}

tll_ptr fork_fun_t371(tll_env env) {
  tll_ptr app_ret_t370; tll_ptr call_ret_t369; tll_ptr fork_ret_t373;
  call_ret_t369 = cmsort_workerL_i53(env[2], env[1], env[0]);
  instr_app(&app_ret_t370, call_ret_t369, 0);
  instr_free_clo(call_ret_t369);
  fork_ret_t373 = app_ret_t370;
  instr_free_thread(env);
  return fork_ret_t373;
}

tll_ptr fork_fun_t378(tll_env env) {
  tll_ptr app_ret_t377; tll_ptr call_ret_t376; tll_ptr fork_ret_t380;
  call_ret_t376 = cmsort_workerL_i53(env[2], env[1], env[0]);
  instr_app(&app_ret_t377, call_ret_t376, 0);
  instr_free_clo(call_ret_t376);
  fork_ret_t380 = app_ret_t377;
  instr_free_thread(env);
  return fork_ret_t380;
}

tll_ptr lam_fun_t384(tll_ptr __v81347, tll_env env) {
  tll_ptr fork_ch_t372; tll_ptr fork_ch_t379; tll_ptr msg1_v81359;
  tll_ptr msg2_v81362; tll_ptr pf1_v81365; tll_ptr pf2_v81367;
  tll_ptr r1_v81360; tll_ptr r2_v81363; tll_ptr recv_msg_t368;
  tll_ptr recv_msg_t375; tll_ptr switch_ret_t374; tll_ptr switch_ret_t381;
  tll_ptr switch_ret_t382; tll_ptr switch_ret_t383; tll_ptr xs1_v81364;
  tll_ptr xs2_v81366;
  instr_fork(&fork_ch_t372, &fork_fun_t371, 2, env[1], env[2]);
  instr_recv(&recv_msg_t368, fork_ch_t372);
  switch(((tll_node)recv_msg_t368)->tag) {
    case 0:
      msg1_v81359 = ((tll_node)recv_msg_t368)->data[0];
      r1_v81360 = ((tll_node)recv_msg_t368)->data[1];
      instr_free_struct(recv_msg_t368);
      instr_fork(&fork_ch_t379, &fork_fun_t378, 2, env[0], env[2]);
      instr_recv(&recv_msg_t375, fork_ch_t379);
      switch(((tll_node)recv_msg_t375)->tag) {
        case 0:
          msg2_v81362 = ((tll_node)recv_msg_t375)->data[0];
          r2_v81363 = ((tll_node)recv_msg_t375)->data[1];
          instr_free_struct(recv_msg_t375);
          switch(((tll_node)msg1_v81359)->tag) {
            case 15:
              xs1_v81364 = ((tll_node)msg1_v81359)->data[0];
              pf1_v81365 = ((tll_node)msg1_v81359)->data[1];
              instr_free_struct(msg1_v81359);
              switch(((tll_node)msg2_v81362)->tag) {
                case 15:
                  xs2_v81366 = ((tll_node)msg2_v81362)->data[0];
                  pf2_v81367 = ((tll_node)msg2_v81362)->data[1];
                  instr_free_struct(msg2_v81362);
                  switch_ret_t383 = 0;
                  break;
              }
              switch_ret_t382 = switch_ret_t383;
              break;
          }
          switch_ret_t381 = switch_ret_t382;
          break;
      }
      switch_ret_t374 = switch_ret_t381;
      break;
  }
  return switch_ret_t374;
}

tll_ptr lam_fun_t386(tll_ptr __v81368, tll_env env) {
  
  
  return 0;
}

tll_ptr cmsort_workerL_i53(tll_ptr n_v81335, tll_ptr zs_v81336, tll_ptr c_v81337) {
  tll_ptr add_ret_t357; tll_ptr call_ret_t364; tll_ptr consUL_t365;
  tll_ptr consUL_t366; tll_ptr ifte_ret_t388; tll_ptr lam_clo_t360;
  tll_ptr lam_clo_t363; tll_ptr lam_clo_t385; tll_ptr lam_clo_t387;
  tll_ptr n0_v81338; tll_ptr switch_ret_t358; tll_ptr switch_ret_t361;
  tll_ptr switch_ret_t367; tll_ptr xs0_v81345; tll_ptr ys0_v81346;
  tll_ptr z0_v81340; tll_ptr z1_v81343; tll_ptr zs0_v81341;
  tll_ptr zs1_v81344;
  if (n_v81335) {
    add_ret_t357 = n_v81335 - 1;
    n0_v81338 = add_ret_t357;
    switch(((tll_node)zs_v81336)->tag) {
      case 11:
        instr_free_struct(zs_v81336);
        instr_clo(&lam_clo_t360, &lam_fun_t359, 0);
        switch_ret_t358 = lam_clo_t360;
        break;
      case 12:
        z0_v81340 = ((tll_node)zs_v81336)->data[0];
        zs0_v81341 = ((tll_node)zs_v81336)->data[1];
        instr_free_struct(zs_v81336);
        switch(((tll_node)zs0_v81341)->tag) {
          case 11:
            instr_free_struct(zs0_v81341);
            instr_clo(&lam_clo_t363, &lam_fun_t362, 0);
            switch_ret_t361 = lam_clo_t363;
            break;
          case 12:
            z1_v81343 = ((tll_node)zs0_v81341)->data[0];
            zs1_v81344 = ((tll_node)zs0_v81341)->data[1];
            instr_free_struct(zs0_v81341);
            instr_struct(&consUL_t365, 12, 2, z1_v81343, zs1_v81344);
            instr_struct(&consUL_t366, 12, 2, z0_v81340, consUL_t365);
            call_ret_t364 = splitL_i45(consUL_t366);
            switch(((tll_node)call_ret_t364)->tag) {
              case 0:
                xs0_v81345 = ((tll_node)call_ret_t364)->data[0];
                ys0_v81346 = ((tll_node)call_ret_t364)->data[1];
                instr_free_struct(call_ret_t364);
                instr_clo(&lam_clo_t385, &lam_fun_t384, 3,
                          ys0_v81346, xs0_v81345, n0_v81338);
                switch_ret_t367 = lam_clo_t385;
                break;
            }
            switch_ret_t361 = switch_ret_t367;
            break;
        }
        switch_ret_t358 = switch_ret_t361;
        break;
    }
    ifte_ret_t388 = switch_ret_t358;
  }
  else {
    instr_clo(&lam_clo_t387, &lam_fun_t386, 0);
    ifte_ret_t388 = lam_clo_t387;
  }
  return ifte_ret_t388;
}

tll_ptr lam_fun_t390(tll_ptr c_v81374, tll_env env) {
  tll_ptr call_ret_t389;
  call_ret_t389 = cmsort_workerL_i53(env[1], env[0], c_v81374);
  return call_ret_t389;
}

tll_ptr lam_fun_t392(tll_ptr zs_v81372, tll_env env) {
  tll_ptr lam_clo_t391;
  instr_clo(&lam_clo_t391, &lam_fun_t390, 2, zs_v81372, env[0]);
  return lam_clo_t391;
}

tll_ptr lam_fun_t394(tll_ptr n_v81369, tll_env env) {
  tll_ptr lam_clo_t393;
  instr_clo(&lam_clo_t393, &lam_fun_t392, 1, n_v81369);
  return lam_clo_t393;
}

tll_ptr fork_fun_t399(tll_env env) {
  tll_ptr app_ret_t398; tll_ptr call_ret_t397; tll_ptr fork_ret_t401;
  call_ret_t397 = cmsort_workerU_i54((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t398, call_ret_t397, 0);
  instr_free_clo(call_ret_t397);
  fork_ret_t401 = app_ret_t398;
  instr_free_thread(env);
  return fork_ret_t401;
}

tll_ptr lam_fun_t403(tll_ptr __v81376, tll_env env) {
  tll_ptr c_v81382; tll_ptr fork_ch_t400; tll_ptr msg_v81381;
  tll_ptr recv_msg_t396; tll_ptr switch_ret_t402;
  instr_fork(&fork_ch_t400, &fork_fun_t399, 1, env[0]);
  instr_recv(&recv_msg_t396, fork_ch_t400);
  switch(((tll_node)recv_msg_t396)->tag) {
    case 0:
      msg_v81381 = ((tll_node)recv_msg_t396)->data[0];
      c_v81382 = ((tll_node)recv_msg_t396)->data[1];
      instr_free_struct(recv_msg_t396);
      switch_ret_t402 = msg_v81381;
      break;
  }
  return switch_ret_t402;
}

tll_ptr cmsortU_i56(tll_ptr zs_v81375) {
  tll_ptr lam_clo_t404;
  instr_clo(&lam_clo_t404, &lam_fun_t403, 1, zs_v81375);
  return lam_clo_t404;
}

tll_ptr lam_fun_t406(tll_ptr zs_v81383, tll_env env) {
  tll_ptr call_ret_t405;
  call_ret_t405 = cmsortU_i56(zs_v81383);
  return call_ret_t405;
}

tll_ptr fork_fun_t411(tll_env env) {
  tll_ptr app_ret_t410; tll_ptr call_ret_t409; tll_ptr fork_ret_t413;
  call_ret_t409 = cmsort_workerL_i53((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t410, call_ret_t409, 0);
  instr_free_clo(call_ret_t409);
  fork_ret_t413 = app_ret_t410;
  instr_free_thread(env);
  return fork_ret_t413;
}

tll_ptr lam_fun_t415(tll_ptr __v81385, tll_env env) {
  tll_ptr c_v81391; tll_ptr fork_ch_t412; tll_ptr msg_v81390;
  tll_ptr recv_msg_t408; tll_ptr switch_ret_t414;
  instr_fork(&fork_ch_t412, &fork_fun_t411, 1, env[0]);
  instr_recv(&recv_msg_t408, fork_ch_t412);
  switch(((tll_node)recv_msg_t408)->tag) {
    case 0:
      msg_v81390 = ((tll_node)recv_msg_t408)->data[0];
      c_v81391 = ((tll_node)recv_msg_t408)->data[1];
      instr_free_struct(recv_msg_t408);
      switch_ret_t414 = msg_v81390;
      break;
  }
  return switch_ret_t414;
}

tll_ptr cmsortL_i55(tll_ptr zs_v81384) {
  tll_ptr lam_clo_t416;
  instr_clo(&lam_clo_t416, &lam_fun_t415, 1, zs_v81384);
  return lam_clo_t416;
}

tll_ptr lam_fun_t418(tll_ptr zs_v81392, tll_env env) {
  tll_ptr call_ret_t417;
  call_ret_t417 = cmsortL_i55(zs_v81392);
  return call_ret_t417;
}

tll_ptr mkListU_i58(tll_ptr n_v81393) {
  tll_ptr add_ret_t421; tll_ptr call_ret_t420; tll_ptr consUU_t422;
  tll_ptr ifte_ret_t424; tll_ptr nilUU_t423;
  if (n_v81393) {
    add_ret_t421 = n_v81393 - 1;
    call_ret_t420 = mkListU_i58(add_ret_t421);
    instr_struct(&consUU_t422, 14, 2, n_v81393, call_ret_t420);
    ifte_ret_t424 = consUU_t422;
  }
  else {
    instr_struct(&nilUU_t423, 13, 0);
    ifte_ret_t424 = nilUU_t423;
  }
  return ifte_ret_t424;
}

tll_ptr lam_fun_t426(tll_ptr n_v81394, tll_env env) {
  tll_ptr call_ret_t425;
  call_ret_t425 = mkListU_i58(n_v81394);
  return call_ret_t425;
}

tll_ptr mkListL_i57(tll_ptr n_v81395) {
  tll_ptr add_ret_t429; tll_ptr call_ret_t428; tll_ptr consUL_t430;
  tll_ptr ifte_ret_t432; tll_ptr nilUL_t431;
  if (n_v81395) {
    add_ret_t429 = n_v81395 - 1;
    call_ret_t428 = mkListL_i57(add_ret_t429);
    instr_struct(&consUL_t430, 12, 2, n_v81395, call_ret_t428);
    ifte_ret_t432 = consUL_t430;
  }
  else {
    instr_struct(&nilUL_t431, 11, 0);
    ifte_ret_t432 = nilUL_t431;
  }
  return ifte_ret_t432;
}

tll_ptr lam_fun_t434(tll_ptr n_v81396, tll_env env) {
  tll_ptr call_ret_t433;
  call_ret_t433 = mkListL_i57(n_v81396);
  return call_ret_t433;
}

tll_ptr free_i35(tll_ptr A_v81397, tll_ptr ls_v81398) {
  tll_ptr __v81399; tll_ptr call_ret_t437; tll_ptr ls_v81400;
  tll_ptr switch_ret_t436;
  switch(((tll_node)ls_v81398)->tag) {
    case 11:
      instr_free_struct(ls_v81398);
      switch_ret_t436 = 0;
      break;
    case 12:
      __v81399 = ((tll_node)ls_v81398)->data[0];
      ls_v81400 = ((tll_node)ls_v81398)->data[1];
      instr_free_struct(ls_v81398);
      call_ret_t437 = free_i35(0, ls_v81400);
      switch_ret_t436 = call_ret_t437;
      break;
  }
  return switch_ret_t436;
}

tll_ptr lam_fun_t439(tll_ptr ls_v81403, tll_env env) {
  tll_ptr call_ret_t438;
  call_ret_t438 = free_i35(env[0], ls_v81403);
  return call_ret_t438;
}

tll_ptr lam_fun_t441(tll_ptr A_v81401, tll_env env) {
  tll_ptr lam_clo_t440;
  instr_clo(&lam_clo_t440, &lam_fun_t439, 1, A_v81401);
  return lam_clo_t440;
}

int main() {
  instr_init();
  tll_ptr __v81405; tll_ptr app_ret_t445; tll_ptr call_ret_t443;
  tll_ptr call_ret_t444; tll_ptr lam_clo_t101; tll_ptr lam_clo_t111;
  tll_ptr lam_clo_t119; tll_ptr lam_clo_t12; tll_ptr lam_clo_t127;
  tll_ptr lam_clo_t133; tll_ptr lam_clo_t146; tll_ptr lam_clo_t159;
  tll_ptr lam_clo_t16; tll_ptr lam_clo_t172; tll_ptr lam_clo_t182;
  tll_ptr lam_clo_t192; tll_ptr lam_clo_t202; tll_ptr lam_clo_t211;
  tll_ptr lam_clo_t216; tll_ptr lam_clo_t221; tll_ptr lam_clo_t238;
  tll_ptr lam_clo_t255; tll_ptr lam_clo_t26; tll_ptr lam_clo_t271;
  tll_ptr lam_clo_t287; tll_ptr lam_clo_t302; tll_ptr lam_clo_t317;
  tll_ptr lam_clo_t356; tll_ptr lam_clo_t37; tll_ptr lam_clo_t395;
  tll_ptr lam_clo_t407; tll_ptr lam_clo_t419; tll_ptr lam_clo_t427;
  tll_ptr lam_clo_t435; tll_ptr lam_clo_t442; tll_ptr lam_clo_t48;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t6; tll_ptr lam_clo_t69;
  tll_ptr lam_clo_t74; tll_ptr lam_clo_t83; tll_ptr lam_clo_t92;
  tll_ptr sorted_v81404; tll_ptr switch_ret_t446;
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
  instr_clo(&lam_clo_t211, &lam_fun_t210, 0);
  readlineclo_i81 = lam_clo_t211;
  instr_clo(&lam_clo_t216, &lam_fun_t215, 0);
  printclo_i82 = lam_clo_t216;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 0);
  prerrclo_i83 = lam_clo_t221;
  instr_clo(&lam_clo_t238, &lam_fun_t237, 0);
  splitUclo_i84 = lam_clo_t238;
  instr_clo(&lam_clo_t255, &lam_fun_t254, 0);
  splitLclo_i85 = lam_clo_t255;
  instr_clo(&lam_clo_t271, &lam_fun_t270, 0);
  mergeUclo_i86 = lam_clo_t271;
  instr_clo(&lam_clo_t287, &lam_fun_t286, 0);
  mergeLclo_i87 = lam_clo_t287;
  instr_clo(&lam_clo_t302, &lam_fun_t301, 0);
  msortUclo_i88 = lam_clo_t302;
  instr_clo(&lam_clo_t317, &lam_fun_t316, 0);
  msortLclo_i89 = lam_clo_t317;
  instr_clo(&lam_clo_t356, &lam_fun_t355, 0);
  cmsort_workerUclo_i90 = lam_clo_t356;
  instr_clo(&lam_clo_t395, &lam_fun_t394, 0);
  cmsort_workerLclo_i91 = lam_clo_t395;
  instr_clo(&lam_clo_t407, &lam_fun_t406, 0);
  cmsortUclo_i92 = lam_clo_t407;
  instr_clo(&lam_clo_t419, &lam_fun_t418, 0);
  cmsortLclo_i93 = lam_clo_t419;
  instr_clo(&lam_clo_t427, &lam_fun_t426, 0);
  mkListUclo_i94 = lam_clo_t427;
  instr_clo(&lam_clo_t435, &lam_fun_t434, 0);
  mkListLclo_i95 = lam_clo_t435;
  instr_clo(&lam_clo_t442, &lam_fun_t441, 0);
  freeclo_i96 = lam_clo_t442;
  call_ret_t444 = mkListL_i57((tll_ptr)2000000);
  call_ret_t443 = cmsortL_i55(call_ret_t444);
  instr_app(&app_ret_t445, call_ret_t443, 0);
  instr_free_clo(call_ret_t443);
  switch(((tll_node)app_ret_t445)->tag) {
    case 15:
      sorted_v81404 = ((tll_node)app_ret_t445)->data[0];
      __v81405 = ((tll_node)app_ret_t445)->data[1];
      instr_free_struct(app_ret_t445);
      switch_ret_t446 = 0;
      break;
  }
  return 0;
}

