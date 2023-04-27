#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v82188, tll_ptr b2_v82189);
tll_ptr orb_i2(tll_ptr b1_v82193, tll_ptr b2_v82194);
tll_ptr notb_i3(tll_ptr b_v82198);
tll_ptr lten_i4(tll_ptr x_v82200, tll_ptr y_v82201);
tll_ptr gten_i5(tll_ptr x_v82207, tll_ptr y_v82208);
tll_ptr ltn_i6(tll_ptr x_v82214, tll_ptr y_v82215);
tll_ptr gtn_i7(tll_ptr x_v82221, tll_ptr y_v82222);
tll_ptr eqn_i8(tll_ptr x_v82228, tll_ptr y_v82229);
tll_ptr pred_i9(tll_ptr x_v82235);
tll_ptr addn_i10(tll_ptr x_v82238, tll_ptr y_v82239);
tll_ptr subn_i11(tll_ptr x_v82244, tll_ptr y_v82245);
tll_ptr muln_i12(tll_ptr x_v82250, tll_ptr y_v82251);
tll_ptr divn_i13(tll_ptr x_v82256, tll_ptr y_v82257);
tll_ptr modn_i14(tll_ptr x_v82261, tll_ptr y_v82262);
tll_ptr cats_i15(tll_ptr s1_v82266, tll_ptr s2_v82267);
tll_ptr strlen_i16(tll_ptr s_v82273);
tll_ptr lenUU_i40(tll_ptr A_v82277, tll_ptr xs_v82278);
tll_ptr lenUL_i39(tll_ptr A_v82286, tll_ptr xs_v82287);
tll_ptr lenLL_i37(tll_ptr A_v82295, tll_ptr xs_v82296);
tll_ptr appendUU_i44(tll_ptr A_v82304, tll_ptr xs_v82305, tll_ptr ys_v82306);
tll_ptr appendUL_i43(tll_ptr A_v82315, tll_ptr xs_v82316, tll_ptr ys_v82317);
tll_ptr appendLL_i41(tll_ptr A_v82326, tll_ptr xs_v82327, tll_ptr ys_v82328);
tll_ptr readline_i25(tll_ptr __v82337);
tll_ptr print_i26(tll_ptr s_v82352);
tll_ptr prerr_i27(tll_ptr s_v82363);
tll_ptr splitU_i46(tll_ptr zs_v82374);
tll_ptr splitL_i45(tll_ptr zs_v82382);
tll_ptr mergeU_i48(tll_ptr xs_v82390, tll_ptr ys_v82391);
tll_ptr mergeL_i47(tll_ptr xs_v82399, tll_ptr ys_v82400);
tll_ptr msortU_i50(tll_ptr zs_v82408);
tll_ptr msortL_i49(tll_ptr zs_v82416);
tll_ptr cmsort_workerU_i54(tll_ptr n_v82424, tll_ptr zs_v82425, tll_ptr c_v82426);
tll_ptr cmsort_workerL_i53(tll_ptr n_v82510, tll_ptr zs_v82511, tll_ptr c_v82512);
tll_ptr cmsortU_i56(tll_ptr zs_v82596);
tll_ptr cmsortL_i55(tll_ptr zs_v82611);
tll_ptr mkListU_i58(tll_ptr n_v82626);
tll_ptr mkListL_i57(tll_ptr n_v82629);
tll_ptr free_i35(tll_ptr A_v82632, tll_ptr ls_v82633);

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

tll_ptr andb_i1(tll_ptr b1_v82188, tll_ptr b2_v82189) {
  tll_ptr ifte_ret_t1;
  if (b1_v82188) {
    ifte_ret_t1 = b2_v82189;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v82192, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v82192);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v82190, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v82190);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v82193, tll_ptr b2_v82194) {
  tll_ptr ifte_ret_t7;
  if (b1_v82193) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v82194;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v82197, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v82197);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v82195, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v82195);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v82198) {
  tll_ptr ifte_ret_t13;
  if (b_v82198) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v82199, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v82199);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v82200, tll_ptr y_v82201) {
  tll_ptr __v82202; tll_ptr __v82203; tll_ptr add_ret_t18;
  tll_ptr add_ret_t19; tll_ptr call_ret_t17; tll_ptr ifte_ret_t20;
  tll_ptr ifte_ret_t21;
  __v82202 = x_v82200;
  if (__v82202) {
    __v82203 = y_v82201;
    if (__v82203) {
      add_ret_t18 = __v82202 - 1;
      add_ret_t19 = __v82203 - 1;
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

tll_ptr lam_fun_t23(tll_ptr y_v82206, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v82206);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v82204, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v82204);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v82207, tll_ptr y_v82208) {
  tll_ptr __v82209; tll_ptr __v82210; tll_ptr add_ret_t28;
  tll_ptr add_ret_t29; tll_ptr call_ret_t27; tll_ptr ifte_ret_t30;
  tll_ptr ifte_ret_t31; tll_ptr ifte_ret_t32;
  __v82209 = x_v82207;
  if (__v82209) {
    __v82210 = y_v82208;
    if (__v82210) {
      add_ret_t28 = __v82209 - 1;
      add_ret_t29 = __v82210 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v82208) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v82213, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v82213);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v82211, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v82211);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v82214, tll_ptr y_v82215) {
  tll_ptr __v82216; tll_ptr __v82217; tll_ptr add_ret_t39;
  tll_ptr add_ret_t40; tll_ptr call_ret_t38; tll_ptr ifte_ret_t41;
  tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t43;
  __v82216 = x_v82214;
  if (__v82216) {
    __v82217 = y_v82215;
    if (__v82217) {
      add_ret_t39 = __v82216 - 1;
      add_ret_t40 = __v82217 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v82215) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v82220, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v82220);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v82218, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v82218);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v82221, tll_ptr y_v82222) {
  tll_ptr __v82223; tll_ptr __v82224; tll_ptr add_ret_t50;
  tll_ptr add_ret_t51; tll_ptr call_ret_t49; tll_ptr ifte_ret_t52;
  tll_ptr ifte_ret_t53;
  __v82223 = x_v82221;
  if (__v82223) {
    __v82224 = y_v82222;
    if (__v82224) {
      add_ret_t50 = __v82223 - 1;
      add_ret_t51 = __v82224 - 1;
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

tll_ptr lam_fun_t55(tll_ptr y_v82227, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v82227);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v82225, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v82225);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v82228, tll_ptr y_v82229) {
  tll_ptr __v82230; tll_ptr __v82231; tll_ptr add_ret_t60;
  tll_ptr add_ret_t61; tll_ptr call_ret_t59; tll_ptr ifte_ret_t62;
  tll_ptr ifte_ret_t63; tll_ptr ifte_ret_t64;
  __v82230 = x_v82228;
  if (__v82230) {
    __v82231 = y_v82229;
    if (__v82231) {
      add_ret_t60 = __v82230 - 1;
      add_ret_t61 = __v82231 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v82229) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v82234, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v82234);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v82232, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v82232);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v82235) {
  tll_ptr __v82236; tll_ptr add_ret_t70; tll_ptr ifte_ret_t71;
  __v82236 = x_v82235;
  if (__v82236) {
    add_ret_t70 = __v82236 - 1;
    ifte_ret_t71 = add_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v82237, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v82237);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v82238, tll_ptr y_v82239) {
  tll_ptr __v82240; tll_ptr add_ret_t76; tll_ptr add_ret_t77;
  tll_ptr call_ret_t75; tll_ptr ifte_ret_t78;
  __v82240 = x_v82238;
  if (__v82240) {
    add_ret_t76 = __v82240 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v82239);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v82239;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v82243, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v82243);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v82241, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v82241);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v82244, tll_ptr y_v82245) {
  tll_ptr __v82246; tll_ptr add_ret_t86; tll_ptr call_ret_t84;
  tll_ptr call_ret_t85; tll_ptr ifte_ret_t87;
  __v82246 = y_v82245;
  if (__v82246) {
    call_ret_t85 = pred_i9(x_v82244);
    add_ret_t86 = __v82246 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v82244;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v82249, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v82249);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v82247, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v82247);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v82250, tll_ptr y_v82251) {
  tll_ptr __v82252; tll_ptr add_ret_t95; tll_ptr call_ret_t93;
  tll_ptr call_ret_t94; tll_ptr ifte_ret_t96;
  __v82252 = x_v82250;
  if (__v82252) {
    add_ret_t95 = __v82252 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v82251);
    call_ret_t93 = addn_i10(y_v82251, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v82255, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v82255);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v82253, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v82253);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v82256, tll_ptr y_v82257) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v82256, y_v82257);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v82256, y_v82257);
    call_ret_t103 = divn_i13(call_ret_t104, y_v82257);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v82260, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v82260);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v82258, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v82258);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v82261, tll_ptr y_v82262) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v82261, y_v82262);
  call_ret_t113 = muln_i12(call_ret_t114, y_v82262);
  call_ret_t112 = subn_i11(x_v82261, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v82265, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v82265);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v82263, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v82263);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v82266, tll_ptr s2_v82267) {
  tll_ptr String_t122; tll_ptr c_v82268; tll_ptr call_ret_t121;
  tll_ptr s1_v82269; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v82266)->tag) {
    case 2:
      switch_ret_t120 = s2_v82267;
      break;
    case 3:
      c_v82268 = ((tll_node)s1_v82266)->data[0];
      s1_v82269 = ((tll_node)s1_v82266)->data[1];
      call_ret_t121 = cats_i15(s1_v82269, s2_v82267);
      instr_struct(&String_t122, 3, 2, c_v82268, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v82272, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v82272);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v82270, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v82270);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v82273) {
  tll_ptr __v82274; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v82275; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v82273)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v82274 = ((tll_node)s_v82273)->data[0];
      s_v82275 = ((tll_node)s_v82273)->data[1];
      call_ret_t129 = strlen_i16(s_v82275);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v82276, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v82276);
  return call_ret_t131;
}

tll_ptr lenUU_i40(tll_ptr A_v82277, tll_ptr xs_v82278) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v82281; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v82279; tll_ptr xs_v82280; tll_ptr xs_v82282;
  switch(((tll_node)xs_v82278)->tag) {
    case 13:
      instr_struct(&nilUU_t135, 13, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 14:
      x_v82279 = ((tll_node)xs_v82278)->data[0];
      xs_v82280 = ((tll_node)xs_v82278)->data[1];
      call_ret_t137 = lenUU_i40(0, xs_v82280);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v82281 = ((tll_node)call_ret_t137)->data[0];
          xs_v82282 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v82281 + 1;
          instr_struct(&consUU_t140, 14, 2, x_v82279, xs_v82282);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v82285, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i40(env[0], xs_v82285);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v82283, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v82283);
  return lam_clo_t144;
}

tll_ptr lenUL_i39(tll_ptr A_v82286, tll_ptr xs_v82287) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v82290; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v82288; tll_ptr xs_v82289; tll_ptr xs_v82291;
  switch(((tll_node)xs_v82287)->tag) {
    case 11:
      instr_free_struct(xs_v82287);
      instr_struct(&nilUL_t148, 11, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 12:
      x_v82288 = ((tll_node)xs_v82287)->data[0];
      xs_v82289 = ((tll_node)xs_v82287)->data[1];
      instr_free_struct(xs_v82287);
      call_ret_t150 = lenUL_i39(0, xs_v82289);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v82290 = ((tll_node)call_ret_t150)->data[0];
          xs_v82291 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v82290 + 1;
          instr_struct(&consUL_t153, 12, 2, x_v82288, xs_v82291);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v82294, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i39(env[0], xs_v82294);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v82292, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v82292);
  return lam_clo_t157;
}

tll_ptr lenLL_i37(tll_ptr A_v82295, tll_ptr xs_v82296) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v82299; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v82297; tll_ptr xs_v82298; tll_ptr xs_v82300;
  switch(((tll_node)xs_v82296)->tag) {
    case 7:
      instr_free_struct(xs_v82296);
      instr_struct(&nilLL_t161, 7, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 8:
      x_v82297 = ((tll_node)xs_v82296)->data[0];
      xs_v82298 = ((tll_node)xs_v82296)->data[1];
      instr_free_struct(xs_v82296);
      call_ret_t163 = lenLL_i37(0, xs_v82298);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v82299 = ((tll_node)call_ret_t163)->data[0];
          xs_v82300 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v82299 + 1;
          instr_struct(&consLL_t166, 8, 2, x_v82297, xs_v82300);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v82303, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i37(env[0], xs_v82303);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v82301, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v82301);
  return lam_clo_t170;
}

tll_ptr appendUU_i44(tll_ptr A_v82304, tll_ptr xs_v82305, tll_ptr ys_v82306) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v82307; tll_ptr xs_v82308;
  switch(((tll_node)xs_v82305)->tag) {
    case 13:
      switch_ret_t173 = ys_v82306;
      break;
    case 14:
      x_v82307 = ((tll_node)xs_v82305)->data[0];
      xs_v82308 = ((tll_node)xs_v82305)->data[1];
      call_ret_t174 = appendUU_i44(0, xs_v82308, ys_v82306);
      instr_struct(&consUU_t175, 14, 2, x_v82307, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v82314, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i44(env[1], env[0], ys_v82314);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v82312, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v82312, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v82309, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v82309);
  return lam_clo_t180;
}

tll_ptr appendUL_i43(tll_ptr A_v82315, tll_ptr xs_v82316, tll_ptr ys_v82317) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v82318; tll_ptr xs_v82319;
  switch(((tll_node)xs_v82316)->tag) {
    case 11:
      instr_free_struct(xs_v82316);
      switch_ret_t183 = ys_v82317;
      break;
    case 12:
      x_v82318 = ((tll_node)xs_v82316)->data[0];
      xs_v82319 = ((tll_node)xs_v82316)->data[1];
      instr_free_struct(xs_v82316);
      call_ret_t184 = appendUL_i43(0, xs_v82319, ys_v82317);
      instr_struct(&consUL_t185, 12, 2, x_v82318, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v82325, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i43(env[1], env[0], ys_v82325);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v82323, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v82323, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v82320, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v82320);
  return lam_clo_t190;
}

tll_ptr appendLL_i41(tll_ptr A_v82326, tll_ptr xs_v82327, tll_ptr ys_v82328) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v82329; tll_ptr xs_v82330;
  switch(((tll_node)xs_v82327)->tag) {
    case 7:
      instr_free_struct(xs_v82327);
      switch_ret_t193 = ys_v82328;
      break;
    case 8:
      x_v82329 = ((tll_node)xs_v82327)->data[0];
      xs_v82330 = ((tll_node)xs_v82327)->data[1];
      instr_free_struct(xs_v82327);
      call_ret_t194 = appendLL_i41(0, xs_v82330, ys_v82328);
      instr_struct(&consLL_t195, 8, 2, x_v82329, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v82336, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i41(env[1], env[0], ys_v82336);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v82334, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v82334, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v82331, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v82331);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v82338, tll_env env) {
  tll_ptr __v82347; tll_ptr ch_v82345; tll_ptr ch_v82346; tll_ptr ch_v82349;
  tll_ptr ch_v82350; tll_ptr prim_ch_t203; tll_ptr recv_msg_t205;
  tll_ptr s_v82348; tll_ptr send_ch_t204; tll_ptr send_ch_t207;
  tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v82345 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v82345, (tll_ptr)1);
  ch_v82346 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v82346);
  __v82347 = recv_msg_t205;
  switch(((tll_node)__v82347)->tag) {
    case 0:
      s_v82348 = ((tll_node)__v82347)->data[0];
      ch_v82349 = ((tll_node)__v82347)->data[1];
      instr_free_struct(__v82347);
      instr_send(&send_ch_t207, ch_v82349, (tll_ptr)0);
      ch_v82350 = send_ch_t207;
      switch_ret_t206 = s_v82348;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v82337) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v82351, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v82351);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v82353, tll_env env) {
  tll_ptr ch_v82358; tll_ptr ch_v82359; tll_ptr ch_v82360; tll_ptr ch_v82361;
  tll_ptr prim_ch_t213; tll_ptr send_ch_t214; tll_ptr send_ch_t215;
  tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v82358 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v82358, (tll_ptr)1);
  ch_v82359 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v82359, env[0]);
  ch_v82360 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v82360, (tll_ptr)0);
  ch_v82361 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v82352) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v82352);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v82362, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v82362);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v82364, tll_env env) {
  tll_ptr ch_v82369; tll_ptr ch_v82370; tll_ptr ch_v82371; tll_ptr ch_v82372;
  tll_ptr prim_ch_t222; tll_ptr send_ch_t223; tll_ptr send_ch_t224;
  tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v82369 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v82369, (tll_ptr)1);
  ch_v82370 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v82370, env[0]);
  ch_v82371 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v82371, (tll_ptr)0);
  ch_v82372 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v82363) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v82363);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v82373, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v82373);
  return call_ret_t228;
}

tll_ptr splitU_i46(tll_ptr zs_v82374) {
  tll_ptr call_ret_t240; tll_ptr consUU_t237; tll_ptr consUU_t242;
  tll_ptr consUU_t243; tll_ptr nilUU_t232; tll_ptr nilUU_t233;
  tll_ptr nilUU_t236; tll_ptr nilUU_t238; tll_ptr pair_struct_t234;
  tll_ptr pair_struct_t239; tll_ptr pair_struct_t244;
  tll_ptr switch_ret_t231; tll_ptr switch_ret_t235; tll_ptr switch_ret_t241;
  tll_ptr x_v82375; tll_ptr xs_v82379; tll_ptr y_v82377; tll_ptr ys_v82380;
  tll_ptr zs_v82376; tll_ptr zs_v82378;
  switch(((tll_node)zs_v82374)->tag) {
    case 13:
      instr_struct(&nilUU_t232, 13, 0);
      instr_struct(&nilUU_t233, 13, 0);
      instr_struct(&pair_struct_t234, 0, 2, nilUU_t232, nilUU_t233);
      switch_ret_t231 = pair_struct_t234;
      break;
    case 14:
      x_v82375 = ((tll_node)zs_v82374)->data[0];
      zs_v82376 = ((tll_node)zs_v82374)->data[1];
      switch(((tll_node)zs_v82376)->tag) {
        case 13:
          instr_struct(&nilUU_t236, 13, 0);
          instr_struct(&consUU_t237, 14, 2, x_v82375, nilUU_t236);
          instr_struct(&nilUU_t238, 13, 0);
          instr_struct(&pair_struct_t239, 0, 2, consUU_t237, nilUU_t238);
          switch_ret_t235 = pair_struct_t239;
          break;
        case 14:
          y_v82377 = ((tll_node)zs_v82376)->data[0];
          zs_v82378 = ((tll_node)zs_v82376)->data[1];
          call_ret_t240 = splitU_i46(zs_v82378);
          switch(((tll_node)call_ret_t240)->tag) {
            case 0:
              xs_v82379 = ((tll_node)call_ret_t240)->data[0];
              ys_v82380 = ((tll_node)call_ret_t240)->data[1];
              instr_free_struct(call_ret_t240);
              instr_struct(&consUU_t242, 14, 2, x_v82375, xs_v82379);
              instr_struct(&consUU_t243, 14, 2, y_v82377, ys_v82380);
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

tll_ptr lam_fun_t246(tll_ptr zs_v82381, tll_env env) {
  tll_ptr call_ret_t245;
  call_ret_t245 = splitU_i46(zs_v82381);
  return call_ret_t245;
}

tll_ptr splitL_i45(tll_ptr zs_v82382) {
  tll_ptr call_ret_t257; tll_ptr consUL_t254; tll_ptr consUL_t259;
  tll_ptr consUL_t260; tll_ptr nilUL_t249; tll_ptr nilUL_t250;
  tll_ptr nilUL_t253; tll_ptr nilUL_t255; tll_ptr pair_struct_t251;
  tll_ptr pair_struct_t256; tll_ptr pair_struct_t261;
  tll_ptr switch_ret_t248; tll_ptr switch_ret_t252; tll_ptr switch_ret_t258;
  tll_ptr x_v82383; tll_ptr xs_v82387; tll_ptr y_v82385; tll_ptr ys_v82388;
  tll_ptr zs_v82384; tll_ptr zs_v82386;
  switch(((tll_node)zs_v82382)->tag) {
    case 11:
      instr_free_struct(zs_v82382);
      instr_struct(&nilUL_t249, 11, 0);
      instr_struct(&nilUL_t250, 11, 0);
      instr_struct(&pair_struct_t251, 0, 2, nilUL_t249, nilUL_t250);
      switch_ret_t248 = pair_struct_t251;
      break;
    case 12:
      x_v82383 = ((tll_node)zs_v82382)->data[0];
      zs_v82384 = ((tll_node)zs_v82382)->data[1];
      instr_free_struct(zs_v82382);
      switch(((tll_node)zs_v82384)->tag) {
        case 11:
          instr_free_struct(zs_v82384);
          instr_struct(&nilUL_t253, 11, 0);
          instr_struct(&consUL_t254, 12, 2, x_v82383, nilUL_t253);
          instr_struct(&nilUL_t255, 11, 0);
          instr_struct(&pair_struct_t256, 0, 2, consUL_t254, nilUL_t255);
          switch_ret_t252 = pair_struct_t256;
          break;
        case 12:
          y_v82385 = ((tll_node)zs_v82384)->data[0];
          zs_v82386 = ((tll_node)zs_v82384)->data[1];
          instr_free_struct(zs_v82384);
          call_ret_t257 = splitL_i45(zs_v82386);
          switch(((tll_node)call_ret_t257)->tag) {
            case 0:
              xs_v82387 = ((tll_node)call_ret_t257)->data[0];
              ys_v82388 = ((tll_node)call_ret_t257)->data[1];
              instr_free_struct(call_ret_t257);
              instr_struct(&consUL_t259, 12, 2, x_v82383, xs_v82387);
              instr_struct(&consUL_t260, 12, 2, y_v82385, ys_v82388);
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

tll_ptr lam_fun_t263(tll_ptr zs_v82389, tll_env env) {
  tll_ptr call_ret_t262;
  call_ret_t262 = splitL_i45(zs_v82389);
  return call_ret_t262;
}

tll_ptr mergeU_i48(tll_ptr xs_v82390, tll_ptr ys_v82391) {
  tll_ptr call_ret_t268; tll_ptr call_ret_t269; tll_ptr call_ret_t272;
  tll_ptr consUU_t267; tll_ptr consUU_t270; tll_ptr consUU_t271;
  tll_ptr consUU_t273; tll_ptr consUU_t274; tll_ptr ifte_ret_t275;
  tll_ptr switch_ret_t265; tll_ptr switch_ret_t266; tll_ptr x_v82392;
  tll_ptr xs0_v82393; tll_ptr y_v82394; tll_ptr ys0_v82395;
  switch(((tll_node)xs_v82390)->tag) {
    case 13:
      switch_ret_t265 = ys_v82391;
      break;
    case 14:
      x_v82392 = ((tll_node)xs_v82390)->data[0];
      xs0_v82393 = ((tll_node)xs_v82390)->data[1];
      switch(((tll_node)ys_v82391)->tag) {
        case 13:
          instr_struct(&consUU_t267, 14, 2, x_v82392, xs0_v82393);
          switch_ret_t266 = consUU_t267;
          break;
        case 14:
          y_v82394 = ((tll_node)ys_v82391)->data[0];
          ys0_v82395 = ((tll_node)ys_v82391)->data[1];
          call_ret_t268 = lten_i4(x_v82392, y_v82394);
          if (call_ret_t268) {
            instr_struct(&consUU_t270, 14, 2, y_v82394, ys0_v82395);
            call_ret_t269 = mergeU_i48(xs0_v82393, consUU_t270);
            instr_struct(&consUU_t271, 14, 2, x_v82392, call_ret_t269);
            ifte_ret_t275 = consUU_t271;
          }
          else {
            instr_struct(&consUU_t273, 14, 2, x_v82392, xs0_v82393);
            call_ret_t272 = mergeU_i48(consUU_t273, ys0_v82395);
            instr_struct(&consUU_t274, 14, 2, y_v82394, call_ret_t272);
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

tll_ptr lam_fun_t277(tll_ptr ys_v82398, tll_env env) {
  tll_ptr call_ret_t276;
  call_ret_t276 = mergeU_i48(env[0], ys_v82398);
  return call_ret_t276;
}

tll_ptr lam_fun_t279(tll_ptr xs_v82396, tll_env env) {
  tll_ptr lam_clo_t278;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 1, xs_v82396);
  return lam_clo_t278;
}

tll_ptr mergeL_i47(tll_ptr xs_v82399, tll_ptr ys_v82400) {
  tll_ptr call_ret_t284; tll_ptr call_ret_t285; tll_ptr call_ret_t288;
  tll_ptr consUL_t283; tll_ptr consUL_t286; tll_ptr consUL_t287;
  tll_ptr consUL_t289; tll_ptr consUL_t290; tll_ptr ifte_ret_t291;
  tll_ptr switch_ret_t281; tll_ptr switch_ret_t282; tll_ptr x_v82401;
  tll_ptr xs0_v82402; tll_ptr y_v82403; tll_ptr ys0_v82404;
  switch(((tll_node)xs_v82399)->tag) {
    case 11:
      instr_free_struct(xs_v82399);
      switch_ret_t281 = ys_v82400;
      break;
    case 12:
      x_v82401 = ((tll_node)xs_v82399)->data[0];
      xs0_v82402 = ((tll_node)xs_v82399)->data[1];
      instr_free_struct(xs_v82399);
      switch(((tll_node)ys_v82400)->tag) {
        case 11:
          instr_free_struct(ys_v82400);
          instr_struct(&consUL_t283, 12, 2, x_v82401, xs0_v82402);
          switch_ret_t282 = consUL_t283;
          break;
        case 12:
          y_v82403 = ((tll_node)ys_v82400)->data[0];
          ys0_v82404 = ((tll_node)ys_v82400)->data[1];
          instr_free_struct(ys_v82400);
          call_ret_t284 = lten_i4(x_v82401, y_v82403);
          if (call_ret_t284) {
            instr_struct(&consUL_t286, 12, 2, y_v82403, ys0_v82404);
            call_ret_t285 = mergeL_i47(xs0_v82402, consUL_t286);
            instr_struct(&consUL_t287, 12, 2, x_v82401, call_ret_t285);
            ifte_ret_t291 = consUL_t287;
          }
          else {
            instr_struct(&consUL_t289, 12, 2, x_v82401, xs0_v82402);
            call_ret_t288 = mergeL_i47(consUL_t289, ys0_v82404);
            instr_struct(&consUL_t290, 12, 2, y_v82403, call_ret_t288);
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

tll_ptr lam_fun_t293(tll_ptr ys_v82407, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = mergeL_i47(env[0], ys_v82407);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v82405, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 1, xs_v82405);
  return lam_clo_t294;
}

tll_ptr msortU_i50(tll_ptr zs_v82408) {
  tll_ptr call_ret_t302; tll_ptr call_ret_t306; tll_ptr call_ret_t307;
  tll_ptr call_ret_t308; tll_ptr consUU_t301; tll_ptr consUU_t303;
  tll_ptr consUU_t304; tll_ptr nilUU_t298; tll_ptr nilUU_t300;
  tll_ptr switch_ret_t297; tll_ptr switch_ret_t299; tll_ptr switch_ret_t305;
  tll_ptr x_v82409; tll_ptr xs_v82413; tll_ptr y_v82411; tll_ptr ys_v82414;
  tll_ptr zs_v82410; tll_ptr zs_v82412;
  switch(((tll_node)zs_v82408)->tag) {
    case 13:
      instr_struct(&nilUU_t298, 13, 0);
      switch_ret_t297 = nilUU_t298;
      break;
    case 14:
      x_v82409 = ((tll_node)zs_v82408)->data[0];
      zs_v82410 = ((tll_node)zs_v82408)->data[1];
      switch(((tll_node)zs_v82410)->tag) {
        case 13:
          instr_struct(&nilUU_t300, 13, 0);
          instr_struct(&consUU_t301, 14, 2, x_v82409, nilUU_t300);
          switch_ret_t299 = consUU_t301;
          break;
        case 14:
          y_v82411 = ((tll_node)zs_v82410)->data[0];
          zs_v82412 = ((tll_node)zs_v82410)->data[1];
          instr_struct(&consUU_t303, 14, 2, y_v82411, zs_v82412);
          instr_struct(&consUU_t304, 14, 2, x_v82409, consUU_t303);
          call_ret_t302 = splitU_i46(consUU_t304);
          switch(((tll_node)call_ret_t302)->tag) {
            case 0:
              xs_v82413 = ((tll_node)call_ret_t302)->data[0];
              ys_v82414 = ((tll_node)call_ret_t302)->data[1];
              instr_free_struct(call_ret_t302);
              call_ret_t307 = msortU_i50(xs_v82413);
              call_ret_t308 = msortU_i50(ys_v82414);
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

tll_ptr lam_fun_t310(tll_ptr zs_v82415, tll_env env) {
  tll_ptr call_ret_t309;
  call_ret_t309 = msortU_i50(zs_v82415);
  return call_ret_t309;
}

tll_ptr msortL_i49(tll_ptr zs_v82416) {
  tll_ptr call_ret_t317; tll_ptr call_ret_t321; tll_ptr call_ret_t322;
  tll_ptr call_ret_t323; tll_ptr consUL_t316; tll_ptr consUL_t318;
  tll_ptr consUL_t319; tll_ptr nilUL_t313; tll_ptr nilUL_t315;
  tll_ptr switch_ret_t312; tll_ptr switch_ret_t314; tll_ptr switch_ret_t320;
  tll_ptr x_v82417; tll_ptr xs_v82421; tll_ptr y_v82419; tll_ptr ys_v82422;
  tll_ptr zs_v82418; tll_ptr zs_v82420;
  switch(((tll_node)zs_v82416)->tag) {
    case 11:
      instr_free_struct(zs_v82416);
      instr_struct(&nilUL_t313, 11, 0);
      switch_ret_t312 = nilUL_t313;
      break;
    case 12:
      x_v82417 = ((tll_node)zs_v82416)->data[0];
      zs_v82418 = ((tll_node)zs_v82416)->data[1];
      instr_free_struct(zs_v82416);
      switch(((tll_node)zs_v82418)->tag) {
        case 11:
          instr_free_struct(zs_v82418);
          instr_struct(&nilUL_t315, 11, 0);
          instr_struct(&consUL_t316, 12, 2, x_v82417, nilUL_t315);
          switch_ret_t314 = consUL_t316;
          break;
        case 12:
          y_v82419 = ((tll_node)zs_v82418)->data[0];
          zs_v82420 = ((tll_node)zs_v82418)->data[1];
          instr_free_struct(zs_v82418);
          instr_struct(&consUL_t318, 12, 2, y_v82419, zs_v82420);
          instr_struct(&consUL_t319, 12, 2, x_v82417, consUL_t318);
          call_ret_t317 = splitL_i45(consUL_t319);
          switch(((tll_node)call_ret_t317)->tag) {
            case 0:
              xs_v82421 = ((tll_node)call_ret_t317)->data[0];
              ys_v82422 = ((tll_node)call_ret_t317)->data[1];
              instr_free_struct(call_ret_t317);
              call_ret_t322 = msortL_i49(xs_v82421);
              call_ret_t323 = msortL_i49(ys_v82422);
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

tll_ptr lam_fun_t325(tll_ptr zs_v82423, tll_env env) {
  tll_ptr call_ret_t324;
  call_ret_t324 = msortL_i49(zs_v82423);
  return call_ret_t324;
}

tll_ptr lam_fun_t332(tll_ptr __v82429, tll_env env) {
  tll_ptr UniqU_t331; tll_ptr c_v82431; tll_ptr nilUU_t330;
  tll_ptr send_ch_t329;
  instr_struct(&nilUU_t330, 13, 0);
  instr_struct(&UniqU_t331, 16, 2, nilUU_t330, 0);
  instr_send(&send_ch_t329, env[0], UniqU_t331);
  c_v82431 = send_ch_t329;
  return 0;
}

tll_ptr lam_fun_t339(tll_ptr __v82459, tll_env env) {
  tll_ptr UniqU_t338; tll_ptr c_v82461; tll_ptr consUU_t337;
  tll_ptr nilUU_t336; tll_ptr send_ch_t335;
  instr_struct(&nilUU_t336, 13, 0);
  instr_struct(&consUU_t337, 14, 2, env[1], nilUU_t336);
  instr_struct(&UniqU_t338, 16, 2, consUU_t337, 0);
  instr_send(&send_ch_t335, env[0], UniqU_t338);
  c_v82461 = send_ch_t335;
  return 0;
}

tll_ptr fork_fun_t347(tll_env env) {
  tll_ptr app_ret_t346; tll_ptr call_ret_t345; tll_ptr fork_ret_t349;
  call_ret_t345 = cmsort_workerU_i54(env[2], env[1], env[0]);
  instr_app(&app_ret_t346, call_ret_t345, 0);
  instr_free_clo(call_ret_t345);
  fork_ret_t349 = app_ret_t346;
  instr_free_thread(env);
  return fork_ret_t349;
}

tll_ptr fork_fun_t352(tll_env env) {
  tll_ptr app_ret_t351; tll_ptr call_ret_t350; tll_ptr fork_ret_t354;
  call_ret_t350 = cmsort_workerU_i54(env[2], env[1], env[0]);
  instr_app(&app_ret_t351, call_ret_t350, 0);
  instr_free_clo(call_ret_t350);
  fork_ret_t354 = app_ret_t351;
  instr_free_thread(env);
  return fork_ret_t354;
}

tll_ptr lam_fun_t366(tll_ptr __v82466, tll_env env) {
  tll_ptr UniqU_t363; tll_ptr __v82488; tll_ptr __v82491; tll_ptr __v82499;
  tll_ptr __v82500; tll_ptr c_v82498; tll_ptr call_ret_t362;
  tll_ptr close_tmp_t364; tll_ptr close_tmp_t365; tll_ptr fork_ch_t348;
  tll_ptr fork_ch_t353; tll_ptr msg1_v82489; tll_ptr msg2_v82492;
  tll_ptr pf1_v82495; tll_ptr pf2_v82497; tll_ptr r1_v82484;
  tll_ptr r1_v82490; tll_ptr r2_v82486; tll_ptr r2_v82493;
  tll_ptr recv_msg_t355; tll_ptr recv_msg_t357; tll_ptr send_ch_t361;
  tll_ptr switch_ret_t356; tll_ptr switch_ret_t358; tll_ptr switch_ret_t359;
  tll_ptr switch_ret_t360; tll_ptr xs1_v82494; tll_ptr xs2_v82496;
  instr_fork(&fork_ch_t348, &fork_fun_t347, 2, env[1], env[3]);
  r1_v82484 = fork_ch_t348;
  instr_fork(&fork_ch_t353, &fork_fun_t352, 2, env[0], env[3]);
  r2_v82486 = fork_ch_t353;
  instr_recv(&recv_msg_t355, r1_v82484);
  __v82488 = recv_msg_t355;
  switch(((tll_node)__v82488)->tag) {
    case 0:
      msg1_v82489 = ((tll_node)__v82488)->data[0];
      r1_v82490 = ((tll_node)__v82488)->data[1];
      instr_free_struct(__v82488);
      instr_recv(&recv_msg_t357, r2_v82486);
      __v82491 = recv_msg_t357;
      switch(((tll_node)__v82491)->tag) {
        case 0:
          msg2_v82492 = ((tll_node)__v82491)->data[0];
          r2_v82493 = ((tll_node)__v82491)->data[1];
          instr_free_struct(__v82491);
          switch(((tll_node)msg1_v82489)->tag) {
            case 16:
              xs1_v82494 = ((tll_node)msg1_v82489)->data[0];
              pf1_v82495 = ((tll_node)msg1_v82489)->data[1];
              switch(((tll_node)msg2_v82492)->tag) {
                case 16:
                  xs2_v82496 = ((tll_node)msg2_v82492)->data[0];
                  pf2_v82497 = ((tll_node)msg2_v82492)->data[1];
                  call_ret_t362 = mergeU_i48(xs1_v82494, xs2_v82496);
                  instr_struct(&UniqU_t363, 16, 2, call_ret_t362, 0);
                  instr_send(&send_ch_t361, env[2], UniqU_t363);
                  c_v82498 = send_ch_t361;
                  instr_close(&close_tmp_t364, r1_v82490);
                  __v82499 = close_tmp_t364;
                  instr_close(&close_tmp_t365, r2_v82493);
                  __v82500 = close_tmp_t365;
                  switch_ret_t360 = 0;
                  break;
              }
              switch_ret_t359 = switch_ret_t360;
              break;
          }
          switch_ret_t358 = switch_ret_t359;
          break;
      }
      switch_ret_t356 = switch_ret_t358;
      break;
  }
  return switch_ret_t356;
}

tll_ptr lam_fun_t368(tll_ptr c_v82434, tll_env env) {
  tll_ptr call_ret_t341; tll_ptr consUU_t342; tll_ptr consUU_t343;
  tll_ptr lam_clo_t340; tll_ptr lam_clo_t367; tll_ptr switch_ret_t334;
  tll_ptr switch_ret_t344; tll_ptr xs0_v82464; tll_ptr ys0_v82465;
  tll_ptr z1_v82462; tll_ptr zs1_v82463;
  switch(((tll_node)env[0])->tag) {
    case 13:
      instr_clo(&lam_clo_t340, &lam_fun_t339, 2, c_v82434, env[1]);
      switch_ret_t334 = lam_clo_t340;
      break;
    case 14:
      z1_v82462 = ((tll_node)env[0])->data[0];
      zs1_v82463 = ((tll_node)env[0])->data[1];
      instr_struct(&consUU_t342, 14, 2, z1_v82462, zs1_v82463);
      instr_struct(&consUU_t343, 14, 2, env[1], consUU_t342);
      call_ret_t341 = splitU_i46(consUU_t343);
      switch(((tll_node)call_ret_t341)->tag) {
        case 0:
          xs0_v82464 = ((tll_node)call_ret_t341)->data[0];
          ys0_v82465 = ((tll_node)call_ret_t341)->data[1];
          instr_free_struct(call_ret_t341);
          instr_clo(&lam_clo_t367, &lam_fun_t366, 4,
                    ys0_v82465, xs0_v82464, c_v82434, env[2]);
          switch_ret_t344 = lam_clo_t367;
          break;
      }
      switch_ret_t334 = switch_ret_t344;
      break;
  }
  return switch_ret_t334;
}

tll_ptr lam_fun_t374(tll_ptr __v82501, tll_env env) {
  tll_ptr UniqU_t373; tll_ptr c_v82503; tll_ptr call_ret_t372;
  tll_ptr send_ch_t371;
  call_ret_t372 = msortU_i50(env[1]);
  instr_struct(&UniqU_t373, 16, 2, call_ret_t372, 0);
  instr_send(&send_ch_t371, env[0], UniqU_t373);
  c_v82503 = send_ch_t371;
  return 0;
}

tll_ptr cmsort_workerU_i54(tll_ptr n_v82424, tll_ptr zs_v82425, tll_ptr c_v82426) {
  tll_ptr __v82427; tll_ptr add_ret_t327; tll_ptr app_ret_t370;
  tll_ptr ifte_ret_t376; tll_ptr lam_clo_t333; tll_ptr lam_clo_t369;
  tll_ptr lam_clo_t375; tll_ptr n0_v82428; tll_ptr switch_ret_t328;
  tll_ptr z0_v82432; tll_ptr zs0_v82433;
  __v82427 = n_v82424;
  if (__v82427) {
    add_ret_t327 = __v82427 - 1;
    n0_v82428 = add_ret_t327;
    switch(((tll_node)zs_v82425)->tag) {
      case 13:
        instr_clo(&lam_clo_t333, &lam_fun_t332, 1, c_v82426);
        switch_ret_t328 = lam_clo_t333;
        break;
      case 14:
        z0_v82432 = ((tll_node)zs_v82425)->data[0];
        zs0_v82433 = ((tll_node)zs_v82425)->data[1];
        instr_clo(&lam_clo_t369, &lam_fun_t368, 3,
                  zs0_v82433, z0_v82432, n0_v82428);
        instr_app(&app_ret_t370, lam_clo_t369, c_v82426);
        switch_ret_t328 = app_ret_t370;
        break;
    }
    ifte_ret_t376 = switch_ret_t328;
  }
  else {
    instr_clo(&lam_clo_t375, &lam_fun_t374, 2, c_v82426, zs_v82425);
    ifte_ret_t376 = lam_clo_t375;
  }
  return ifte_ret_t376;
}

tll_ptr lam_fun_t378(tll_ptr c_v82509, tll_env env) {
  tll_ptr call_ret_t377;
  call_ret_t377 = cmsort_workerU_i54(env[1], env[0], c_v82509);
  return call_ret_t377;
}

tll_ptr lam_fun_t380(tll_ptr zs_v82507, tll_env env) {
  tll_ptr lam_clo_t379;
  instr_clo(&lam_clo_t379, &lam_fun_t378, 2, zs_v82507, env[0]);
  return lam_clo_t379;
}

tll_ptr lam_fun_t382(tll_ptr n_v82504, tll_env env) {
  tll_ptr lam_clo_t381;
  instr_clo(&lam_clo_t381, &lam_fun_t380, 1, n_v82504);
  return lam_clo_t381;
}

tll_ptr lam_fun_t389(tll_ptr __v82515, tll_env env) {
  tll_ptr UniqL_t388; tll_ptr c_v82517; tll_ptr nilUL_t387;
  tll_ptr send_ch_t386;
  instr_struct(&nilUL_t387, 11, 0);
  instr_struct(&UniqL_t388, 15, 2, nilUL_t387, 0);
  instr_send(&send_ch_t386, env[0], UniqL_t388);
  c_v82517 = send_ch_t386;
  return 0;
}

tll_ptr lam_fun_t396(tll_ptr __v82545, tll_env env) {
  tll_ptr UniqL_t395; tll_ptr c_v82547; tll_ptr consUL_t394;
  tll_ptr nilUL_t393; tll_ptr send_ch_t392;
  instr_struct(&nilUL_t393, 11, 0);
  instr_struct(&consUL_t394, 12, 2, env[1], nilUL_t393);
  instr_struct(&UniqL_t395, 15, 2, consUL_t394, 0);
  instr_send(&send_ch_t392, env[0], UniqL_t395);
  c_v82547 = send_ch_t392;
  return 0;
}

tll_ptr fork_fun_t404(tll_env env) {
  tll_ptr app_ret_t403; tll_ptr call_ret_t402; tll_ptr fork_ret_t406;
  call_ret_t402 = cmsort_workerL_i53(env[2], env[1], env[0]);
  instr_app(&app_ret_t403, call_ret_t402, 0);
  instr_free_clo(call_ret_t402);
  fork_ret_t406 = app_ret_t403;
  instr_free_thread(env);
  return fork_ret_t406;
}

tll_ptr fork_fun_t409(tll_env env) {
  tll_ptr app_ret_t408; tll_ptr call_ret_t407; tll_ptr fork_ret_t411;
  call_ret_t407 = cmsort_workerL_i53(env[2], env[1], env[0]);
  instr_app(&app_ret_t408, call_ret_t407, 0);
  instr_free_clo(call_ret_t407);
  fork_ret_t411 = app_ret_t408;
  instr_free_thread(env);
  return fork_ret_t411;
}

tll_ptr lam_fun_t423(tll_ptr __v82552, tll_env env) {
  tll_ptr UniqL_t420; tll_ptr __v82574; tll_ptr __v82577; tll_ptr __v82585;
  tll_ptr __v82586; tll_ptr c_v82584; tll_ptr call_ret_t419;
  tll_ptr close_tmp_t421; tll_ptr close_tmp_t422; tll_ptr fork_ch_t405;
  tll_ptr fork_ch_t410; tll_ptr msg1_v82575; tll_ptr msg2_v82578;
  tll_ptr pf1_v82581; tll_ptr pf2_v82583; tll_ptr r1_v82570;
  tll_ptr r1_v82576; tll_ptr r2_v82572; tll_ptr r2_v82579;
  tll_ptr recv_msg_t412; tll_ptr recv_msg_t414; tll_ptr send_ch_t418;
  tll_ptr switch_ret_t413; tll_ptr switch_ret_t415; tll_ptr switch_ret_t416;
  tll_ptr switch_ret_t417; tll_ptr xs1_v82580; tll_ptr xs2_v82582;
  instr_fork(&fork_ch_t405, &fork_fun_t404, 2, env[1], env[3]);
  r1_v82570 = fork_ch_t405;
  instr_fork(&fork_ch_t410, &fork_fun_t409, 2, env[0], env[3]);
  r2_v82572 = fork_ch_t410;
  instr_recv(&recv_msg_t412, r1_v82570);
  __v82574 = recv_msg_t412;
  switch(((tll_node)__v82574)->tag) {
    case 0:
      msg1_v82575 = ((tll_node)__v82574)->data[0];
      r1_v82576 = ((tll_node)__v82574)->data[1];
      instr_free_struct(__v82574);
      instr_recv(&recv_msg_t414, r2_v82572);
      __v82577 = recv_msg_t414;
      switch(((tll_node)__v82577)->tag) {
        case 0:
          msg2_v82578 = ((tll_node)__v82577)->data[0];
          r2_v82579 = ((tll_node)__v82577)->data[1];
          instr_free_struct(__v82577);
          switch(((tll_node)msg1_v82575)->tag) {
            case 15:
              xs1_v82580 = ((tll_node)msg1_v82575)->data[0];
              pf1_v82581 = ((tll_node)msg1_v82575)->data[1];
              instr_free_struct(msg1_v82575);
              switch(((tll_node)msg2_v82578)->tag) {
                case 15:
                  xs2_v82582 = ((tll_node)msg2_v82578)->data[0];
                  pf2_v82583 = ((tll_node)msg2_v82578)->data[1];
                  instr_free_struct(msg2_v82578);
                  call_ret_t419 = mergeL_i47(xs1_v82580, xs2_v82582);
                  instr_struct(&UniqL_t420, 15, 2, call_ret_t419, 0);
                  instr_send(&send_ch_t418, env[2], UniqL_t420);
                  c_v82584 = send_ch_t418;
                  instr_close(&close_tmp_t421, r1_v82576);
                  __v82585 = close_tmp_t421;
                  instr_close(&close_tmp_t422, r2_v82579);
                  __v82586 = close_tmp_t422;
                  switch_ret_t417 = 0;
                  break;
              }
              switch_ret_t416 = switch_ret_t417;
              break;
          }
          switch_ret_t415 = switch_ret_t416;
          break;
      }
      switch_ret_t413 = switch_ret_t415;
      break;
  }
  return switch_ret_t413;
}

tll_ptr lam_fun_t425(tll_ptr c_v82520, tll_env env) {
  tll_ptr call_ret_t398; tll_ptr consUL_t399; tll_ptr consUL_t400;
  tll_ptr lam_clo_t397; tll_ptr lam_clo_t424; tll_ptr switch_ret_t391;
  tll_ptr switch_ret_t401; tll_ptr xs0_v82550; tll_ptr ys0_v82551;
  tll_ptr z1_v82548; tll_ptr zs1_v82549;
  switch(((tll_node)env[0])->tag) {
    case 11:
      instr_free_struct(env[0]);
      instr_clo(&lam_clo_t397, &lam_fun_t396, 2, c_v82520, env[1]);
      switch_ret_t391 = lam_clo_t397;
      break;
    case 12:
      z1_v82548 = ((tll_node)env[0])->data[0];
      zs1_v82549 = ((tll_node)env[0])->data[1];
      instr_free_struct(env[0]);
      instr_struct(&consUL_t399, 12, 2, z1_v82548, zs1_v82549);
      instr_struct(&consUL_t400, 12, 2, env[1], consUL_t399);
      call_ret_t398 = splitL_i45(consUL_t400);
      switch(((tll_node)call_ret_t398)->tag) {
        case 0:
          xs0_v82550 = ((tll_node)call_ret_t398)->data[0];
          ys0_v82551 = ((tll_node)call_ret_t398)->data[1];
          instr_free_struct(call_ret_t398);
          instr_clo(&lam_clo_t424, &lam_fun_t423, 4,
                    ys0_v82551, xs0_v82550, c_v82520, env[2]);
          switch_ret_t401 = lam_clo_t424;
          break;
      }
      switch_ret_t391 = switch_ret_t401;
      break;
  }
  return switch_ret_t391;
}

tll_ptr lam_fun_t431(tll_ptr __v82587, tll_env env) {
  tll_ptr UniqL_t430; tll_ptr c_v82589; tll_ptr call_ret_t429;
  tll_ptr send_ch_t428;
  call_ret_t429 = msortL_i49(env[1]);
  instr_struct(&UniqL_t430, 15, 2, call_ret_t429, 0);
  instr_send(&send_ch_t428, env[0], UniqL_t430);
  c_v82589 = send_ch_t428;
  return 0;
}

tll_ptr cmsort_workerL_i53(tll_ptr n_v82510, tll_ptr zs_v82511, tll_ptr c_v82512) {
  tll_ptr __v82513; tll_ptr add_ret_t384; tll_ptr app_ret_t427;
  tll_ptr ifte_ret_t433; tll_ptr lam_clo_t390; tll_ptr lam_clo_t426;
  tll_ptr lam_clo_t432; tll_ptr n0_v82514; tll_ptr switch_ret_t385;
  tll_ptr z0_v82518; tll_ptr zs0_v82519;
  __v82513 = n_v82510;
  if (__v82513) {
    add_ret_t384 = __v82513 - 1;
    n0_v82514 = add_ret_t384;
    switch(((tll_node)zs_v82511)->tag) {
      case 11:
        instr_free_struct(zs_v82511);
        instr_clo(&lam_clo_t390, &lam_fun_t389, 1, c_v82512);
        switch_ret_t385 = lam_clo_t390;
        break;
      case 12:
        z0_v82518 = ((tll_node)zs_v82511)->data[0];
        zs0_v82519 = ((tll_node)zs_v82511)->data[1];
        instr_free_struct(zs_v82511);
        instr_clo(&lam_clo_t426, &lam_fun_t425, 3,
                  zs0_v82519, z0_v82518, n0_v82514);
        instr_app(&app_ret_t427, lam_clo_t426, c_v82512);
        instr_free_clo(lam_clo_t426);
        switch_ret_t385 = app_ret_t427;
        break;
    }
    ifte_ret_t433 = switch_ret_t385;
  }
  else {
    instr_clo(&lam_clo_t432, &lam_fun_t431, 2, c_v82512, zs_v82511);
    ifte_ret_t433 = lam_clo_t432;
  }
  return ifte_ret_t433;
}

tll_ptr lam_fun_t435(tll_ptr c_v82595, tll_env env) {
  tll_ptr call_ret_t434;
  call_ret_t434 = cmsort_workerL_i53(env[1], env[0], c_v82595);
  return call_ret_t434;
}

tll_ptr lam_fun_t437(tll_ptr zs_v82593, tll_env env) {
  tll_ptr lam_clo_t436;
  instr_clo(&lam_clo_t436, &lam_fun_t435, 2, zs_v82593, env[0]);
  return lam_clo_t436;
}

tll_ptr lam_fun_t439(tll_ptr n_v82590, tll_env env) {
  tll_ptr lam_clo_t438;
  instr_clo(&lam_clo_t438, &lam_fun_t437, 1, n_v82590);
  return lam_clo_t438;
}

tll_ptr fork_fun_t443(tll_env env) {
  tll_ptr app_ret_t442; tll_ptr call_ret_t441; tll_ptr fork_ret_t445;
  call_ret_t441 = cmsort_workerU_i54((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t442, call_ret_t441, 0);
  instr_free_clo(call_ret_t441);
  fork_ret_t445 = app_ret_t442;
  instr_free_thread(env);
  return fork_ret_t445;
}

tll_ptr lam_fun_t449(tll_ptr __v82597, tll_env env) {
  tll_ptr __v82606; tll_ptr __v82609; tll_ptr c_v82604; tll_ptr c_v82608;
  tll_ptr close_tmp_t448; tll_ptr fork_ch_t444; tll_ptr msg_v82607;
  tll_ptr recv_msg_t446; tll_ptr switch_ret_t447;
  instr_fork(&fork_ch_t444, &fork_fun_t443, 1, env[0]);
  c_v82604 = fork_ch_t444;
  instr_recv(&recv_msg_t446, c_v82604);
  __v82606 = recv_msg_t446;
  switch(((tll_node)__v82606)->tag) {
    case 0:
      msg_v82607 = ((tll_node)__v82606)->data[0];
      c_v82608 = ((tll_node)__v82606)->data[1];
      instr_free_struct(__v82606);
      instr_close(&close_tmp_t448, c_v82608);
      __v82609 = close_tmp_t448;
      switch_ret_t447 = msg_v82607;
      break;
  }
  return switch_ret_t447;
}

tll_ptr cmsortU_i56(tll_ptr zs_v82596) {
  tll_ptr lam_clo_t450;
  instr_clo(&lam_clo_t450, &lam_fun_t449, 1, zs_v82596);
  return lam_clo_t450;
}

tll_ptr lam_fun_t452(tll_ptr zs_v82610, tll_env env) {
  tll_ptr call_ret_t451;
  call_ret_t451 = cmsortU_i56(zs_v82610);
  return call_ret_t451;
}

tll_ptr fork_fun_t456(tll_env env) {
  tll_ptr app_ret_t455; tll_ptr call_ret_t454; tll_ptr fork_ret_t458;
  call_ret_t454 = cmsort_workerL_i53((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t455, call_ret_t454, 0);
  instr_free_clo(call_ret_t454);
  fork_ret_t458 = app_ret_t455;
  instr_free_thread(env);
  return fork_ret_t458;
}

tll_ptr lam_fun_t462(tll_ptr __v82612, tll_env env) {
  tll_ptr __v82621; tll_ptr __v82624; tll_ptr c_v82619; tll_ptr c_v82623;
  tll_ptr close_tmp_t461; tll_ptr fork_ch_t457; tll_ptr msg_v82622;
  tll_ptr recv_msg_t459; tll_ptr switch_ret_t460;
  instr_fork(&fork_ch_t457, &fork_fun_t456, 1, env[0]);
  c_v82619 = fork_ch_t457;
  instr_recv(&recv_msg_t459, c_v82619);
  __v82621 = recv_msg_t459;
  switch(((tll_node)__v82621)->tag) {
    case 0:
      msg_v82622 = ((tll_node)__v82621)->data[0];
      c_v82623 = ((tll_node)__v82621)->data[1];
      instr_free_struct(__v82621);
      instr_close(&close_tmp_t461, c_v82623);
      __v82624 = close_tmp_t461;
      switch_ret_t460 = msg_v82622;
      break;
  }
  return switch_ret_t460;
}

tll_ptr cmsortL_i55(tll_ptr zs_v82611) {
  tll_ptr lam_clo_t463;
  instr_clo(&lam_clo_t463, &lam_fun_t462, 1, zs_v82611);
  return lam_clo_t463;
}

tll_ptr lam_fun_t465(tll_ptr zs_v82625, tll_env env) {
  tll_ptr call_ret_t464;
  call_ret_t464 = cmsortL_i55(zs_v82625);
  return call_ret_t464;
}

tll_ptr mkListU_i58(tll_ptr n_v82626) {
  tll_ptr __v82627; tll_ptr add_ret_t468; tll_ptr call_ret_t467;
  tll_ptr consUU_t469; tll_ptr ifte_ret_t471; tll_ptr nilUU_t470;
  __v82627 = n_v82626;
  if (__v82627) {
    add_ret_t468 = __v82627 - 1;
    call_ret_t467 = mkListU_i58(add_ret_t468);
    instr_struct(&consUU_t469, 14, 2, n_v82626, call_ret_t467);
    ifte_ret_t471 = consUU_t469;
  }
  else {
    instr_struct(&nilUU_t470, 13, 0);
    ifte_ret_t471 = nilUU_t470;
  }
  return ifte_ret_t471;
}

tll_ptr lam_fun_t473(tll_ptr n_v82628, tll_env env) {
  tll_ptr call_ret_t472;
  call_ret_t472 = mkListU_i58(n_v82628);
  return call_ret_t472;
}

tll_ptr mkListL_i57(tll_ptr n_v82629) {
  tll_ptr __v82630; tll_ptr add_ret_t476; tll_ptr call_ret_t475;
  tll_ptr consUL_t477; tll_ptr ifte_ret_t479; tll_ptr nilUL_t478;
  __v82630 = n_v82629;
  if (__v82630) {
    add_ret_t476 = __v82630 - 1;
    call_ret_t475 = mkListL_i57(add_ret_t476);
    instr_struct(&consUL_t477, 12, 2, n_v82629, call_ret_t475);
    ifte_ret_t479 = consUL_t477;
  }
  else {
    instr_struct(&nilUL_t478, 11, 0);
    ifte_ret_t479 = nilUL_t478;
  }
  return ifte_ret_t479;
}

tll_ptr lam_fun_t481(tll_ptr n_v82631, tll_env env) {
  tll_ptr call_ret_t480;
  call_ret_t480 = mkListL_i57(n_v82631);
  return call_ret_t480;
}

tll_ptr free_i35(tll_ptr A_v82632, tll_ptr ls_v82633) {
  tll_ptr __v82634; tll_ptr call_ret_t484; tll_ptr ls_v82635;
  tll_ptr switch_ret_t483;
  switch(((tll_node)ls_v82633)->tag) {
    case 11:
      instr_free_struct(ls_v82633);
      switch_ret_t483 = 0;
      break;
    case 12:
      __v82634 = ((tll_node)ls_v82633)->data[0];
      ls_v82635 = ((tll_node)ls_v82633)->data[1];
      instr_free_struct(ls_v82633);
      call_ret_t484 = free_i35(0, ls_v82635);
      switch_ret_t483 = call_ret_t484;
      break;
  }
  return switch_ret_t483;
}

tll_ptr lam_fun_t486(tll_ptr ls_v82638, tll_env env) {
  tll_ptr call_ret_t485;
  call_ret_t485 = free_i35(env[0], ls_v82638);
  return call_ret_t485;
}

tll_ptr lam_fun_t488(tll_ptr A_v82636, tll_env env) {
  tll_ptr lam_clo_t487;
  instr_clo(&lam_clo_t487, &lam_fun_t486, 1, A_v82636);
  return lam_clo_t487;
}

int main() {
  instr_init();
  tll_ptr __v82641; tll_ptr app_ret_t492; tll_ptr call_ret_t490;
  tll_ptr call_ret_t491; tll_ptr lam_clo_t101; tll_ptr lam_clo_t111;
  tll_ptr lam_clo_t119; tll_ptr lam_clo_t12; tll_ptr lam_clo_t127;
  tll_ptr lam_clo_t133; tll_ptr lam_clo_t146; tll_ptr lam_clo_t159;
  tll_ptr lam_clo_t16; tll_ptr lam_clo_t172; tll_ptr lam_clo_t182;
  tll_ptr lam_clo_t192; tll_ptr lam_clo_t202; tll_ptr lam_clo_t212;
  tll_ptr lam_clo_t221; tll_ptr lam_clo_t230; tll_ptr lam_clo_t247;
  tll_ptr lam_clo_t26; tll_ptr lam_clo_t264; tll_ptr lam_clo_t280;
  tll_ptr lam_clo_t296; tll_ptr lam_clo_t311; tll_ptr lam_clo_t326;
  tll_ptr lam_clo_t37; tll_ptr lam_clo_t383; tll_ptr lam_clo_t440;
  tll_ptr lam_clo_t453; tll_ptr lam_clo_t466; tll_ptr lam_clo_t474;
  tll_ptr lam_clo_t48; tll_ptr lam_clo_t482; tll_ptr lam_clo_t489;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t6; tll_ptr lam_clo_t69;
  tll_ptr lam_clo_t74; tll_ptr lam_clo_t83; tll_ptr lam_clo_t92;
  tll_ptr msg_v82639; tll_ptr sorted_v82640; tll_ptr switch_ret_t493;
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
  instr_clo(&lam_clo_t383, &lam_fun_t382, 0);
  cmsort_workerUclo_i90 = lam_clo_t383;
  instr_clo(&lam_clo_t440, &lam_fun_t439, 0);
  cmsort_workerLclo_i91 = lam_clo_t440;
  instr_clo(&lam_clo_t453, &lam_fun_t452, 0);
  cmsortUclo_i92 = lam_clo_t453;
  instr_clo(&lam_clo_t466, &lam_fun_t465, 0);
  cmsortLclo_i93 = lam_clo_t466;
  instr_clo(&lam_clo_t474, &lam_fun_t473, 0);
  mkListUclo_i94 = lam_clo_t474;
  instr_clo(&lam_clo_t482, &lam_fun_t481, 0);
  mkListLclo_i95 = lam_clo_t482;
  instr_clo(&lam_clo_t489, &lam_fun_t488, 0);
  freeclo_i96 = lam_clo_t489;
  call_ret_t491 = mkListL_i57((tll_ptr)2000000);
  call_ret_t490 = cmsortL_i55(call_ret_t491);
  instr_app(&app_ret_t492, call_ret_t490, 0);
  instr_free_clo(call_ret_t490);
  msg_v82639 = app_ret_t492;
  switch(((tll_node)msg_v82639)->tag) {
    case 15:
      sorted_v82640 = ((tll_node)msg_v82639)->data[0];
      __v82641 = ((tll_node)msg_v82639)->data[1];
      instr_free_struct(msg_v82639);
      switch_ret_t493 = 0;
      break;
  }
  return 0;
}

