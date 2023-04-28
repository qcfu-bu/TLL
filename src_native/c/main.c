#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v32262, tll_ptr b2_v32263);
tll_ptr orb_i2(tll_ptr b1_v32267, tll_ptr b2_v32268);
tll_ptr notb_i3(tll_ptr b_v32272);
tll_ptr lten_i4(tll_ptr x_v32274, tll_ptr y_v32275);
tll_ptr gten_i5(tll_ptr x_v32279, tll_ptr y_v32280);
tll_ptr ltn_i6(tll_ptr x_v32284, tll_ptr y_v32285);
tll_ptr gtn_i7(tll_ptr x_v32289, tll_ptr y_v32290);
tll_ptr eqn_i8(tll_ptr x_v32294, tll_ptr y_v32295);
tll_ptr pred_i9(tll_ptr x_v32299);
tll_ptr addn_i10(tll_ptr x_v32301, tll_ptr y_v32302);
tll_ptr subn_i11(tll_ptr x_v32306, tll_ptr y_v32307);
tll_ptr muln_i12(tll_ptr x_v32311, tll_ptr y_v32312);
tll_ptr divn_i13(tll_ptr x_v32316, tll_ptr y_v32317);
tll_ptr modn_i14(tll_ptr x_v32321, tll_ptr y_v32322);
tll_ptr cats_i15(tll_ptr s1_v32326, tll_ptr s2_v32327);
tll_ptr strlen_i16(tll_ptr s_v32333);
tll_ptr lenUU_i44(tll_ptr A_v32337, tll_ptr xs_v32338);
tll_ptr lenUL_i43(tll_ptr A_v32346, tll_ptr xs_v32347);
tll_ptr lenLL_i41(tll_ptr A_v32355, tll_ptr xs_v32356);
tll_ptr appendUU_i48(tll_ptr A_v32364, tll_ptr xs_v32365, tll_ptr ys_v32366);
tll_ptr appendUL_i47(tll_ptr A_v32375, tll_ptr xs_v32376, tll_ptr ys_v32377);
tll_ptr appendLL_i45(tll_ptr A_v32386, tll_ptr xs_v32387, tll_ptr ys_v32388);
tll_ptr readline_i25(tll_ptr __v32397);
tll_ptr print_i26(tll_ptr s_v32412);
tll_ptr prerr_i27(tll_ptr s_v32423);
tll_ptr get_at_i29(tll_ptr A_v32434, tll_ptr n_v32435, tll_ptr xs_v32436, tll_ptr a_v32437);
tll_ptr string_of_digit_i30(tll_ptr n_v32452);
tll_ptr string_of_nat_i31(tll_ptr n_v32454);
tll_ptr powm_i33(tll_ptr a_v32458, tll_ptr b_v32459, tll_ptr m_v32460);
tll_ptr client_i38(tll_ptr ch_v32467);
tll_ptr server_i39(tll_ptr ch_v32534);

tll_ptr addnclo_i58;
tll_ptr andbclo_i49;
tll_ptr appendLLclo_i70;
tll_ptr appendULclo_i69;
tll_ptr appendUUclo_i68;
tll_ptr catsclo_i63;
tll_ptr clientclo_i78;
tll_ptr digits_i28;
tll_ptr divnclo_i61;
tll_ptr eqnclo_i56;
tll_ptr get_atclo_i74;
tll_ptr gtenclo_i53;
tll_ptr gtnclo_i55;
tll_ptr lenLLclo_i67;
tll_ptr lenULclo_i66;
tll_ptr lenUUclo_i65;
tll_ptr ltenclo_i52;
tll_ptr ltnclo_i54;
tll_ptr modnclo_i62;
tll_ptr mulnclo_i60;
tll_ptr notbclo_i51;
tll_ptr orbclo_i50;
tll_ptr powmclo_i77;
tll_ptr predclo_i57;
tll_ptr prerrclo_i73;
tll_ptr printclo_i72;
tll_ptr readlineclo_i71;
tll_ptr serverclo_i79;
tll_ptr string_of_digitclo_i75;
tll_ptr string_of_natclo_i76;
tll_ptr strlenclo_i64;
tll_ptr subnclo_i59;

tll_ptr andb_i1(tll_ptr b1_v32262, tll_ptr b2_v32263) {
  tll_ptr ifte_ret_t1;
  if (b1_v32262) {
    ifte_ret_t1 = b2_v32263;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v32266, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v32266);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v32264, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v32264);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v32267, tll_ptr b2_v32268) {
  tll_ptr ifte_ret_t7;
  if (b1_v32267) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v32268;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v32271, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v32271);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v32269, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v32269);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v32272) {
  tll_ptr ifte_ret_t13;
  if (b_v32272) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v32273, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v32273);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v32274, tll_ptr y_v32275) {
  tll_ptr add_ret_t18; tll_ptr add_ret_t19; tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  if (x_v32274) {
    if (y_v32275) {
      add_ret_t18 = x_v32274 - 1;
      add_ret_t19 = y_v32275 - 1;
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

tll_ptr lam_fun_t23(tll_ptr y_v32278, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v32278);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v32276, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v32276);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v32279, tll_ptr y_v32280) {
  tll_ptr add_ret_t28; tll_ptr add_ret_t29; tll_ptr call_ret_t27;
  tll_ptr ifte_ret_t30; tll_ptr ifte_ret_t31; tll_ptr ifte_ret_t32;
  if (x_v32279) {
    if (y_v32280) {
      add_ret_t28 = x_v32279 - 1;
      add_ret_t29 = y_v32280 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v32280) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v32283, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v32283);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v32281, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v32281);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v32284, tll_ptr y_v32285) {
  tll_ptr add_ret_t39; tll_ptr add_ret_t40; tll_ptr call_ret_t38;
  tll_ptr ifte_ret_t41; tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t43;
  if (x_v32284) {
    if (y_v32285) {
      add_ret_t39 = x_v32284 - 1;
      add_ret_t40 = y_v32285 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v32285) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v32288, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v32288);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v32286, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v32286);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v32289, tll_ptr y_v32290) {
  tll_ptr add_ret_t50; tll_ptr add_ret_t51; tll_ptr call_ret_t49;
  tll_ptr ifte_ret_t52; tll_ptr ifte_ret_t53;
  if (x_v32289) {
    if (y_v32290) {
      add_ret_t50 = x_v32289 - 1;
      add_ret_t51 = y_v32290 - 1;
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

tll_ptr lam_fun_t55(tll_ptr y_v32293, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v32293);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v32291, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v32291);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v32294, tll_ptr y_v32295) {
  tll_ptr add_ret_t60; tll_ptr add_ret_t61; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t62; tll_ptr ifte_ret_t63; tll_ptr ifte_ret_t64;
  if (x_v32294) {
    if (y_v32295) {
      add_ret_t60 = x_v32294 - 1;
      add_ret_t61 = y_v32295 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v32295) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v32298, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v32298);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v32296, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v32296);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v32299) {
  tll_ptr add_ret_t70; tll_ptr ifte_ret_t71;
  if (x_v32299) {
    add_ret_t70 = x_v32299 - 1;
    ifte_ret_t71 = add_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v32300, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v32300);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v32301, tll_ptr y_v32302) {
  tll_ptr add_ret_t76; tll_ptr add_ret_t77; tll_ptr call_ret_t75;
  tll_ptr ifte_ret_t78;
  if (x_v32301) {
    add_ret_t76 = x_v32301 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v32302);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v32302;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v32305, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v32305);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v32303, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v32303);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v32306, tll_ptr y_v32307) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v32307) {
    call_ret_t85 = pred_i9(x_v32306);
    add_ret_t86 = y_v32307 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v32306;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v32310, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v32310);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v32308, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v32308);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v32311, tll_ptr y_v32312) {
  tll_ptr add_ret_t95; tll_ptr call_ret_t93; tll_ptr call_ret_t94;
  tll_ptr ifte_ret_t96;
  if (x_v32311) {
    add_ret_t95 = x_v32311 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v32312);
    call_ret_t93 = addn_i10(y_v32312, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v32315, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v32315);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v32313, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v32313);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v32316, tll_ptr y_v32317) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v32316, y_v32317);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v32316, y_v32317);
    call_ret_t103 = divn_i13(call_ret_t104, y_v32317);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v32320, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v32320);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v32318, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v32318);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v32321, tll_ptr y_v32322) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v32321, y_v32322);
  call_ret_t113 = muln_i12(call_ret_t114, y_v32322);
  call_ret_t112 = subn_i11(x_v32321, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v32325, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v32325);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v32323, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v32323);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v32326, tll_ptr s2_v32327) {
  tll_ptr String_t122; tll_ptr c_v32328; tll_ptr call_ret_t121;
  tll_ptr s1_v32329; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v32326)->tag) {
    case 2:
      switch_ret_t120 = s2_v32327;
      break;
    case 3:
      c_v32328 = ((tll_node)s1_v32326)->data[0];
      s1_v32329 = ((tll_node)s1_v32326)->data[1];
      call_ret_t121 = cats_i15(s1_v32329, s2_v32327);
      instr_struct(&String_t122, 3, 2, c_v32328, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v32332, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v32332);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v32330, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v32330);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v32333) {
  tll_ptr __v32334; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v32335; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v32333)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v32334 = ((tll_node)s_v32333)->data[0];
      s_v32335 = ((tll_node)s_v32333)->data[1];
      call_ret_t129 = strlen_i16(s_v32335);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v32336, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v32336);
  return call_ret_t131;
}

tll_ptr lenUU_i44(tll_ptr A_v32337, tll_ptr xs_v32338) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v32341; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v32339; tll_ptr xs_v32340; tll_ptr xs_v32342;
  switch(((tll_node)xs_v32338)->tag) {
    case 12:
      instr_struct(&nilUU_t135, 12, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 13:
      x_v32339 = ((tll_node)xs_v32338)->data[0];
      xs_v32340 = ((tll_node)xs_v32338)->data[1];
      call_ret_t137 = lenUU_i44(0, xs_v32340);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v32341 = ((tll_node)call_ret_t137)->data[0];
          xs_v32342 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v32341 + 1;
          instr_struct(&consUU_t140, 13, 2, x_v32339, xs_v32342);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v32345, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i44(env[0], xs_v32345);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v32343, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v32343);
  return lam_clo_t144;
}

tll_ptr lenUL_i43(tll_ptr A_v32346, tll_ptr xs_v32347) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v32350; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v32348; tll_ptr xs_v32349; tll_ptr xs_v32351;
  switch(((tll_node)xs_v32347)->tag) {
    case 10:
      instr_free_struct(xs_v32347);
      instr_struct(&nilUL_t148, 10, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 11:
      x_v32348 = ((tll_node)xs_v32347)->data[0];
      xs_v32349 = ((tll_node)xs_v32347)->data[1];
      instr_free_struct(xs_v32347);
      call_ret_t150 = lenUL_i43(0, xs_v32349);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v32350 = ((tll_node)call_ret_t150)->data[0];
          xs_v32351 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v32350 + 1;
          instr_struct(&consUL_t153, 11, 2, x_v32348, xs_v32351);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v32354, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i43(env[0], xs_v32354);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v32352, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v32352);
  return lam_clo_t157;
}

tll_ptr lenLL_i41(tll_ptr A_v32355, tll_ptr xs_v32356) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v32359; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v32357; tll_ptr xs_v32358; tll_ptr xs_v32360;
  switch(((tll_node)xs_v32356)->tag) {
    case 6:
      instr_free_struct(xs_v32356);
      instr_struct(&nilLL_t161, 6, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 7:
      x_v32357 = ((tll_node)xs_v32356)->data[0];
      xs_v32358 = ((tll_node)xs_v32356)->data[1];
      instr_free_struct(xs_v32356);
      call_ret_t163 = lenLL_i41(0, xs_v32358);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v32359 = ((tll_node)call_ret_t163)->data[0];
          xs_v32360 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v32359 + 1;
          instr_struct(&consLL_t166, 7, 2, x_v32357, xs_v32360);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v32363, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i41(env[0], xs_v32363);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v32361, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v32361);
  return lam_clo_t170;
}

tll_ptr appendUU_i48(tll_ptr A_v32364, tll_ptr xs_v32365, tll_ptr ys_v32366) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v32367; tll_ptr xs_v32368;
  switch(((tll_node)xs_v32365)->tag) {
    case 12:
      switch_ret_t173 = ys_v32366;
      break;
    case 13:
      x_v32367 = ((tll_node)xs_v32365)->data[0];
      xs_v32368 = ((tll_node)xs_v32365)->data[1];
      call_ret_t174 = appendUU_i48(0, xs_v32368, ys_v32366);
      instr_struct(&consUU_t175, 13, 2, x_v32367, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v32374, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i48(env[1], env[0], ys_v32374);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v32372, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v32372, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v32369, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v32369);
  return lam_clo_t180;
}

tll_ptr appendUL_i47(tll_ptr A_v32375, tll_ptr xs_v32376, tll_ptr ys_v32377) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v32378; tll_ptr xs_v32379;
  switch(((tll_node)xs_v32376)->tag) {
    case 10:
      instr_free_struct(xs_v32376);
      switch_ret_t183 = ys_v32377;
      break;
    case 11:
      x_v32378 = ((tll_node)xs_v32376)->data[0];
      xs_v32379 = ((tll_node)xs_v32376)->data[1];
      instr_free_struct(xs_v32376);
      call_ret_t184 = appendUL_i47(0, xs_v32379, ys_v32377);
      instr_struct(&consUL_t185, 11, 2, x_v32378, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v32385, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i47(env[1], env[0], ys_v32385);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v32383, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v32383, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v32380, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v32380);
  return lam_clo_t190;
}

tll_ptr appendLL_i45(tll_ptr A_v32386, tll_ptr xs_v32387, tll_ptr ys_v32388) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v32389; tll_ptr xs_v32390;
  switch(((tll_node)xs_v32387)->tag) {
    case 6:
      instr_free_struct(xs_v32387);
      switch_ret_t193 = ys_v32388;
      break;
    case 7:
      x_v32389 = ((tll_node)xs_v32387)->data[0];
      xs_v32390 = ((tll_node)xs_v32387)->data[1];
      instr_free_struct(xs_v32387);
      call_ret_t194 = appendLL_i45(0, xs_v32390, ys_v32388);
      instr_struct(&consLL_t195, 7, 2, x_v32389, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v32396, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i45(env[1], env[0], ys_v32396);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v32394, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v32394, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v32391, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v32391);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v32398, tll_env env) {
  tll_ptr __v32407; tll_ptr ch_v32405; tll_ptr ch_v32406; tll_ptr ch_v32409;
  tll_ptr ch_v32410; tll_ptr prim_ch_t203; tll_ptr recv_msg_t205;
  tll_ptr s_v32408; tll_ptr send_ch_t204; tll_ptr send_ch_t207;
  tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v32405 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v32405, (tll_ptr)1);
  ch_v32406 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v32406);
  __v32407 = recv_msg_t205;
  switch(((tll_node)__v32407)->tag) {
    case 0:
      s_v32408 = ((tll_node)__v32407)->data[0];
      ch_v32409 = ((tll_node)__v32407)->data[1];
      instr_free_struct(__v32407);
      instr_send(&send_ch_t207, ch_v32409, (tll_ptr)0);
      ch_v32410 = send_ch_t207;
      switch_ret_t206 = s_v32408;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v32397) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v32411, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v32411);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v32413, tll_env env) {
  tll_ptr ch_v32418; tll_ptr ch_v32419; tll_ptr ch_v32420; tll_ptr ch_v32421;
  tll_ptr prim_ch_t213; tll_ptr send_ch_t214; tll_ptr send_ch_t215;
  tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v32418 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v32418, (tll_ptr)1);
  ch_v32419 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v32419, env[0]);
  ch_v32420 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v32420, (tll_ptr)0);
  ch_v32421 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v32412) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v32412);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v32422, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v32422);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v32424, tll_env env) {
  tll_ptr ch_v32429; tll_ptr ch_v32430; tll_ptr ch_v32431; tll_ptr ch_v32432;
  tll_ptr prim_ch_t222; tll_ptr send_ch_t223; tll_ptr send_ch_t224;
  tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v32429 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v32429, (tll_ptr)1);
  ch_v32430 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v32430, env[0]);
  ch_v32431 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v32431, (tll_ptr)0);
  ch_v32432 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v32423) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v32423);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v32433, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v32433);
  return call_ret_t228;
}

tll_ptr get_at_i29(tll_ptr A_v32434, tll_ptr n_v32435, tll_ptr xs_v32436, tll_ptr a_v32437) {
  tll_ptr __v32438; tll_ptr __v32441; tll_ptr add_ret_t274;
  tll_ptr call_ret_t273; tll_ptr ifte_ret_t276; tll_ptr switch_ret_t272;
  tll_ptr switch_ret_t275; tll_ptr x_v32440; tll_ptr xs_v32439;
  if (n_v32435) {
    switch(((tll_node)xs_v32436)->tag) {
      case 12:
        switch_ret_t272 = a_v32437;
        break;
      case 13:
        __v32438 = ((tll_node)xs_v32436)->data[0];
        xs_v32439 = ((tll_node)xs_v32436)->data[1];
        add_ret_t274 = n_v32435 - 1;
        call_ret_t273 = get_at_i29(0, add_ret_t274, xs_v32439, a_v32437);
        switch_ret_t272 = call_ret_t273;
        break;
    }
    ifte_ret_t276 = switch_ret_t272;
  }
  else {
    switch(((tll_node)xs_v32436)->tag) {
      case 12:
        switch_ret_t275 = a_v32437;
        break;
      case 13:
        x_v32440 = ((tll_node)xs_v32436)->data[0];
        __v32441 = ((tll_node)xs_v32436)->data[1];
        switch_ret_t275 = x_v32440;
        break;
    }
    ifte_ret_t276 = switch_ret_t275;
  }
  return ifte_ret_t276;
}

tll_ptr lam_fun_t278(tll_ptr a_v32451, tll_env env) {
  tll_ptr call_ret_t277;
  call_ret_t277 = get_at_i29(env[2], env[1], env[0], a_v32451);
  return call_ret_t277;
}

tll_ptr lam_fun_t280(tll_ptr xs_v32449, tll_env env) {
  tll_ptr lam_clo_t279;
  instr_clo(&lam_clo_t279, &lam_fun_t278, 3, xs_v32449, env[0], env[1]);
  return lam_clo_t279;
}

tll_ptr lam_fun_t282(tll_ptr n_v32446, tll_env env) {
  tll_ptr lam_clo_t281;
  instr_clo(&lam_clo_t281, &lam_fun_t280, 2, n_v32446, env[0]);
  return lam_clo_t281;
}

tll_ptr lam_fun_t284(tll_ptr A_v32442, tll_env env) {
  tll_ptr lam_clo_t283;
  instr_clo(&lam_clo_t283, &lam_fun_t282, 1, A_v32442);
  return lam_clo_t283;
}

tll_ptr string_of_digit_i30(tll_ptr n_v32452) {
  tll_ptr EmptyString_t287; tll_ptr call_ret_t286;
  instr_struct(&EmptyString_t287, 2, 0);
  call_ret_t286 = get_at_i29(0, n_v32452, digits_i28, EmptyString_t287);
  return call_ret_t286;
}

tll_ptr lam_fun_t289(tll_ptr n_v32453, tll_env env) {
  tll_ptr call_ret_t288;
  call_ret_t288 = string_of_digit_i30(n_v32453);
  return call_ret_t288;
}

tll_ptr string_of_nat_i31(tll_ptr n_v32454) {
  tll_ptr call_ret_t291; tll_ptr call_ret_t292; tll_ptr call_ret_t293;
  tll_ptr call_ret_t294; tll_ptr call_ret_t295; tll_ptr call_ret_t296;
  tll_ptr ifte_ret_t297; tll_ptr n_v32456; tll_ptr s_v32455;
  call_ret_t292 = modn_i14(n_v32454, (tll_ptr)10);
  call_ret_t291 = string_of_digit_i30(call_ret_t292);
  s_v32455 = call_ret_t291;
  call_ret_t293 = divn_i13(n_v32454, (tll_ptr)10);
  n_v32456 = call_ret_t293;
  call_ret_t294 = ltn_i6((tll_ptr)0, n_v32456);
  if (call_ret_t294) {
    call_ret_t296 = string_of_nat_i31(n_v32456);
    call_ret_t295 = cats_i15(call_ret_t296, s_v32455);
    ifte_ret_t297 = call_ret_t295;
  }
  else {
    ifte_ret_t297 = s_v32455;
  }
  return ifte_ret_t297;
}

tll_ptr lam_fun_t299(tll_ptr n_v32457, tll_env env) {
  tll_ptr call_ret_t298;
  call_ret_t298 = string_of_nat_i31(n_v32457);
  return call_ret_t298;
}

tll_ptr powm_i33(tll_ptr a_v32458, tll_ptr b_v32459, tll_ptr m_v32460) {
  tll_ptr add_ret_t304; tll_ptr call_ret_t301; tll_ptr call_ret_t302;
  tll_ptr call_ret_t303; tll_ptr ifte_ret_t305;
  if (b_v32459) {
    add_ret_t304 = b_v32459 - 1;
    call_ret_t303 = powm_i33(a_v32458, add_ret_t304, m_v32460);
    call_ret_t302 = muln_i12(a_v32458, call_ret_t303);
    call_ret_t301 = modn_i14(call_ret_t302, m_v32460);
    ifte_ret_t305 = call_ret_t301;
  }
  else {
    ifte_ret_t305 = (tll_ptr)1;
  }
  return ifte_ret_t305;
}

tll_ptr lam_fun_t307(tll_ptr m_v32466, tll_env env) {
  tll_ptr call_ret_t306;
  call_ret_t306 = powm_i33(env[1], env[0], m_v32466);
  return call_ret_t306;
}

tll_ptr lam_fun_t309(tll_ptr b_v32464, tll_env env) {
  tll_ptr lam_clo_t308;
  instr_clo(&lam_clo_t308, &lam_fun_t307, 2, b_v32464, env[0]);
  return lam_clo_t308;
}

tll_ptr lam_fun_t311(tll_ptr a_v32461, tll_env env) {
  tll_ptr lam_clo_t310;
  instr_clo(&lam_clo_t310, &lam_fun_t309, 1, a_v32461);
  return lam_clo_t310;
}

tll_ptr lam_fun_t344(tll_ptr __v32468, tll_env env) {
  tll_ptr P1_v32529; tll_ptr __v32505; tll_ptr __v32514;
  tll_ptr call_ret_t337; tll_ptr ch_v32502; tll_ptr ch_v32504;
  tll_ptr ch_v32507; tll_ptr ch_v32509; tll_ptr ch_v32511; tll_ptr ch_v32513;
  tll_ptr ch_v32516; tll_ptr ch_v32518; tll_ptr ch_v32520; tll_ptr ch_v32522;
  tll_ptr ch_v32524; tll_ptr ch_v32526; tll_ptr ch_v32527; tll_ptr ch_v32530;
  tll_ptr ch_v32532; tll_ptr close_tmp_t343; tll_ptr d_v32523;
  tll_ptr e_v32515; tll_ptr n_v32506; tll_ptr pair_struct_t313;
  tll_ptr pair_struct_t315; tll_ptr pair_struct_t319;
  tll_ptr pair_struct_t321; tll_ptr pair_struct_t323;
  tll_ptr pair_struct_t327; tll_ptr pair_struct_t329;
  tll_ptr pair_struct_t331; tll_ptr pair_struct_t333;
  tll_ptr pair_struct_t335; tll_ptr pair_struct_t339;
  tll_ptr pair_struct_t341; tll_ptr pf1_v32508; tll_ptr pf2_v32512;
  tll_ptr pf3_v32517; tll_ptr pf4_v32519; tll_ptr pf5_v32521;
  tll_ptr pf6_v32525; tll_ptr pf7_v32531; tll_ptr recv_msg_t317;
  tll_ptr recv_msg_t325; tll_ptr send_ch_t338; tll_ptr switch_ret_t314;
  tll_ptr switch_ret_t316; tll_ptr switch_ret_t318; tll_ptr switch_ret_t320;
  tll_ptr switch_ret_t322; tll_ptr switch_ret_t324; tll_ptr switch_ret_t326;
  tll_ptr switch_ret_t328; tll_ptr switch_ret_t330; tll_ptr switch_ret_t332;
  tll_ptr switch_ret_t334; tll_ptr switch_ret_t336; tll_ptr switch_ret_t340;
  tll_ptr switch_ret_t342; tll_ptr tot_v32510; tll_ptr x_v32501;
  tll_ptr x_v32528; tll_ptr y_v32503;
  instr_struct(&pair_struct_t313, 0, 2, 0, env[0]);
  switch(((tll_node)pair_struct_t313)->tag) {
    case 0:
      x_v32501 = ((tll_node)pair_struct_t313)->data[0];
      ch_v32502 = ((tll_node)pair_struct_t313)->data[1];
      instr_free_struct(pair_struct_t313);
      instr_struct(&pair_struct_t315, 0, 2, 0, ch_v32502);
      switch(((tll_node)pair_struct_t315)->tag) {
        case 0:
          y_v32503 = ((tll_node)pair_struct_t315)->data[0];
          ch_v32504 = ((tll_node)pair_struct_t315)->data[1];
          instr_free_struct(pair_struct_t315);
          instr_recv(&recv_msg_t317, ch_v32504);
          __v32505 = recv_msg_t317;
          switch(((tll_node)__v32505)->tag) {
            case 0:
              n_v32506 = ((tll_node)__v32505)->data[0];
              ch_v32507 = ((tll_node)__v32505)->data[1];
              instr_free_struct(__v32505);
              instr_struct(&pair_struct_t319, 0, 2, 0, ch_v32507);
              switch(((tll_node)pair_struct_t319)->tag) {
                case 0:
                  pf1_v32508 = ((tll_node)pair_struct_t319)->data[0];
                  ch_v32509 = ((tll_node)pair_struct_t319)->data[1];
                  instr_free_struct(pair_struct_t319);
                  instr_struct(&pair_struct_t321, 0, 2, 0, ch_v32509);
                  switch(((tll_node)pair_struct_t321)->tag) {
                    case 0:
                      tot_v32510 = ((tll_node)pair_struct_t321)->data[0];
                      ch_v32511 = ((tll_node)pair_struct_t321)->data[1];
                      instr_free_struct(pair_struct_t321);
                      instr_struct(&pair_struct_t323, 0, 2, 0, ch_v32511);
                      switch(((tll_node)pair_struct_t323)->tag) {
                        case 0:
                          pf2_v32512 = ((tll_node)pair_struct_t323)->data[0];
                          ch_v32513 = ((tll_node)pair_struct_t323)->data[1];
                          instr_free_struct(pair_struct_t323);
                          instr_recv(&recv_msg_t325, ch_v32513);
                          __v32514 = recv_msg_t325;
                          switch(((tll_node)__v32514)->tag) {
                            case 0:
                              e_v32515 = ((tll_node)__v32514)->data[0];
                              ch_v32516 = ((tll_node)__v32514)->data[1];
                              instr_free_struct(__v32514);
                              instr_struct(&pair_struct_t327, 0, 2,
                                           0, ch_v32516);
                              switch(((tll_node)pair_struct_t327)->tag) {
                                case 0:
                                  pf3_v32517 = ((tll_node)pair_struct_t327)->data[0];
                                  ch_v32518 = ((tll_node)pair_struct_t327)->data[1];
                                  instr_free_struct(pair_struct_t327);
                                  instr_struct(&pair_struct_t329, 0, 2,
                                               0, ch_v32518);
                                  switch(((tll_node)pair_struct_t329)->tag) {
                                    case 0:
                                      pf4_v32519 = ((tll_node)pair_struct_t329)->data[0];
                                      ch_v32520 = ((tll_node)pair_struct_t329)->data[1];
                                      instr_free_struct(pair_struct_t329);
                                      instr_struct(&pair_struct_t331, 0, 2,
                                                   0, ch_v32520);
                                      switch(((tll_node)pair_struct_t331)->tag) {
                                        case 0:
                                          pf5_v32521 = ((tll_node)pair_struct_t331)->data[0];
                                          ch_v32522 = ((tll_node)pair_struct_t331)->data[1];
                                          instr_free_struct(pair_struct_t331);
                                          instr_struct(&pair_struct_t333, 0, 2,
                                                       0, ch_v32522);
                                          switch(((tll_node)pair_struct_t333)->tag) {
                                            case 0:
                                              d_v32523 = ((tll_node)pair_struct_t333)->data[0];
                                              ch_v32524 = ((tll_node)pair_struct_t333)->data[1];
                                              instr_free_struct(pair_struct_t333);
                                              instr_struct(&pair_struct_t335, 0, 2,
                                                           0, ch_v32524);
                                              switch(((tll_node)pair_struct_t335)->tag) {
                                                case 0:
                                                  pf6_v32525 = ((tll_node)pair_struct_t335)->data[0];
                                                  ch_v32526 = ((tll_node)pair_struct_t335)->data[1];
                                                  instr_free_struct(pair_struct_t335);
                                                  call_ret_t337 = powm_i33(
                                                  (tll_ptr)123, e_v32515,
                                                  n_v32506);
                                                  x_v32528 = call_ret_t337;
                                                  instr_send(&send_ch_t338, ch_v32526, x_v32528);
                                                  ch_v32527 = send_ch_t338;
                                                  instr_struct(&pair_struct_t339, 0, 2,
                                                               0, ch_v32527);
                                                  switch(((tll_node)pair_struct_t339)->tag) {
                                                    case 0:
                                                      P1_v32529 = ((tll_node)pair_struct_t339)->data[0];
                                                      ch_v32530 = ((tll_node)pair_struct_t339)->data[1];
                                                      instr_free_struct(pair_struct_t339);
                                                      instr_struct(&pair_struct_t341, 0, 2,
                                                                   0,
                                                                   ch_v32530);
                                                      switch(((tll_node)pair_struct_t341)->tag) {
                                                        case 0:
                                                          pf7_v32531 = ((tll_node)pair_struct_t341)->data[0];
                                                          ch_v32532 = ((tll_node)pair_struct_t341)->data[1];
                                                          instr_free_struct(pair_struct_t341);
                                                          instr_close(&close_tmp_t343, ch_v32532);
                                                          switch_ret_t342 = close_tmp_t343;
                                                          break;
                                                      }
                                                      switch_ret_t340 = switch_ret_t342;
                                                      break;
                                                  }
                                                  switch_ret_t336 = switch_ret_t340;
                                                  break;
                                              }
                                              switch_ret_t334 = switch_ret_t336;
                                              break;
                                          }
                                          switch_ret_t332 = switch_ret_t334;
                                          break;
                                      }
                                      switch_ret_t330 = switch_ret_t332;
                                      break;
                                  }
                                  switch_ret_t328 = switch_ret_t330;
                                  break;
                              }
                              switch_ret_t326 = switch_ret_t328;
                              break;
                          }
                          switch_ret_t324 = switch_ret_t326;
                          break;
                      }
                      switch_ret_t322 = switch_ret_t324;
                      break;
                  }
                  switch_ret_t320 = switch_ret_t322;
                  break;
              }
              switch_ret_t318 = switch_ret_t320;
              break;
          }
          switch_ret_t316 = switch_ret_t318;
          break;
      }
      switch_ret_t314 = switch_ret_t316;
      break;
  }
  return switch_ret_t314;
}

tll_ptr client_i38(tll_ptr ch_v32467) {
  tll_ptr lam_clo_t345;
  instr_clo(&lam_clo_t345, &lam_fun_t344, 1, ch_v32467);
  return lam_clo_t345;
}

tll_ptr lam_fun_t347(tll_ptr ch_v32533, tll_env env) {
  tll_ptr call_ret_t346;
  call_ret_t346 = client_i38(ch_v32533);
  return call_ret_t346;
}

tll_ptr lam_fun_t369(tll_ptr __v32537, tll_env env) {
  tll_ptr C_v32553; tll_ptr Char_t365; tll_ptr EmptyString_t366;
  tll_ptr P0_v32550; tll_ptr P1_v32557; tll_ptr String_t367;
  tll_ptr __v32552; tll_ptr app_ret_t368; tll_ptr call_ret_t361;
  tll_ptr call_ret_t362; tll_ptr call_ret_t363; tll_ptr call_ret_t364;
  tll_ptr ch_v32548; tll_ptr ch_v32549; tll_ptr ch_v32551; tll_ptr ch_v32554;
  tll_ptr ch_v32556; tll_ptr pair_struct_t355; tll_ptr pair_struct_t359;
  tll_ptr pf_v32555; tll_ptr recv_msg_t357; tll_ptr send_ch_t353;
  tll_ptr send_ch_t354; tll_ptr switch_ret_t356; tll_ptr switch_ret_t358;
  tll_ptr switch_ret_t360;
  instr_send(&send_ch_t353, env[1], env[0]);
  ch_v32548 = send_ch_t353;
  instr_send(&send_ch_t354, ch_v32548, (tll_ptr)5);
  ch_v32549 = send_ch_t354;
  instr_struct(&pair_struct_t355, 0, 2, 0, ch_v32549);
  switch(((tll_node)pair_struct_t355)->tag) {
    case 0:
      P0_v32550 = ((tll_node)pair_struct_t355)->data[0];
      ch_v32551 = ((tll_node)pair_struct_t355)->data[1];
      instr_free_struct(pair_struct_t355);
      instr_recv(&recv_msg_t357, ch_v32551);
      __v32552 = recv_msg_t357;
      switch(((tll_node)__v32552)->tag) {
        case 0:
          C_v32553 = ((tll_node)__v32552)->data[0];
          ch_v32554 = ((tll_node)__v32552)->data[1];
          instr_free_struct(__v32552);
          instr_struct(&pair_struct_t359, 0, 2, 0, ch_v32554);
          switch(((tll_node)pair_struct_t359)->tag) {
            case 0:
              pf_v32555 = ((tll_node)pair_struct_t359)->data[0];
              ch_v32556 = ((tll_node)pair_struct_t359)->data[1];
              instr_free_struct(pair_struct_t359);
              call_ret_t361 = powm_i33(C_v32553, (tll_ptr)65, env[0]);
              P1_v32557 = call_ret_t361;
              call_ret_t364 = string_of_nat_i31(P1_v32557);
              instr_struct(&Char_t365, 1, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t366, 2, 0);
              instr_struct(&String_t367, 3, 2, Char_t365, EmptyString_t366);
              call_ret_t363 = cats_i15(call_ret_t364, String_t367);
              call_ret_t362 = print_i26(call_ret_t363);
              instr_app(&app_ret_t368, call_ret_t362, 0);
              instr_free_clo(call_ret_t362);
              switch_ret_t360 = app_ret_t368;
              break;
          }
          switch_ret_t358 = switch_ret_t360;
          break;
      }
      switch_ret_t356 = switch_ret_t358;
      break;
  }
  return switch_ret_t356;
}

tll_ptr server_i39(tll_ptr ch_v32534) {
  tll_ptr call_ret_t349; tll_ptr call_ret_t350; tll_ptr call_ret_t351;
  tll_ptr call_ret_t352; tll_ptr lam_clo_t370; tll_ptr n_v32535;
  tll_ptr tot_v32536;
  call_ret_t349 = muln_i12((tll_ptr)7, (tll_ptr)19);
  n_v32535 = call_ret_t349;
  call_ret_t351 = subn_i11((tll_ptr)7, (tll_ptr)1);
  call_ret_t352 = subn_i11((tll_ptr)19, (tll_ptr)1);
  call_ret_t350 = muln_i12(call_ret_t351, call_ret_t352);
  tot_v32536 = call_ret_t350;
  instr_clo(&lam_clo_t370, &lam_fun_t369, 2, n_v32535, ch_v32534);
  return lam_clo_t370;
}

tll_ptr lam_fun_t372(tll_ptr ch_v32558, tll_env env) {
  tll_ptr call_ret_t371;
  call_ret_t371 = server_i39(ch_v32558);
  return call_ret_t371;
}

tll_ptr fork_fun_t376(tll_env env) {
  tll_ptr app_ret_t375; tll_ptr call_ret_t374; tll_ptr fork_ret_t378;
  call_ret_t374 = server_i39(env[0]);
  instr_app(&app_ret_t375, call_ret_t374, 0);
  instr_free_clo(call_ret_t374);
  fork_ret_t378 = app_ret_t375;
  instr_free_thread(env);
  return fork_ret_t378;
}

tll_ptr fork_fun_t383(tll_env env) {
  tll_ptr __v32566; tll_ptr app_ret_t382; tll_ptr c0_v32568;
  tll_ptr c_v32567; tll_ptr call_ret_t381; tll_ptr fork_ret_t385;
  tll_ptr recv_msg_t379; tll_ptr switch_ret_t380;
  instr_recv(&recv_msg_t379, env[0]);
  __v32566 = recv_msg_t379;
  switch(((tll_node)__v32566)->tag) {
    case 0:
      c_v32567 = ((tll_node)__v32566)->data[0];
      c0_v32568 = ((tll_node)__v32566)->data[1];
      instr_free_struct(__v32566);
      call_ret_t381 = client_i38(c_v32567);
      instr_app(&app_ret_t382, call_ret_t381, 0);
      instr_free_clo(call_ret_t381);
      switch_ret_t380 = app_ret_t382;
      break;
  }
  fork_ret_t385 = switch_ret_t380;
  instr_free_thread(env);
  return fork_ret_t385;
}

int main() {
  instr_init();
  tll_ptr Char_t231; tll_ptr Char_t234; tll_ptr Char_t237; tll_ptr Char_t240;
  tll_ptr Char_t243; tll_ptr Char_t246; tll_ptr Char_t249; tll_ptr Char_t252;
  tll_ptr Char_t255; tll_ptr Char_t258; tll_ptr EmptyString_t232;
  tll_ptr EmptyString_t235; tll_ptr EmptyString_t238;
  tll_ptr EmptyString_t241; tll_ptr EmptyString_t244;
  tll_ptr EmptyString_t247; tll_ptr EmptyString_t250;
  tll_ptr EmptyString_t253; tll_ptr EmptyString_t256;
  tll_ptr EmptyString_t259; tll_ptr String_t233; tll_ptr String_t236;
  tll_ptr String_t239; tll_ptr String_t242; tll_ptr String_t245;
  tll_ptr String_t248; tll_ptr String_t251; tll_ptr String_t254;
  tll_ptr String_t257; tll_ptr String_t260; tll_ptr __v32570;
  tll_ptr c0_v32561; tll_ptr c0_v32569; tll_ptr c_v32559;
  tll_ptr close_tmp_t387; tll_ptr consUU_t262; tll_ptr consUU_t263;
  tll_ptr consUU_t264; tll_ptr consUU_t265; tll_ptr consUU_t266;
  tll_ptr consUU_t267; tll_ptr consUU_t268; tll_ptr consUU_t269;
  tll_ptr consUU_t270; tll_ptr consUU_t271; tll_ptr fork_ch_t377;
  tll_ptr fork_ch_t384; tll_ptr lam_clo_t101; tll_ptr lam_clo_t111;
  tll_ptr lam_clo_t119; tll_ptr lam_clo_t12; tll_ptr lam_clo_t127;
  tll_ptr lam_clo_t133; tll_ptr lam_clo_t146; tll_ptr lam_clo_t159;
  tll_ptr lam_clo_t16; tll_ptr lam_clo_t172; tll_ptr lam_clo_t182;
  tll_ptr lam_clo_t192; tll_ptr lam_clo_t202; tll_ptr lam_clo_t212;
  tll_ptr lam_clo_t221; tll_ptr lam_clo_t230; tll_ptr lam_clo_t26;
  tll_ptr lam_clo_t285; tll_ptr lam_clo_t290; tll_ptr lam_clo_t300;
  tll_ptr lam_clo_t312; tll_ptr lam_clo_t348; tll_ptr lam_clo_t37;
  tll_ptr lam_clo_t373; tll_ptr lam_clo_t48; tll_ptr lam_clo_t58;
  tll_ptr lam_clo_t6; tll_ptr lam_clo_t69; tll_ptr lam_clo_t74;
  tll_ptr lam_clo_t83; tll_ptr lam_clo_t92; tll_ptr nilUU_t261;
  tll_ptr send_ch_t386; tll_ptr sleep_tmp_t388;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i49 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i50 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i51 = lam_clo_t16;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 0);
  ltenclo_i52 = lam_clo_t26;
  instr_clo(&lam_clo_t37, &lam_fun_t36, 0);
  gtenclo_i53 = lam_clo_t37;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  ltnclo_i54 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  gtnclo_i55 = lam_clo_t58;
  instr_clo(&lam_clo_t69, &lam_fun_t68, 0);
  eqnclo_i56 = lam_clo_t69;
  instr_clo(&lam_clo_t74, &lam_fun_t73, 0);
  predclo_i57 = lam_clo_t74;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i58 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i59 = lam_clo_t92;
  instr_clo(&lam_clo_t101, &lam_fun_t100, 0);
  mulnclo_i60 = lam_clo_t101;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 0);
  divnclo_i61 = lam_clo_t111;
  instr_clo(&lam_clo_t119, &lam_fun_t118, 0);
  modnclo_i62 = lam_clo_t119;
  instr_clo(&lam_clo_t127, &lam_fun_t126, 0);
  catsclo_i63 = lam_clo_t127;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 0);
  strlenclo_i64 = lam_clo_t133;
  instr_clo(&lam_clo_t146, &lam_fun_t145, 0);
  lenUUclo_i65 = lam_clo_t146;
  instr_clo(&lam_clo_t159, &lam_fun_t158, 0);
  lenULclo_i66 = lam_clo_t159;
  instr_clo(&lam_clo_t172, &lam_fun_t171, 0);
  lenLLclo_i67 = lam_clo_t172;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 0);
  appendUUclo_i68 = lam_clo_t182;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 0);
  appendULclo_i69 = lam_clo_t192;
  instr_clo(&lam_clo_t202, &lam_fun_t201, 0);
  appendLLclo_i70 = lam_clo_t202;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  readlineclo_i71 = lam_clo_t212;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 0);
  printclo_i72 = lam_clo_t221;
  instr_clo(&lam_clo_t230, &lam_fun_t229, 0);
  prerrclo_i73 = lam_clo_t230;
  instr_struct(&Char_t231, 1, 1, (tll_ptr)48);
  instr_struct(&EmptyString_t232, 2, 0);
  instr_struct(&String_t233, 3, 2, Char_t231, EmptyString_t232);
  instr_struct(&Char_t234, 1, 1, (tll_ptr)49);
  instr_struct(&EmptyString_t235, 2, 0);
  instr_struct(&String_t236, 3, 2, Char_t234, EmptyString_t235);
  instr_struct(&Char_t237, 1, 1, (tll_ptr)50);
  instr_struct(&EmptyString_t238, 2, 0);
  instr_struct(&String_t239, 3, 2, Char_t237, EmptyString_t238);
  instr_struct(&Char_t240, 1, 1, (tll_ptr)51);
  instr_struct(&EmptyString_t241, 2, 0);
  instr_struct(&String_t242, 3, 2, Char_t240, EmptyString_t241);
  instr_struct(&Char_t243, 1, 1, (tll_ptr)52);
  instr_struct(&EmptyString_t244, 2, 0);
  instr_struct(&String_t245, 3, 2, Char_t243, EmptyString_t244);
  instr_struct(&Char_t246, 1, 1, (tll_ptr)53);
  instr_struct(&EmptyString_t247, 2, 0);
  instr_struct(&String_t248, 3, 2, Char_t246, EmptyString_t247);
  instr_struct(&Char_t249, 1, 1, (tll_ptr)54);
  instr_struct(&EmptyString_t250, 2, 0);
  instr_struct(&String_t251, 3, 2, Char_t249, EmptyString_t250);
  instr_struct(&Char_t252, 1, 1, (tll_ptr)55);
  instr_struct(&EmptyString_t253, 2, 0);
  instr_struct(&String_t254, 3, 2, Char_t252, EmptyString_t253);
  instr_struct(&Char_t255, 1, 1, (tll_ptr)56);
  instr_struct(&EmptyString_t256, 2, 0);
  instr_struct(&String_t257, 3, 2, Char_t255, EmptyString_t256);
  instr_struct(&Char_t258, 1, 1, (tll_ptr)57);
  instr_struct(&EmptyString_t259, 2, 0);
  instr_struct(&String_t260, 3, 2, Char_t258, EmptyString_t259);
  instr_struct(&nilUU_t261, 12, 0);
  instr_struct(&consUU_t262, 13, 2, String_t260, nilUU_t261);
  instr_struct(&consUU_t263, 13, 2, String_t257, consUU_t262);
  instr_struct(&consUU_t264, 13, 2, String_t254, consUU_t263);
  instr_struct(&consUU_t265, 13, 2, String_t251, consUU_t264);
  instr_struct(&consUU_t266, 13, 2, String_t248, consUU_t265);
  instr_struct(&consUU_t267, 13, 2, String_t245, consUU_t266);
  instr_struct(&consUU_t268, 13, 2, String_t242, consUU_t267);
  instr_struct(&consUU_t269, 13, 2, String_t239, consUU_t268);
  instr_struct(&consUU_t270, 13, 2, String_t236, consUU_t269);
  instr_struct(&consUU_t271, 13, 2, String_t233, consUU_t270);
  digits_i28 = consUU_t271;
  instr_clo(&lam_clo_t285, &lam_fun_t284, 0);
  get_atclo_i74 = lam_clo_t285;
  instr_clo(&lam_clo_t290, &lam_fun_t289, 0);
  string_of_digitclo_i75 = lam_clo_t290;
  instr_clo(&lam_clo_t300, &lam_fun_t299, 0);
  string_of_natclo_i76 = lam_clo_t300;
  instr_clo(&lam_clo_t312, &lam_fun_t311, 0);
  powmclo_i77 = lam_clo_t312;
  instr_clo(&lam_clo_t348, &lam_fun_t347, 0);
  clientclo_i78 = lam_clo_t348;
  instr_clo(&lam_clo_t373, &lam_fun_t372, 0);
  serverclo_i79 = lam_clo_t373;
  instr_fork(&fork_ch_t377, &fork_fun_t376, 0);
  c_v32559 = fork_ch_t377;
  instr_fork(&fork_ch_t384, &fork_fun_t383, 0);
  c0_v32561 = fork_ch_t384;
  instr_send(&send_ch_t386, c0_v32561, c_v32559);
  c0_v32569 = send_ch_t386;
  instr_close(&close_tmp_t387, c0_v32569);
  __v32570 = close_tmp_t387;
  instr_sleep(&sleep_tmp_t388, (tll_ptr)1);
  return 0;
}

