#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v14057, tll_ptr b2_v14058);
tll_ptr orb_i2(tll_ptr b1_v14062, tll_ptr b2_v14063);
tll_ptr notb_i3(tll_ptr b_v14067);
tll_ptr lten_i4(tll_ptr x_v14069, tll_ptr y_v14070);
tll_ptr gten_i5(tll_ptr x_v14074, tll_ptr y_v14075);
tll_ptr ltn_i6(tll_ptr x_v14079, tll_ptr y_v14080);
tll_ptr gtn_i7(tll_ptr x_v14084, tll_ptr y_v14085);
tll_ptr eqn_i8(tll_ptr x_v14089, tll_ptr y_v14090);
tll_ptr pred_i9(tll_ptr x_v14094);
tll_ptr addn_i10(tll_ptr x_v14096, tll_ptr y_v14097);
tll_ptr subn_i11(tll_ptr x_v14101, tll_ptr y_v14102);
tll_ptr muln_i12(tll_ptr x_v14106, tll_ptr y_v14107);
tll_ptr divn_i13(tll_ptr x_v14111, tll_ptr y_v14112);
tll_ptr modn_i14(tll_ptr x_v14116, tll_ptr y_v14117);
tll_ptr cats_i15(tll_ptr s1_v14121, tll_ptr s2_v14122);
tll_ptr strlen_i16(tll_ptr s_v14128);
tll_ptr lenUU_i39(tll_ptr A_v14132, tll_ptr xs_v14133);
tll_ptr lenUL_i38(tll_ptr A_v14141, tll_ptr xs_v14142);
tll_ptr lenLL_i36(tll_ptr A_v14150, tll_ptr xs_v14151);
tll_ptr appendUU_i43(tll_ptr A_v14159, tll_ptr xs_v14160, tll_ptr ys_v14161);
tll_ptr appendUL_i42(tll_ptr A_v14170, tll_ptr xs_v14171, tll_ptr ys_v14172);
tll_ptr appendLL_i40(tll_ptr A_v14181, tll_ptr xs_v14182, tll_ptr ys_v14183);
tll_ptr readline_i25(tll_ptr __v14192);
tll_ptr print_i26(tll_ptr s_v14207);
tll_ptr prerr_i27(tll_ptr s_v14218);
tll_ptr splitU_i45(tll_ptr zs_v14229);
tll_ptr splitL_i44(tll_ptr zs_v14238);
tll_ptr mergeU_i47(tll_ptr xs_v14247, tll_ptr ys_v14248);
tll_ptr mergeL_i46(tll_ptr xs_v14256, tll_ptr ys_v14257);
tll_ptr msortU_i49(tll_ptr zs_v14265);
tll_ptr msortL_i48(tll_ptr zs_v14274);
tll_ptr cmsort_workerU_i53(tll_ptr n_v14283, tll_ptr zs_v14284, tll_ptr c_v14285);
tll_ptr cmsort_workerL_i52(tll_ptr n_v14332, tll_ptr zs_v14333, tll_ptr c_v14334);
tll_ptr cmsortU_i55(tll_ptr zs0_v14381);
tll_ptr cmsortL_i54(tll_ptr zs0_v14396);
tll_ptr mkListU_i57(tll_ptr n_v14411);
tll_ptr mkListL_i56(tll_ptr n_v14413);

tll_ptr addnclo_i67;
tll_ptr andbclo_i58;
tll_ptr appendLLclo_i79;
tll_ptr appendULclo_i78;
tll_ptr appendUUclo_i77;
tll_ptr catsclo_i72;
tll_ptr cmsortLclo_i92;
tll_ptr cmsortUclo_i91;
tll_ptr cmsort_workerLclo_i90;
tll_ptr cmsort_workerUclo_i89;
tll_ptr divnclo_i70;
tll_ptr eqnclo_i65;
tll_ptr gtenclo_i62;
tll_ptr gtnclo_i64;
tll_ptr lenLLclo_i76;
tll_ptr lenULclo_i75;
tll_ptr lenUUclo_i74;
tll_ptr ltenclo_i61;
tll_ptr ltnclo_i63;
tll_ptr mergeLclo_i86;
tll_ptr mergeUclo_i85;
tll_ptr mkListLclo_i94;
tll_ptr mkListUclo_i93;
tll_ptr modnclo_i71;
tll_ptr msortLclo_i88;
tll_ptr msortUclo_i87;
tll_ptr mulnclo_i69;
tll_ptr notbclo_i60;
tll_ptr orbclo_i59;
tll_ptr predclo_i66;
tll_ptr prerrclo_i82;
tll_ptr printclo_i81;
tll_ptr readlineclo_i80;
tll_ptr splitLclo_i84;
tll_ptr splitUclo_i83;
tll_ptr strlenclo_i73;
tll_ptr subnclo_i68;

tll_ptr andb_i1(tll_ptr b1_v14057, tll_ptr b2_v14058) {
  tll_ptr ifte_ret_t1;
  if (b1_v14057) {
    ifte_ret_t1 = b2_v14058;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v14061, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v14061);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v14059, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v14059);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v14062, tll_ptr b2_v14063) {
  tll_ptr ifte_ret_t7;
  if (b1_v14062) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v14063;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v14066, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v14066);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v14064, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v14064);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v14067) {
  tll_ptr ifte_ret_t13;
  if (b_v14067) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v14068, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v14068);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v14069, tll_ptr y_v14070) {
  tll_ptr add_ret_t18; tll_ptr add_ret_t19; tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  if (x_v14069) {
    if (y_v14070) {
      add_ret_t18 = x_v14069 - 1;
      add_ret_t19 = y_v14070 - 1;
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

tll_ptr lam_fun_t23(tll_ptr y_v14073, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v14073);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v14071, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v14071);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v14074, tll_ptr y_v14075) {
  tll_ptr add_ret_t28; tll_ptr add_ret_t29; tll_ptr call_ret_t27;
  tll_ptr ifte_ret_t30; tll_ptr ifte_ret_t31; tll_ptr ifte_ret_t32;
  if (x_v14074) {
    if (y_v14075) {
      add_ret_t28 = x_v14074 - 1;
      add_ret_t29 = y_v14075 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v14075) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v14078, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v14078);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v14076, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v14076);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v14079, tll_ptr y_v14080) {
  tll_ptr add_ret_t39; tll_ptr add_ret_t40; tll_ptr call_ret_t38;
  tll_ptr ifte_ret_t41; tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t43;
  if (x_v14079) {
    if (y_v14080) {
      add_ret_t39 = x_v14079 - 1;
      add_ret_t40 = y_v14080 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v14080) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v14083, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v14083);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v14081, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v14081);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v14084, tll_ptr y_v14085) {
  tll_ptr add_ret_t50; tll_ptr add_ret_t51; tll_ptr call_ret_t49;
  tll_ptr ifte_ret_t52; tll_ptr ifte_ret_t53;
  if (x_v14084) {
    if (y_v14085) {
      add_ret_t50 = x_v14084 - 1;
      add_ret_t51 = y_v14085 - 1;
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

tll_ptr lam_fun_t55(tll_ptr y_v14088, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v14088);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v14086, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v14086);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v14089, tll_ptr y_v14090) {
  tll_ptr add_ret_t60; tll_ptr add_ret_t61; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t62; tll_ptr ifte_ret_t63; tll_ptr ifte_ret_t64;
  if (x_v14089) {
    if (y_v14090) {
      add_ret_t60 = x_v14089 - 1;
      add_ret_t61 = y_v14090 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v14090) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v14093, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v14093);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v14091, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v14091);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v14094) {
  tll_ptr add_ret_t70; tll_ptr ifte_ret_t71;
  if (x_v14094) {
    add_ret_t70 = x_v14094 - 1;
    ifte_ret_t71 = add_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v14095, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v14095);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v14096, tll_ptr y_v14097) {
  tll_ptr add_ret_t76; tll_ptr add_ret_t77; tll_ptr call_ret_t75;
  tll_ptr ifte_ret_t78;
  if (x_v14096) {
    add_ret_t76 = x_v14096 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v14097);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v14097;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v14100, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v14100);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v14098, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v14098);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v14101, tll_ptr y_v14102) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v14102) {
    call_ret_t85 = pred_i9(x_v14101);
    add_ret_t86 = y_v14102 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v14101;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v14105, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v14105);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v14103, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v14103);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v14106, tll_ptr y_v14107) {
  tll_ptr add_ret_t95; tll_ptr call_ret_t93; tll_ptr call_ret_t94;
  tll_ptr ifte_ret_t96;
  if (x_v14106) {
    add_ret_t95 = x_v14106 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v14107);
    call_ret_t93 = addn_i10(y_v14107, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v14110, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v14110);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v14108, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v14108);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v14111, tll_ptr y_v14112) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v14111, y_v14112);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v14111, y_v14112);
    call_ret_t103 = divn_i13(call_ret_t104, y_v14112);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v14115, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v14115);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v14113, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v14113);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v14116, tll_ptr y_v14117) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v14116, y_v14117);
  call_ret_t113 = muln_i12(call_ret_t114, y_v14117);
  call_ret_t112 = subn_i11(x_v14116, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v14120, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v14120);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v14118, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v14118);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v14121, tll_ptr s2_v14122) {
  tll_ptr String_t122; tll_ptr c_v14123; tll_ptr call_ret_t121;
  tll_ptr s1_v14124; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v14121)->tag) {
    case 2:
      switch_ret_t120 = s2_v14122;
      break;
    case 3:
      c_v14123 = ((tll_node)s1_v14121)->data[0];
      s1_v14124 = ((tll_node)s1_v14121)->data[1];
      call_ret_t121 = cats_i15(s1_v14124, s2_v14122);
      instr_struct(&String_t122, 3, 2, c_v14123, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v14127, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v14127);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v14125, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v14125);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v14128) {
  tll_ptr __v14129; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v14130; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v14128)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v14129 = ((tll_node)s_v14128)->data[0];
      s_v14130 = ((tll_node)s_v14128)->data[1];
      call_ret_t129 = strlen_i16(s_v14130);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v14131, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v14131);
  return call_ret_t131;
}

tll_ptr lenUU_i39(tll_ptr A_v14132, tll_ptr xs_v14133) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v14136; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v14134; tll_ptr xs_v14135; tll_ptr xs_v14137;
  switch(((tll_node)xs_v14133)->tag) {
    case 12:
      instr_struct(&nilUU_t135, 12, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 13:
      x_v14134 = ((tll_node)xs_v14133)->data[0];
      xs_v14135 = ((tll_node)xs_v14133)->data[1];
      call_ret_t137 = lenUU_i39(0, xs_v14135);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v14136 = ((tll_node)call_ret_t137)->data[0];
          xs_v14137 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v14136 + 1;
          instr_struct(&consUU_t140, 13, 2, x_v14134, xs_v14137);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v14140, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i39(env[0], xs_v14140);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v14138, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v14138);
  return lam_clo_t144;
}

tll_ptr lenUL_i38(tll_ptr A_v14141, tll_ptr xs_v14142) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v14145; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v14143; tll_ptr xs_v14144; tll_ptr xs_v14146;
  switch(((tll_node)xs_v14142)->tag) {
    case 10:
      instr_free_struct(xs_v14142);
      instr_struct(&nilUL_t148, 10, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 11:
      x_v14143 = ((tll_node)xs_v14142)->data[0];
      xs_v14144 = ((tll_node)xs_v14142)->data[1];
      instr_free_struct(xs_v14142);
      call_ret_t150 = lenUL_i38(0, xs_v14144);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v14145 = ((tll_node)call_ret_t150)->data[0];
          xs_v14146 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v14145 + 1;
          instr_struct(&consUL_t153, 11, 2, x_v14143, xs_v14146);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v14149, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i38(env[0], xs_v14149);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v14147, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v14147);
  return lam_clo_t157;
}

tll_ptr lenLL_i36(tll_ptr A_v14150, tll_ptr xs_v14151) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v14154; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v14152; tll_ptr xs_v14153; tll_ptr xs_v14155;
  switch(((tll_node)xs_v14151)->tag) {
    case 6:
      instr_free_struct(xs_v14151);
      instr_struct(&nilLL_t161, 6, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 7:
      x_v14152 = ((tll_node)xs_v14151)->data[0];
      xs_v14153 = ((tll_node)xs_v14151)->data[1];
      instr_free_struct(xs_v14151);
      call_ret_t163 = lenLL_i36(0, xs_v14153);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v14154 = ((tll_node)call_ret_t163)->data[0];
          xs_v14155 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v14154 + 1;
          instr_struct(&consLL_t166, 7, 2, x_v14152, xs_v14155);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v14158, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i36(env[0], xs_v14158);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v14156, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v14156);
  return lam_clo_t170;
}

tll_ptr appendUU_i43(tll_ptr A_v14159, tll_ptr xs_v14160, tll_ptr ys_v14161) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v14162; tll_ptr xs_v14163;
  switch(((tll_node)xs_v14160)->tag) {
    case 12:
      switch_ret_t173 = ys_v14161;
      break;
    case 13:
      x_v14162 = ((tll_node)xs_v14160)->data[0];
      xs_v14163 = ((tll_node)xs_v14160)->data[1];
      call_ret_t174 = appendUU_i43(0, xs_v14163, ys_v14161);
      instr_struct(&consUU_t175, 13, 2, x_v14162, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v14169, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i43(env[1], env[0], ys_v14169);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v14167, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v14167, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v14164, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v14164);
  return lam_clo_t180;
}

tll_ptr appendUL_i42(tll_ptr A_v14170, tll_ptr xs_v14171, tll_ptr ys_v14172) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v14173; tll_ptr xs_v14174;
  switch(((tll_node)xs_v14171)->tag) {
    case 10:
      instr_free_struct(xs_v14171);
      switch_ret_t183 = ys_v14172;
      break;
    case 11:
      x_v14173 = ((tll_node)xs_v14171)->data[0];
      xs_v14174 = ((tll_node)xs_v14171)->data[1];
      instr_free_struct(xs_v14171);
      call_ret_t184 = appendUL_i42(0, xs_v14174, ys_v14172);
      instr_struct(&consUL_t185, 11, 2, x_v14173, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v14180, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i42(env[1], env[0], ys_v14180);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v14178, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v14178, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v14175, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v14175);
  return lam_clo_t190;
}

tll_ptr appendLL_i40(tll_ptr A_v14181, tll_ptr xs_v14182, tll_ptr ys_v14183) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v14184; tll_ptr xs_v14185;
  switch(((tll_node)xs_v14182)->tag) {
    case 6:
      instr_free_struct(xs_v14182);
      switch_ret_t193 = ys_v14183;
      break;
    case 7:
      x_v14184 = ((tll_node)xs_v14182)->data[0];
      xs_v14185 = ((tll_node)xs_v14182)->data[1];
      instr_free_struct(xs_v14182);
      call_ret_t194 = appendLL_i40(0, xs_v14185, ys_v14183);
      instr_struct(&consLL_t195, 7, 2, x_v14184, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v14191, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i40(env[1], env[0], ys_v14191);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v14189, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v14189, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v14186, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v14186);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v14193, tll_env env) {
  tll_ptr __v14202; tll_ptr ch_v14200; tll_ptr ch_v14201; tll_ptr ch_v14204;
  tll_ptr ch_v14205; tll_ptr prim_ch_t203; tll_ptr recv_msg_t205;
  tll_ptr s_v14203; tll_ptr send_ch_t204; tll_ptr send_ch_t207;
  tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v14200 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v14200, (tll_ptr)1);
  ch_v14201 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v14201);
  __v14202 = recv_msg_t205;
  switch(((tll_node)__v14202)->tag) {
    case 0:
      s_v14203 = ((tll_node)__v14202)->data[0];
      ch_v14204 = ((tll_node)__v14202)->data[1];
      instr_free_struct(__v14202);
      instr_send(&send_ch_t207, ch_v14204, (tll_ptr)0);
      ch_v14205 = send_ch_t207;
      switch_ret_t206 = s_v14203;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v14192) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v14206, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v14206);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v14208, tll_env env) {
  tll_ptr ch_v14213; tll_ptr ch_v14214; tll_ptr ch_v14215; tll_ptr ch_v14216;
  tll_ptr prim_ch_t213; tll_ptr send_ch_t214; tll_ptr send_ch_t215;
  tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v14213 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v14213, (tll_ptr)1);
  ch_v14214 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v14214, env[0]);
  ch_v14215 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v14215, (tll_ptr)0);
  ch_v14216 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v14207) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v14207);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v14217, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v14217);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v14219, tll_env env) {
  tll_ptr ch_v14224; tll_ptr ch_v14225; tll_ptr ch_v14226; tll_ptr ch_v14227;
  tll_ptr prim_ch_t222; tll_ptr send_ch_t223; tll_ptr send_ch_t224;
  tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v14224 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v14224, (tll_ptr)1);
  ch_v14225 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v14225, env[0]);
  ch_v14226 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v14226, (tll_ptr)0);
  ch_v14227 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v14218) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v14218);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v14228, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v14228);
  return call_ret_t228;
}

tll_ptr splitU_i45(tll_ptr zs_v14229) {
  tll_ptr __v14234; tll_ptr call_ret_t240; tll_ptr consUU_t237;
  tll_ptr consUU_t242; tll_ptr consUU_t243; tll_ptr nilUU_t232;
  tll_ptr nilUU_t233; tll_ptr nilUU_t236; tll_ptr nilUU_t238;
  tll_ptr pair_struct_t234; tll_ptr pair_struct_t239;
  tll_ptr pair_struct_t244; tll_ptr switch_ret_t231; tll_ptr switch_ret_t235;
  tll_ptr switch_ret_t241; tll_ptr x_v14230; tll_ptr xs_v14235;
  tll_ptr y_v14232; tll_ptr ys_v14236; tll_ptr zs_v14231; tll_ptr zs_v14233;
  switch(((tll_node)zs_v14229)->tag) {
    case 12:
      instr_struct(&nilUU_t232, 12, 0);
      instr_struct(&nilUU_t233, 12, 0);
      instr_struct(&pair_struct_t234, 0, 2, nilUU_t232, nilUU_t233);
      switch_ret_t231 = pair_struct_t234;
      break;
    case 13:
      x_v14230 = ((tll_node)zs_v14229)->data[0];
      zs_v14231 = ((tll_node)zs_v14229)->data[1];
      switch(((tll_node)zs_v14231)->tag) {
        case 12:
          instr_struct(&nilUU_t236, 12, 0);
          instr_struct(&consUU_t237, 13, 2, x_v14230, nilUU_t236);
          instr_struct(&nilUU_t238, 12, 0);
          instr_struct(&pair_struct_t239, 0, 2, consUU_t237, nilUU_t238);
          switch_ret_t235 = pair_struct_t239;
          break;
        case 13:
          y_v14232 = ((tll_node)zs_v14231)->data[0];
          zs_v14233 = ((tll_node)zs_v14231)->data[1];
          call_ret_t240 = splitU_i45(zs_v14233);
          __v14234 = call_ret_t240;
          switch(((tll_node)__v14234)->tag) {
            case 0:
              xs_v14235 = ((tll_node)__v14234)->data[0];
              ys_v14236 = ((tll_node)__v14234)->data[1];
              instr_free_struct(__v14234);
              instr_struct(&consUU_t242, 13, 2, x_v14230, xs_v14235);
              instr_struct(&consUU_t243, 13, 2, y_v14232, ys_v14236);
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

tll_ptr lam_fun_t246(tll_ptr zs_v14237, tll_env env) {
  tll_ptr call_ret_t245;
  call_ret_t245 = splitU_i45(zs_v14237);
  return call_ret_t245;
}

tll_ptr splitL_i44(tll_ptr zs_v14238) {
  tll_ptr __v14243; tll_ptr call_ret_t257; tll_ptr consUL_t254;
  tll_ptr consUL_t259; tll_ptr consUL_t260; tll_ptr nilUL_t249;
  tll_ptr nilUL_t250; tll_ptr nilUL_t253; tll_ptr nilUL_t255;
  tll_ptr pair_struct_t251; tll_ptr pair_struct_t256;
  tll_ptr pair_struct_t261; tll_ptr switch_ret_t248; tll_ptr switch_ret_t252;
  tll_ptr switch_ret_t258; tll_ptr x_v14239; tll_ptr xs_v14244;
  tll_ptr y_v14241; tll_ptr ys_v14245; tll_ptr zs_v14240; tll_ptr zs_v14242;
  switch(((tll_node)zs_v14238)->tag) {
    case 10:
      instr_free_struct(zs_v14238);
      instr_struct(&nilUL_t249, 10, 0);
      instr_struct(&nilUL_t250, 10, 0);
      instr_struct(&pair_struct_t251, 0, 2, nilUL_t249, nilUL_t250);
      switch_ret_t248 = pair_struct_t251;
      break;
    case 11:
      x_v14239 = ((tll_node)zs_v14238)->data[0];
      zs_v14240 = ((tll_node)zs_v14238)->data[1];
      instr_free_struct(zs_v14238);
      switch(((tll_node)zs_v14240)->tag) {
        case 10:
          instr_free_struct(zs_v14240);
          instr_struct(&nilUL_t253, 10, 0);
          instr_struct(&consUL_t254, 11, 2, x_v14239, nilUL_t253);
          instr_struct(&nilUL_t255, 10, 0);
          instr_struct(&pair_struct_t256, 0, 2, consUL_t254, nilUL_t255);
          switch_ret_t252 = pair_struct_t256;
          break;
        case 11:
          y_v14241 = ((tll_node)zs_v14240)->data[0];
          zs_v14242 = ((tll_node)zs_v14240)->data[1];
          instr_free_struct(zs_v14240);
          call_ret_t257 = splitL_i44(zs_v14242);
          __v14243 = call_ret_t257;
          switch(((tll_node)__v14243)->tag) {
            case 0:
              xs_v14244 = ((tll_node)__v14243)->data[0];
              ys_v14245 = ((tll_node)__v14243)->data[1];
              instr_free_struct(__v14243);
              instr_struct(&consUL_t259, 11, 2, x_v14239, xs_v14244);
              instr_struct(&consUL_t260, 11, 2, y_v14241, ys_v14245);
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

tll_ptr lam_fun_t263(tll_ptr zs_v14246, tll_env env) {
  tll_ptr call_ret_t262;
  call_ret_t262 = splitL_i44(zs_v14246);
  return call_ret_t262;
}

tll_ptr mergeU_i47(tll_ptr xs_v14247, tll_ptr ys_v14248) {
  tll_ptr call_ret_t268; tll_ptr call_ret_t269; tll_ptr call_ret_t272;
  tll_ptr consUU_t267; tll_ptr consUU_t270; tll_ptr consUU_t271;
  tll_ptr consUU_t273; tll_ptr consUU_t274; tll_ptr ifte_ret_t275;
  tll_ptr switch_ret_t265; tll_ptr switch_ret_t266; tll_ptr x_v14249;
  tll_ptr xs0_v14250; tll_ptr y_v14251; tll_ptr ys0_v14252;
  switch(((tll_node)xs_v14247)->tag) {
    case 12:
      switch_ret_t265 = ys_v14248;
      break;
    case 13:
      x_v14249 = ((tll_node)xs_v14247)->data[0];
      xs0_v14250 = ((tll_node)xs_v14247)->data[1];
      switch(((tll_node)ys_v14248)->tag) {
        case 12:
          instr_struct(&consUU_t267, 13, 2, x_v14249, xs0_v14250);
          switch_ret_t266 = consUU_t267;
          break;
        case 13:
          y_v14251 = ((tll_node)ys_v14248)->data[0];
          ys0_v14252 = ((tll_node)ys_v14248)->data[1];
          call_ret_t268 = lten_i4(x_v14249, y_v14251);
          if (call_ret_t268) {
            instr_struct(&consUU_t270, 13, 2, y_v14251, ys0_v14252);
            call_ret_t269 = mergeU_i47(xs0_v14250, consUU_t270);
            instr_struct(&consUU_t271, 13, 2, x_v14249, call_ret_t269);
            ifte_ret_t275 = consUU_t271;
          }
          else {
            instr_struct(&consUU_t273, 13, 2, x_v14249, xs0_v14250);
            call_ret_t272 = mergeU_i47(consUU_t273, ys0_v14252);
            instr_struct(&consUU_t274, 13, 2, y_v14251, call_ret_t272);
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

tll_ptr lam_fun_t277(tll_ptr ys_v14255, tll_env env) {
  tll_ptr call_ret_t276;
  call_ret_t276 = mergeU_i47(env[0], ys_v14255);
  return call_ret_t276;
}

tll_ptr lam_fun_t279(tll_ptr xs_v14253, tll_env env) {
  tll_ptr lam_clo_t278;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 1, xs_v14253);
  return lam_clo_t278;
}

tll_ptr mergeL_i46(tll_ptr xs_v14256, tll_ptr ys_v14257) {
  tll_ptr call_ret_t284; tll_ptr call_ret_t285; tll_ptr call_ret_t288;
  tll_ptr consUL_t283; tll_ptr consUL_t286; tll_ptr consUL_t287;
  tll_ptr consUL_t289; tll_ptr consUL_t290; tll_ptr ifte_ret_t291;
  tll_ptr switch_ret_t281; tll_ptr switch_ret_t282; tll_ptr x_v14258;
  tll_ptr xs0_v14259; tll_ptr y_v14260; tll_ptr ys0_v14261;
  switch(((tll_node)xs_v14256)->tag) {
    case 10:
      instr_free_struct(xs_v14256);
      switch_ret_t281 = ys_v14257;
      break;
    case 11:
      x_v14258 = ((tll_node)xs_v14256)->data[0];
      xs0_v14259 = ((tll_node)xs_v14256)->data[1];
      instr_free_struct(xs_v14256);
      switch(((tll_node)ys_v14257)->tag) {
        case 10:
          instr_free_struct(ys_v14257);
          instr_struct(&consUL_t283, 11, 2, x_v14258, xs0_v14259);
          switch_ret_t282 = consUL_t283;
          break;
        case 11:
          y_v14260 = ((tll_node)ys_v14257)->data[0];
          ys0_v14261 = ((tll_node)ys_v14257)->data[1];
          instr_free_struct(ys_v14257);
          call_ret_t284 = lten_i4(x_v14258, y_v14260);
          if (call_ret_t284) {
            instr_struct(&consUL_t286, 11, 2, y_v14260, ys0_v14261);
            call_ret_t285 = mergeL_i46(xs0_v14259, consUL_t286);
            instr_struct(&consUL_t287, 11, 2, x_v14258, call_ret_t285);
            ifte_ret_t291 = consUL_t287;
          }
          else {
            instr_struct(&consUL_t289, 11, 2, x_v14258, xs0_v14259);
            call_ret_t288 = mergeL_i46(consUL_t289, ys0_v14261);
            instr_struct(&consUL_t290, 11, 2, y_v14260, call_ret_t288);
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

tll_ptr lam_fun_t293(tll_ptr ys_v14264, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = mergeL_i46(env[0], ys_v14264);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v14262, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 1, xs_v14262);
  return lam_clo_t294;
}

tll_ptr msortU_i49(tll_ptr zs_v14265) {
  tll_ptr __v14270; tll_ptr call_ret_t302; tll_ptr call_ret_t306;
  tll_ptr call_ret_t307; tll_ptr call_ret_t308; tll_ptr consUU_t301;
  tll_ptr consUU_t303; tll_ptr consUU_t304; tll_ptr nilUU_t298;
  tll_ptr nilUU_t300; tll_ptr switch_ret_t297; tll_ptr switch_ret_t299;
  tll_ptr switch_ret_t305; tll_ptr x_v14266; tll_ptr xs_v14271;
  tll_ptr y_v14268; tll_ptr ys_v14272; tll_ptr zs_v14267; tll_ptr zs_v14269;
  switch(((tll_node)zs_v14265)->tag) {
    case 12:
      instr_struct(&nilUU_t298, 12, 0);
      switch_ret_t297 = nilUU_t298;
      break;
    case 13:
      x_v14266 = ((tll_node)zs_v14265)->data[0];
      zs_v14267 = ((tll_node)zs_v14265)->data[1];
      switch(((tll_node)zs_v14267)->tag) {
        case 12:
          instr_struct(&nilUU_t300, 12, 0);
          instr_struct(&consUU_t301, 13, 2, x_v14266, nilUU_t300);
          switch_ret_t299 = consUU_t301;
          break;
        case 13:
          y_v14268 = ((tll_node)zs_v14267)->data[0];
          zs_v14269 = ((tll_node)zs_v14267)->data[1];
          instr_struct(&consUU_t303, 13, 2, y_v14268, zs_v14269);
          instr_struct(&consUU_t304, 13, 2, x_v14266, consUU_t303);
          call_ret_t302 = splitU_i45(consUU_t304);
          __v14270 = call_ret_t302;
          switch(((tll_node)__v14270)->tag) {
            case 0:
              xs_v14271 = ((tll_node)__v14270)->data[0];
              ys_v14272 = ((tll_node)__v14270)->data[1];
              instr_free_struct(__v14270);
              call_ret_t307 = msortU_i49(xs_v14271);
              call_ret_t308 = msortU_i49(ys_v14272);
              call_ret_t306 = mergeU_i47(call_ret_t307, call_ret_t308);
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

tll_ptr lam_fun_t310(tll_ptr zs_v14273, tll_env env) {
  tll_ptr call_ret_t309;
  call_ret_t309 = msortU_i49(zs_v14273);
  return call_ret_t309;
}

tll_ptr msortL_i48(tll_ptr zs_v14274) {
  tll_ptr __v14279; tll_ptr call_ret_t317; tll_ptr call_ret_t321;
  tll_ptr call_ret_t322; tll_ptr call_ret_t323; tll_ptr consUL_t316;
  tll_ptr consUL_t318; tll_ptr consUL_t319; tll_ptr nilUL_t313;
  tll_ptr nilUL_t315; tll_ptr switch_ret_t312; tll_ptr switch_ret_t314;
  tll_ptr switch_ret_t320; tll_ptr x_v14275; tll_ptr xs_v14280;
  tll_ptr y_v14277; tll_ptr ys_v14281; tll_ptr zs_v14276; tll_ptr zs_v14278;
  switch(((tll_node)zs_v14274)->tag) {
    case 10:
      instr_free_struct(zs_v14274);
      instr_struct(&nilUL_t313, 10, 0);
      switch_ret_t312 = nilUL_t313;
      break;
    case 11:
      x_v14275 = ((tll_node)zs_v14274)->data[0];
      zs_v14276 = ((tll_node)zs_v14274)->data[1];
      instr_free_struct(zs_v14274);
      switch(((tll_node)zs_v14276)->tag) {
        case 10:
          instr_free_struct(zs_v14276);
          instr_struct(&nilUL_t315, 10, 0);
          instr_struct(&consUL_t316, 11, 2, x_v14275, nilUL_t315);
          switch_ret_t314 = consUL_t316;
          break;
        case 11:
          y_v14277 = ((tll_node)zs_v14276)->data[0];
          zs_v14278 = ((tll_node)zs_v14276)->data[1];
          instr_free_struct(zs_v14276);
          instr_struct(&consUL_t318, 11, 2, y_v14277, zs_v14278);
          instr_struct(&consUL_t319, 11, 2, x_v14275, consUL_t318);
          call_ret_t317 = splitL_i44(consUL_t319);
          __v14279 = call_ret_t317;
          switch(((tll_node)__v14279)->tag) {
            case 0:
              xs_v14280 = ((tll_node)__v14279)->data[0];
              ys_v14281 = ((tll_node)__v14279)->data[1];
              instr_free_struct(__v14279);
              call_ret_t322 = msortL_i48(xs_v14280);
              call_ret_t323 = msortL_i48(ys_v14281);
              call_ret_t321 = mergeL_i46(call_ret_t322, call_ret_t323);
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

tll_ptr lam_fun_t325(tll_ptr zs_v14282, tll_env env) {
  tll_ptr call_ret_t324;
  call_ret_t324 = msortL_i48(zs_v14282);
  return call_ret_t324;
}

tll_ptr lam_fun_t330(tll_ptr __v14286, tll_env env) {
  tll_ptr c_v14288; tll_ptr nilUU_t329; tll_ptr send_ch_t328;
  instr_struct(&nilUU_t329, 12, 0);
  instr_send(&send_ch_t328, env[0], nilUU_t329);
  c_v14288 = send_ch_t328;
  return 0;
}

tll_ptr lam_fun_t335(tll_ptr __v14291, tll_env env) {
  tll_ptr c_v14293; tll_ptr nilUU_t334; tll_ptr send_ch_t333;
  instr_struct(&nilUU_t334, 12, 0);
  instr_send(&send_ch_t333, env[0], nilUU_t334);
  c_v14293 = send_ch_t333;
  return 0;
}

tll_ptr fork_fun_t344(tll_env env) {
  tll_ptr add_ret_t342; tll_ptr app_ret_t343; tll_ptr call_ret_t341;
  tll_ptr fork_ret_t346;
  add_ret_t342 = env[2] - 1;
  call_ret_t341 = cmsort_workerU_i53(add_ret_t342, env[1], env[0]);
  instr_app(&app_ret_t343, call_ret_t341, 0);
  instr_free_clo(call_ret_t341);
  fork_ret_t346 = app_ret_t343;
  instr_free_thread(env);
  return fork_ret_t346;
}

tll_ptr lam_fun_t353(tll_ptr __v14299, tll_env env) {
  tll_ptr __v14312; tll_ptr __v14317; tll_ptr c_v14316;
  tll_ptr call_ret_t347; tll_ptr call_ret_t350; tll_ptr close_tmp_t352;
  tll_ptr fork_ch_t345; tll_ptr r_v14309; tll_ptr r_v14314;
  tll_ptr recv_msg_t348; tll_ptr send_ch_t351; tll_ptr switch_ret_t349;
  tll_ptr xs1_v14313; tll_ptr ys1_v14311; tll_ptr zs_v14315;
  instr_fork(&fork_ch_t345, &fork_fun_t344, 2, env[1], env[3]);
  r_v14309 = fork_ch_t345;
  call_ret_t347 = msortU_i49(env[0]);
  ys1_v14311 = call_ret_t347;
  instr_recv(&recv_msg_t348, r_v14309);
  __v14312 = recv_msg_t348;
  switch(((tll_node)__v14312)->tag) {
    case 0:
      xs1_v14313 = ((tll_node)__v14312)->data[0];
      r_v14314 = ((tll_node)__v14312)->data[1];
      instr_free_struct(__v14312);
      call_ret_t350 = mergeU_i47(xs1_v14313, ys1_v14311);
      zs_v14315 = call_ret_t350;
      instr_send(&send_ch_t351, env[2], zs_v14315);
      c_v14316 = send_ch_t351;
      instr_close(&close_tmp_t352, r_v14314);
      __v14317 = close_tmp_t352;
      switch_ret_t349 = 0;
      break;
  }
  return switch_ret_t349;
}

tll_ptr lam_fun_t356(tll_ptr __v14325, tll_env env) {
  tll_ptr send_ch_t355;
  instr_send(&send_ch_t355, env[1], env[0]);
  return send_ch_t355;
}

tll_ptr lam_fun_t358(tll_ptr x_v14323, tll_env env) {
  tll_ptr lam_clo_t357;
  instr_clo(&lam_clo_t357, &lam_fun_t356, 2, x_v14323, env[0]);
  return lam_clo_t357;
}

tll_ptr lam_fun_t363(tll_ptr __v14318, tll_env env) {
  tll_ptr app_ret_t361; tll_ptr app_ret_t362; tll_ptr c_v14322;
  tll_ptr call_ret_t360; tll_ptr lam_clo_t359;
  instr_clo(&lam_clo_t359, &lam_fun_t358, 1, env[0]);
  call_ret_t360 = msortU_i49(env[1]);
  instr_app(&app_ret_t361, lam_clo_t359, call_ret_t360);
  instr_free_clo(lam_clo_t359);
  instr_app(&app_ret_t362, app_ret_t361, 0);
  instr_free_clo(app_ret_t361);
  c_v14322 = app_ret_t362;
  return 0;
}

tll_ptr cmsort_workerU_i53(tll_ptr n_v14283, tll_ptr zs_v14284, tll_ptr c_v14285) {
  tll_ptr __v14296; tll_ptr call_ret_t337; tll_ptr consUU_t338;
  tll_ptr consUU_t339; tll_ptr ifte_ret_t365; tll_ptr lam_clo_t331;
  tll_ptr lam_clo_t336; tll_ptr lam_clo_t354; tll_ptr lam_clo_t364;
  tll_ptr switch_ret_t327; tll_ptr switch_ret_t332; tll_ptr switch_ret_t340;
  tll_ptr xs0_v14297; tll_ptr ys0_v14298; tll_ptr z0_v14289;
  tll_ptr z1_v14294; tll_ptr zs0_v14290; tll_ptr zs1_v14295;
  if (n_v14283) {
    switch(((tll_node)zs_v14284)->tag) {
      case 12:
        instr_clo(&lam_clo_t331, &lam_fun_t330, 1, c_v14285);
        switch_ret_t327 = lam_clo_t331;
        break;
      case 13:
        z0_v14289 = ((tll_node)zs_v14284)->data[0];
        zs0_v14290 = ((tll_node)zs_v14284)->data[1];
        switch(((tll_node)zs0_v14290)->tag) {
          case 12:
            instr_clo(&lam_clo_t336, &lam_fun_t335, 1, c_v14285);
            switch_ret_t332 = lam_clo_t336;
            break;
          case 13:
            z1_v14294 = ((tll_node)zs0_v14290)->data[0];
            zs1_v14295 = ((tll_node)zs0_v14290)->data[1];
            instr_struct(&consUU_t338, 13, 2, z1_v14294, zs1_v14295);
            instr_struct(&consUU_t339, 13, 2, z0_v14289, consUU_t338);
            call_ret_t337 = splitU_i45(consUU_t339);
            __v14296 = call_ret_t337;
            switch(((tll_node)__v14296)->tag) {
              case 0:
                xs0_v14297 = ((tll_node)__v14296)->data[0];
                ys0_v14298 = ((tll_node)__v14296)->data[1];
                instr_free_struct(__v14296);
                instr_clo(&lam_clo_t354, &lam_fun_t353, 4,
                          ys0_v14298, xs0_v14297, c_v14285, n_v14283);
                switch_ret_t340 = lam_clo_t354;
                break;
            }
            switch_ret_t332 = switch_ret_t340;
            break;
        }
        switch_ret_t327 = switch_ret_t332;
        break;
    }
    ifte_ret_t365 = switch_ret_t327;
  }
  else {
    instr_clo(&lam_clo_t364, &lam_fun_t363, 2, c_v14285, zs_v14284);
    ifte_ret_t365 = lam_clo_t364;
  }
  return ifte_ret_t365;
}

tll_ptr lam_fun_t367(tll_ptr c_v14331, tll_env env) {
  tll_ptr call_ret_t366;
  call_ret_t366 = cmsort_workerU_i53(env[1], env[0], c_v14331);
  return call_ret_t366;
}

tll_ptr lam_fun_t369(tll_ptr zs_v14329, tll_env env) {
  tll_ptr lam_clo_t368;
  instr_clo(&lam_clo_t368, &lam_fun_t367, 2, zs_v14329, env[0]);
  return lam_clo_t368;
}

tll_ptr lam_fun_t371(tll_ptr n_v14326, tll_env env) {
  tll_ptr lam_clo_t370;
  instr_clo(&lam_clo_t370, &lam_fun_t369, 1, n_v14326);
  return lam_clo_t370;
}

tll_ptr lam_fun_t376(tll_ptr __v14335, tll_env env) {
  tll_ptr c_v14337; tll_ptr nilUL_t375; tll_ptr send_ch_t374;
  instr_struct(&nilUL_t375, 10, 0);
  instr_send(&send_ch_t374, env[0], nilUL_t375);
  c_v14337 = send_ch_t374;
  return 0;
}

tll_ptr lam_fun_t381(tll_ptr __v14340, tll_env env) {
  tll_ptr c_v14342; tll_ptr nilUL_t380; tll_ptr send_ch_t379;
  instr_struct(&nilUL_t380, 10, 0);
  instr_send(&send_ch_t379, env[0], nilUL_t380);
  c_v14342 = send_ch_t379;
  return 0;
}

tll_ptr fork_fun_t390(tll_env env) {
  tll_ptr add_ret_t388; tll_ptr app_ret_t389; tll_ptr call_ret_t387;
  tll_ptr fork_ret_t392;
  add_ret_t388 = env[2] - 1;
  call_ret_t387 = cmsort_workerL_i52(add_ret_t388, env[1], env[0]);
  instr_app(&app_ret_t389, call_ret_t387, 0);
  instr_free_clo(call_ret_t387);
  fork_ret_t392 = app_ret_t389;
  instr_free_thread(env);
  return fork_ret_t392;
}

tll_ptr lam_fun_t399(tll_ptr __v14348, tll_env env) {
  tll_ptr __v14361; tll_ptr __v14366; tll_ptr c_v14365;
  tll_ptr call_ret_t393; tll_ptr call_ret_t396; tll_ptr close_tmp_t398;
  tll_ptr fork_ch_t391; tll_ptr r_v14358; tll_ptr r_v14363;
  tll_ptr recv_msg_t394; tll_ptr send_ch_t397; tll_ptr switch_ret_t395;
  tll_ptr xs1_v14362; tll_ptr ys1_v14360; tll_ptr zs_v14364;
  instr_fork(&fork_ch_t391, &fork_fun_t390, 2, env[1], env[3]);
  r_v14358 = fork_ch_t391;
  call_ret_t393 = msortL_i48(env[0]);
  ys1_v14360 = call_ret_t393;
  instr_recv(&recv_msg_t394, r_v14358);
  __v14361 = recv_msg_t394;
  switch(((tll_node)__v14361)->tag) {
    case 0:
      xs1_v14362 = ((tll_node)__v14361)->data[0];
      r_v14363 = ((tll_node)__v14361)->data[1];
      instr_free_struct(__v14361);
      call_ret_t396 = mergeL_i46(xs1_v14362, ys1_v14360);
      zs_v14364 = call_ret_t396;
      instr_send(&send_ch_t397, env[2], zs_v14364);
      c_v14365 = send_ch_t397;
      instr_close(&close_tmp_t398, r_v14363);
      __v14366 = close_tmp_t398;
      switch_ret_t395 = 0;
      break;
  }
  return switch_ret_t395;
}

tll_ptr lam_fun_t402(tll_ptr __v14374, tll_env env) {
  tll_ptr send_ch_t401;
  instr_send(&send_ch_t401, env[1], env[0]);
  return send_ch_t401;
}

tll_ptr lam_fun_t404(tll_ptr x_v14372, tll_env env) {
  tll_ptr lam_clo_t403;
  instr_clo(&lam_clo_t403, &lam_fun_t402, 2, x_v14372, env[0]);
  return lam_clo_t403;
}

tll_ptr lam_fun_t409(tll_ptr __v14367, tll_env env) {
  tll_ptr app_ret_t407; tll_ptr app_ret_t408; tll_ptr c_v14371;
  tll_ptr call_ret_t406; tll_ptr lam_clo_t405;
  instr_clo(&lam_clo_t405, &lam_fun_t404, 1, env[0]);
  call_ret_t406 = msortL_i48(env[1]);
  instr_app(&app_ret_t407, lam_clo_t405, call_ret_t406);
  instr_free_clo(lam_clo_t405);
  instr_app(&app_ret_t408, app_ret_t407, 0);
  instr_free_clo(app_ret_t407);
  c_v14371 = app_ret_t408;
  return 0;
}

tll_ptr cmsort_workerL_i52(tll_ptr n_v14332, tll_ptr zs_v14333, tll_ptr c_v14334) {
  tll_ptr __v14345; tll_ptr call_ret_t383; tll_ptr consUL_t384;
  tll_ptr consUL_t385; tll_ptr ifte_ret_t411; tll_ptr lam_clo_t377;
  tll_ptr lam_clo_t382; tll_ptr lam_clo_t400; tll_ptr lam_clo_t410;
  tll_ptr switch_ret_t373; tll_ptr switch_ret_t378; tll_ptr switch_ret_t386;
  tll_ptr xs0_v14346; tll_ptr ys0_v14347; tll_ptr z0_v14338;
  tll_ptr z1_v14343; tll_ptr zs0_v14339; tll_ptr zs1_v14344;
  if (n_v14332) {
    switch(((tll_node)zs_v14333)->tag) {
      case 10:
        instr_free_struct(zs_v14333);
        instr_clo(&lam_clo_t377, &lam_fun_t376, 1, c_v14334);
        switch_ret_t373 = lam_clo_t377;
        break;
      case 11:
        z0_v14338 = ((tll_node)zs_v14333)->data[0];
        zs0_v14339 = ((tll_node)zs_v14333)->data[1];
        instr_free_struct(zs_v14333);
        switch(((tll_node)zs0_v14339)->tag) {
          case 10:
            instr_free_struct(zs0_v14339);
            instr_clo(&lam_clo_t382, &lam_fun_t381, 1, c_v14334);
            switch_ret_t378 = lam_clo_t382;
            break;
          case 11:
            z1_v14343 = ((tll_node)zs0_v14339)->data[0];
            zs1_v14344 = ((tll_node)zs0_v14339)->data[1];
            instr_free_struct(zs0_v14339);
            instr_struct(&consUL_t384, 11, 2, z1_v14343, zs1_v14344);
            instr_struct(&consUL_t385, 11, 2, z0_v14338, consUL_t384);
            call_ret_t383 = splitL_i44(consUL_t385);
            __v14345 = call_ret_t383;
            switch(((tll_node)__v14345)->tag) {
              case 0:
                xs0_v14346 = ((tll_node)__v14345)->data[0];
                ys0_v14347 = ((tll_node)__v14345)->data[1];
                instr_free_struct(__v14345);
                instr_clo(&lam_clo_t400, &lam_fun_t399, 4,
                          ys0_v14347, xs0_v14346, c_v14334, n_v14332);
                switch_ret_t386 = lam_clo_t400;
                break;
            }
            switch_ret_t378 = switch_ret_t386;
            break;
        }
        switch_ret_t373 = switch_ret_t378;
        break;
    }
    ifte_ret_t411 = switch_ret_t373;
  }
  else {
    instr_clo(&lam_clo_t410, &lam_fun_t409, 2, c_v14334, zs_v14333);
    ifte_ret_t411 = lam_clo_t410;
  }
  return ifte_ret_t411;
}

tll_ptr lam_fun_t413(tll_ptr c_v14380, tll_env env) {
  tll_ptr call_ret_t412;
  call_ret_t412 = cmsort_workerL_i52(env[1], env[0], c_v14380);
  return call_ret_t412;
}

tll_ptr lam_fun_t415(tll_ptr zs_v14378, tll_env env) {
  tll_ptr lam_clo_t414;
  instr_clo(&lam_clo_t414, &lam_fun_t413, 2, zs_v14378, env[0]);
  return lam_clo_t414;
}

tll_ptr lam_fun_t417(tll_ptr n_v14375, tll_env env) {
  tll_ptr lam_clo_t416;
  instr_clo(&lam_clo_t416, &lam_fun_t415, 1, n_v14375);
  return lam_clo_t416;
}

tll_ptr fork_fun_t421(tll_env env) {
  tll_ptr app_ret_t420; tll_ptr call_ret_t419; tll_ptr fork_ret_t423;
  call_ret_t419 = cmsort_workerU_i53((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t420, call_ret_t419, 0);
  instr_free_clo(call_ret_t419);
  fork_ret_t423 = app_ret_t420;
  instr_free_thread(env);
  return fork_ret_t423;
}

tll_ptr lam_fun_t427(tll_ptr __v14382, tll_env env) {
  tll_ptr __v14391; tll_ptr __v14394; tll_ptr c_v14389; tll_ptr c_v14393;
  tll_ptr close_tmp_t426; tll_ptr fork_ch_t422; tll_ptr recv_msg_t424;
  tll_ptr switch_ret_t425; tll_ptr zs1_v14392;
  instr_fork(&fork_ch_t422, &fork_fun_t421, 1, env[0]);
  c_v14389 = fork_ch_t422;
  instr_recv(&recv_msg_t424, c_v14389);
  __v14391 = recv_msg_t424;
  switch(((tll_node)__v14391)->tag) {
    case 0:
      zs1_v14392 = ((tll_node)__v14391)->data[0];
      c_v14393 = ((tll_node)__v14391)->data[1];
      instr_free_struct(__v14391);
      instr_close(&close_tmp_t426, c_v14393);
      __v14394 = close_tmp_t426;
      switch_ret_t425 = zs1_v14392;
      break;
  }
  return switch_ret_t425;
}

tll_ptr cmsortU_i55(tll_ptr zs0_v14381) {
  tll_ptr lam_clo_t428;
  instr_clo(&lam_clo_t428, &lam_fun_t427, 1, zs0_v14381);
  return lam_clo_t428;
}

tll_ptr lam_fun_t430(tll_ptr zs0_v14395, tll_env env) {
  tll_ptr call_ret_t429;
  call_ret_t429 = cmsortU_i55(zs0_v14395);
  return call_ret_t429;
}

tll_ptr fork_fun_t434(tll_env env) {
  tll_ptr app_ret_t433; tll_ptr call_ret_t432; tll_ptr fork_ret_t436;
  call_ret_t432 = cmsort_workerL_i52((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t433, call_ret_t432, 0);
  instr_free_clo(call_ret_t432);
  fork_ret_t436 = app_ret_t433;
  instr_free_thread(env);
  return fork_ret_t436;
}

tll_ptr lam_fun_t440(tll_ptr __v14397, tll_env env) {
  tll_ptr __v14406; tll_ptr __v14409; tll_ptr c_v14404; tll_ptr c_v14408;
  tll_ptr close_tmp_t439; tll_ptr fork_ch_t435; tll_ptr recv_msg_t437;
  tll_ptr switch_ret_t438; tll_ptr zs1_v14407;
  instr_fork(&fork_ch_t435, &fork_fun_t434, 1, env[0]);
  c_v14404 = fork_ch_t435;
  instr_recv(&recv_msg_t437, c_v14404);
  __v14406 = recv_msg_t437;
  switch(((tll_node)__v14406)->tag) {
    case 0:
      zs1_v14407 = ((tll_node)__v14406)->data[0];
      c_v14408 = ((tll_node)__v14406)->data[1];
      instr_free_struct(__v14406);
      instr_close(&close_tmp_t439, c_v14408);
      __v14409 = close_tmp_t439;
      switch_ret_t438 = zs1_v14407;
      break;
  }
  return switch_ret_t438;
}

tll_ptr cmsortL_i54(tll_ptr zs0_v14396) {
  tll_ptr lam_clo_t441;
  instr_clo(&lam_clo_t441, &lam_fun_t440, 1, zs0_v14396);
  return lam_clo_t441;
}

tll_ptr lam_fun_t443(tll_ptr zs0_v14410, tll_env env) {
  tll_ptr call_ret_t442;
  call_ret_t442 = cmsortL_i54(zs0_v14410);
  return call_ret_t442;
}

tll_ptr mkListU_i57(tll_ptr n_v14411) {
  tll_ptr add_ret_t446; tll_ptr call_ret_t445; tll_ptr consUU_t447;
  tll_ptr ifte_ret_t449; tll_ptr nilUU_t448;
  if (n_v14411) {
    add_ret_t446 = n_v14411 - 1;
    call_ret_t445 = mkListU_i57(add_ret_t446);
    instr_struct(&consUU_t447, 13, 2, n_v14411, call_ret_t445);
    ifte_ret_t449 = consUU_t447;
  }
  else {
    instr_struct(&nilUU_t448, 12, 0);
    ifte_ret_t449 = nilUU_t448;
  }
  return ifte_ret_t449;
}

tll_ptr lam_fun_t451(tll_ptr n_v14412, tll_env env) {
  tll_ptr call_ret_t450;
  call_ret_t450 = mkListU_i57(n_v14412);
  return call_ret_t450;
}

tll_ptr mkListL_i56(tll_ptr n_v14413) {
  tll_ptr add_ret_t454; tll_ptr call_ret_t453; tll_ptr consUL_t455;
  tll_ptr ifte_ret_t457; tll_ptr nilUL_t456;
  if (n_v14413) {
    add_ret_t454 = n_v14413 - 1;
    call_ret_t453 = mkListL_i56(add_ret_t454);
    instr_struct(&consUL_t455, 11, 2, n_v14413, call_ret_t453);
    ifte_ret_t457 = consUL_t455;
  }
  else {
    instr_struct(&nilUL_t456, 10, 0);
    ifte_ret_t457 = nilUL_t456;
  }
  return ifte_ret_t457;
}

tll_ptr lam_fun_t459(tll_ptr n_v14414, tll_env env) {
  tll_ptr call_ret_t458;
  call_ret_t458 = mkListL_i56(n_v14414);
  return call_ret_t458;
}

int main() {
  instr_init();
  tll_ptr app_ret_t463; tll_ptr call_ret_t461; tll_ptr call_ret_t462;
  tll_ptr lam_clo_t101; tll_ptr lam_clo_t111; tll_ptr lam_clo_t119;
  tll_ptr lam_clo_t12; tll_ptr lam_clo_t127; tll_ptr lam_clo_t133;
  tll_ptr lam_clo_t146; tll_ptr lam_clo_t159; tll_ptr lam_clo_t16;
  tll_ptr lam_clo_t172; tll_ptr lam_clo_t182; tll_ptr lam_clo_t192;
  tll_ptr lam_clo_t202; tll_ptr lam_clo_t212; tll_ptr lam_clo_t221;
  tll_ptr lam_clo_t230; tll_ptr lam_clo_t247; tll_ptr lam_clo_t26;
  tll_ptr lam_clo_t264; tll_ptr lam_clo_t280; tll_ptr lam_clo_t296;
  tll_ptr lam_clo_t311; tll_ptr lam_clo_t326; tll_ptr lam_clo_t37;
  tll_ptr lam_clo_t372; tll_ptr lam_clo_t418; tll_ptr lam_clo_t431;
  tll_ptr lam_clo_t444; tll_ptr lam_clo_t452; tll_ptr lam_clo_t460;
  tll_ptr lam_clo_t48; tll_ptr lam_clo_t58; tll_ptr lam_clo_t6;
  tll_ptr lam_clo_t69; tll_ptr lam_clo_t74; tll_ptr lam_clo_t83;
  tll_ptr lam_clo_t92; tll_ptr sorted_v14416; tll_ptr test_v14415;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i58 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i59 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i60 = lam_clo_t16;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 0);
  ltenclo_i61 = lam_clo_t26;
  instr_clo(&lam_clo_t37, &lam_fun_t36, 0);
  gtenclo_i62 = lam_clo_t37;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  ltnclo_i63 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  gtnclo_i64 = lam_clo_t58;
  instr_clo(&lam_clo_t69, &lam_fun_t68, 0);
  eqnclo_i65 = lam_clo_t69;
  instr_clo(&lam_clo_t74, &lam_fun_t73, 0);
  predclo_i66 = lam_clo_t74;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i67 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i68 = lam_clo_t92;
  instr_clo(&lam_clo_t101, &lam_fun_t100, 0);
  mulnclo_i69 = lam_clo_t101;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 0);
  divnclo_i70 = lam_clo_t111;
  instr_clo(&lam_clo_t119, &lam_fun_t118, 0);
  modnclo_i71 = lam_clo_t119;
  instr_clo(&lam_clo_t127, &lam_fun_t126, 0);
  catsclo_i72 = lam_clo_t127;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 0);
  strlenclo_i73 = lam_clo_t133;
  instr_clo(&lam_clo_t146, &lam_fun_t145, 0);
  lenUUclo_i74 = lam_clo_t146;
  instr_clo(&lam_clo_t159, &lam_fun_t158, 0);
  lenULclo_i75 = lam_clo_t159;
  instr_clo(&lam_clo_t172, &lam_fun_t171, 0);
  lenLLclo_i76 = lam_clo_t172;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 0);
  appendUUclo_i77 = lam_clo_t182;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 0);
  appendULclo_i78 = lam_clo_t192;
  instr_clo(&lam_clo_t202, &lam_fun_t201, 0);
  appendLLclo_i79 = lam_clo_t202;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  readlineclo_i80 = lam_clo_t212;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 0);
  printclo_i81 = lam_clo_t221;
  instr_clo(&lam_clo_t230, &lam_fun_t229, 0);
  prerrclo_i82 = lam_clo_t230;
  instr_clo(&lam_clo_t247, &lam_fun_t246, 0);
  splitUclo_i83 = lam_clo_t247;
  instr_clo(&lam_clo_t264, &lam_fun_t263, 0);
  splitLclo_i84 = lam_clo_t264;
  instr_clo(&lam_clo_t280, &lam_fun_t279, 0);
  mergeUclo_i85 = lam_clo_t280;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 0);
  mergeLclo_i86 = lam_clo_t296;
  instr_clo(&lam_clo_t311, &lam_fun_t310, 0);
  msortUclo_i87 = lam_clo_t311;
  instr_clo(&lam_clo_t326, &lam_fun_t325, 0);
  msortLclo_i88 = lam_clo_t326;
  instr_clo(&lam_clo_t372, &lam_fun_t371, 0);
  cmsort_workerUclo_i89 = lam_clo_t372;
  instr_clo(&lam_clo_t418, &lam_fun_t417, 0);
  cmsort_workerLclo_i90 = lam_clo_t418;
  instr_clo(&lam_clo_t431, &lam_fun_t430, 0);
  cmsortUclo_i91 = lam_clo_t431;
  instr_clo(&lam_clo_t444, &lam_fun_t443, 0);
  cmsortLclo_i92 = lam_clo_t444;
  instr_clo(&lam_clo_t452, &lam_fun_t451, 0);
  mkListUclo_i93 = lam_clo_t452;
  instr_clo(&lam_clo_t460, &lam_fun_t459, 0);
  mkListLclo_i94 = lam_clo_t460;
  call_ret_t461 = mkListU_i57((tll_ptr)6000);
  test_v14415 = call_ret_t461;
  call_ret_t462 = cmsortU_i55(test_v14415);
  instr_app(&app_ret_t463, call_ret_t462, 0);
  instr_free_clo(call_ret_t462);
  sorted_v14416 = app_ret_t463;
  return 0;
}

