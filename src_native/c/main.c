#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v10924, tll_ptr b2_v10925);
tll_ptr orb_i2(tll_ptr b1_v10929, tll_ptr b2_v10930);
tll_ptr notb_i3(tll_ptr b_v10934);
tll_ptr lten_i4(tll_ptr x_v10936, tll_ptr y_v10937);
tll_ptr gten_i5(tll_ptr x_v10941, tll_ptr y_v10942);
tll_ptr ltn_i6(tll_ptr x_v10946, tll_ptr y_v10947);
tll_ptr gtn_i7(tll_ptr x_v10951, tll_ptr y_v10952);
tll_ptr eqn_i8(tll_ptr x_v10956, tll_ptr y_v10957);
tll_ptr pred_i9(tll_ptr x_v10961);
tll_ptr addn_i10(tll_ptr x_v10963, tll_ptr y_v10964);
tll_ptr subn_i11(tll_ptr x_v10968, tll_ptr y_v10969);
tll_ptr muln_i12(tll_ptr x_v10973, tll_ptr y_v10974);
tll_ptr divn_i13(tll_ptr x_v10978, tll_ptr y_v10979);
tll_ptr modn_i14(tll_ptr x_v10983, tll_ptr y_v10984);
tll_ptr cats_i15(tll_ptr s1_v10988, tll_ptr s2_v10989);
tll_ptr strlen_i16(tll_ptr s_v10995);
tll_ptr lenUU_i39(tll_ptr A_v10999, tll_ptr xs_v11000);
tll_ptr lenUL_i38(tll_ptr A_v11008, tll_ptr xs_v11009);
tll_ptr lenLL_i36(tll_ptr A_v11017, tll_ptr xs_v11018);
tll_ptr appendUU_i43(tll_ptr A_v11026, tll_ptr xs_v11027, tll_ptr ys_v11028);
tll_ptr appendUL_i42(tll_ptr A_v11037, tll_ptr xs_v11038, tll_ptr ys_v11039);
tll_ptr appendLL_i40(tll_ptr A_v11048, tll_ptr xs_v11049, tll_ptr ys_v11050);
tll_ptr readline_i25(tll_ptr __v11059);
tll_ptr print_i26(tll_ptr s_v11074);
tll_ptr prerr_i27(tll_ptr s_v11085);
tll_ptr splitU_i45(tll_ptr zs_v11096);
tll_ptr splitL_i44(tll_ptr zs_v11105);
tll_ptr mergeU_i47(tll_ptr xs_v11114, tll_ptr ys_v11115);
tll_ptr mergeL_i46(tll_ptr xs_v11123, tll_ptr ys_v11124);
tll_ptr msortU_i49(tll_ptr zs_v11132);
tll_ptr msortL_i48(tll_ptr zs_v11141);
tll_ptr cmsort_workerU_i53(tll_ptr n_v11150, tll_ptr zs_v11151, tll_ptr c_v11152);
tll_ptr cmsort_workerL_i52(tll_ptr n_v11167, tll_ptr zs_v11168, tll_ptr c_v11169);
tll_ptr cmsortU_i55(tll_ptr zs0_v11184);
tll_ptr cmsortL_i54(tll_ptr zs0_v11199);
tll_ptr mkListU_i57(tll_ptr n_v11214);
tll_ptr mkListL_i56(tll_ptr n_v11216);

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

tll_ptr andb_i1(tll_ptr b1_v10924, tll_ptr b2_v10925) {
  tll_ptr ifte_ret_t1;
  if (b1_v10924) {
    ifte_ret_t1 = b2_v10925;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v10928, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v10928);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v10926, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v10926);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v10929, tll_ptr b2_v10930) {
  tll_ptr ifte_ret_t7;
  if (b1_v10929) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v10930;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v10933, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v10933);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v10931, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v10931);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v10934) {
  tll_ptr ifte_ret_t13;
  if (b_v10934) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v10935, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v10935);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v10936, tll_ptr y_v10937) {
  tll_ptr add_ret_t18; tll_ptr add_ret_t19; tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  if (x_v10936) {
    if (y_v10937) {
      add_ret_t18 = x_v10936 - 1;
      add_ret_t19 = y_v10937 - 1;
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

tll_ptr lam_fun_t23(tll_ptr y_v10940, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v10940);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v10938, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v10938);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v10941, tll_ptr y_v10942) {
  tll_ptr add_ret_t28; tll_ptr add_ret_t29; tll_ptr call_ret_t27;
  tll_ptr ifte_ret_t30; tll_ptr ifte_ret_t31; tll_ptr ifte_ret_t32;
  if (x_v10941) {
    if (y_v10942) {
      add_ret_t28 = x_v10941 - 1;
      add_ret_t29 = y_v10942 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v10942) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v10945, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v10945);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v10943, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v10943);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v10946, tll_ptr y_v10947) {
  tll_ptr add_ret_t39; tll_ptr add_ret_t40; tll_ptr call_ret_t38;
  tll_ptr ifte_ret_t41; tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t43;
  if (x_v10946) {
    if (y_v10947) {
      add_ret_t39 = x_v10946 - 1;
      add_ret_t40 = y_v10947 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v10947) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v10950, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v10950);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v10948, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v10948);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v10951, tll_ptr y_v10952) {
  tll_ptr add_ret_t50; tll_ptr add_ret_t51; tll_ptr call_ret_t49;
  tll_ptr ifte_ret_t52; tll_ptr ifte_ret_t53;
  if (x_v10951) {
    if (y_v10952) {
      add_ret_t50 = x_v10951 - 1;
      add_ret_t51 = y_v10952 - 1;
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

tll_ptr lam_fun_t55(tll_ptr y_v10955, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v10955);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v10953, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v10953);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v10956, tll_ptr y_v10957) {
  tll_ptr add_ret_t60; tll_ptr add_ret_t61; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t62; tll_ptr ifte_ret_t63; tll_ptr ifte_ret_t64;
  if (x_v10956) {
    if (y_v10957) {
      add_ret_t60 = x_v10956 - 1;
      add_ret_t61 = y_v10957 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v10957) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v10960, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v10960);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v10958, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v10958);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v10961) {
  tll_ptr add_ret_t70; tll_ptr ifte_ret_t71;
  if (x_v10961) {
    add_ret_t70 = x_v10961 - 1;
    ifte_ret_t71 = add_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v10962, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v10962);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v10963, tll_ptr y_v10964) {
  tll_ptr add_ret_t76; tll_ptr add_ret_t77; tll_ptr call_ret_t75;
  tll_ptr ifte_ret_t78;
  if (x_v10963) {
    add_ret_t76 = x_v10963 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v10964);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v10964;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v10967, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v10967);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v10965, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v10965);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v10968, tll_ptr y_v10969) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v10969) {
    call_ret_t85 = pred_i9(x_v10968);
    add_ret_t86 = y_v10969 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v10968;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v10972, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v10972);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v10970, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v10970);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v10973, tll_ptr y_v10974) {
  tll_ptr add_ret_t95; tll_ptr call_ret_t93; tll_ptr call_ret_t94;
  tll_ptr ifte_ret_t96;
  if (x_v10973) {
    add_ret_t95 = x_v10973 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v10974);
    call_ret_t93 = addn_i10(y_v10974, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v10977, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v10977);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v10975, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v10975);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v10978, tll_ptr y_v10979) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v10978, y_v10979);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v10978, y_v10979);
    call_ret_t103 = divn_i13(call_ret_t104, y_v10979);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v10982, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v10982);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v10980, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v10980);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v10983, tll_ptr y_v10984) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v10983, y_v10984);
  call_ret_t113 = muln_i12(call_ret_t114, y_v10984);
  call_ret_t112 = subn_i11(x_v10983, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v10987, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v10987);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v10985, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v10985);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v10988, tll_ptr s2_v10989) {
  tll_ptr String_t122; tll_ptr c_v10990; tll_ptr call_ret_t121;
  tll_ptr s1_v10991; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v10988)->tag) {
    case 2:
      switch_ret_t120 = s2_v10989;
      break;
    case 3:
      c_v10990 = ((tll_node)s1_v10988)->data[0];
      s1_v10991 = ((tll_node)s1_v10988)->data[1];
      call_ret_t121 = cats_i15(s1_v10991, s2_v10989);
      instr_struct(&String_t122, 3, 2, c_v10990, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v10994, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v10994);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v10992, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v10992);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v10995) {
  tll_ptr __v10996; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v10997; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v10995)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v10996 = ((tll_node)s_v10995)->data[0];
      s_v10997 = ((tll_node)s_v10995)->data[1];
      call_ret_t129 = strlen_i16(s_v10997);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v10998, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v10998);
  return call_ret_t131;
}

tll_ptr lenUU_i39(tll_ptr A_v10999, tll_ptr xs_v11000) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v11003; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v11001; tll_ptr xs_v11002; tll_ptr xs_v11004;
  switch(((tll_node)xs_v11000)->tag) {
    case 12:
      instr_struct(&nilUU_t135, 12, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 13:
      x_v11001 = ((tll_node)xs_v11000)->data[0];
      xs_v11002 = ((tll_node)xs_v11000)->data[1];
      call_ret_t137 = lenUU_i39(0, xs_v11002);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v11003 = ((tll_node)call_ret_t137)->data[0];
          xs_v11004 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v11003 + 1;
          instr_struct(&consUU_t140, 13, 2, x_v11001, xs_v11004);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v11007, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i39(env[0], xs_v11007);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v11005, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v11005);
  return lam_clo_t144;
}

tll_ptr lenUL_i38(tll_ptr A_v11008, tll_ptr xs_v11009) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v11012; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v11010; tll_ptr xs_v11011; tll_ptr xs_v11013;
  switch(((tll_node)xs_v11009)->tag) {
    case 10:
      instr_free_struct(xs_v11009);
      instr_struct(&nilUL_t148, 10, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 11:
      x_v11010 = ((tll_node)xs_v11009)->data[0];
      xs_v11011 = ((tll_node)xs_v11009)->data[1];
      instr_free_struct(xs_v11009);
      call_ret_t150 = lenUL_i38(0, xs_v11011);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v11012 = ((tll_node)call_ret_t150)->data[0];
          xs_v11013 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v11012 + 1;
          instr_struct(&consUL_t153, 11, 2, x_v11010, xs_v11013);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v11016, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i38(env[0], xs_v11016);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v11014, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v11014);
  return lam_clo_t157;
}

tll_ptr lenLL_i36(tll_ptr A_v11017, tll_ptr xs_v11018) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v11021; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v11019; tll_ptr xs_v11020; tll_ptr xs_v11022;
  switch(((tll_node)xs_v11018)->tag) {
    case 6:
      instr_free_struct(xs_v11018);
      instr_struct(&nilLL_t161, 6, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 7:
      x_v11019 = ((tll_node)xs_v11018)->data[0];
      xs_v11020 = ((tll_node)xs_v11018)->data[1];
      instr_free_struct(xs_v11018);
      call_ret_t163 = lenLL_i36(0, xs_v11020);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v11021 = ((tll_node)call_ret_t163)->data[0];
          xs_v11022 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v11021 + 1;
          instr_struct(&consLL_t166, 7, 2, x_v11019, xs_v11022);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v11025, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i36(env[0], xs_v11025);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v11023, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v11023);
  return lam_clo_t170;
}

tll_ptr appendUU_i43(tll_ptr A_v11026, tll_ptr xs_v11027, tll_ptr ys_v11028) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v11029; tll_ptr xs_v11030;
  switch(((tll_node)xs_v11027)->tag) {
    case 12:
      switch_ret_t173 = ys_v11028;
      break;
    case 13:
      x_v11029 = ((tll_node)xs_v11027)->data[0];
      xs_v11030 = ((tll_node)xs_v11027)->data[1];
      call_ret_t174 = appendUU_i43(0, xs_v11030, ys_v11028);
      instr_struct(&consUU_t175, 13, 2, x_v11029, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v11036, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i43(env[1], env[0], ys_v11036);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v11034, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v11034, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v11031, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v11031);
  return lam_clo_t180;
}

tll_ptr appendUL_i42(tll_ptr A_v11037, tll_ptr xs_v11038, tll_ptr ys_v11039) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v11040; tll_ptr xs_v11041;
  switch(((tll_node)xs_v11038)->tag) {
    case 10:
      instr_free_struct(xs_v11038);
      switch_ret_t183 = ys_v11039;
      break;
    case 11:
      x_v11040 = ((tll_node)xs_v11038)->data[0];
      xs_v11041 = ((tll_node)xs_v11038)->data[1];
      instr_free_struct(xs_v11038);
      call_ret_t184 = appendUL_i42(0, xs_v11041, ys_v11039);
      instr_struct(&consUL_t185, 11, 2, x_v11040, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v11047, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i42(env[1], env[0], ys_v11047);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v11045, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v11045, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v11042, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v11042);
  return lam_clo_t190;
}

tll_ptr appendLL_i40(tll_ptr A_v11048, tll_ptr xs_v11049, tll_ptr ys_v11050) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v11051; tll_ptr xs_v11052;
  switch(((tll_node)xs_v11049)->tag) {
    case 6:
      instr_free_struct(xs_v11049);
      switch_ret_t193 = ys_v11050;
      break;
    case 7:
      x_v11051 = ((tll_node)xs_v11049)->data[0];
      xs_v11052 = ((tll_node)xs_v11049)->data[1];
      instr_free_struct(xs_v11049);
      call_ret_t194 = appendLL_i40(0, xs_v11052, ys_v11050);
      instr_struct(&consLL_t195, 7, 2, x_v11051, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v11058, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i40(env[1], env[0], ys_v11058);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v11056, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v11056, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v11053, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v11053);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v11060, tll_env env) {
  tll_ptr __v11069; tll_ptr ch_v11067; tll_ptr ch_v11068; tll_ptr ch_v11071;
  tll_ptr ch_v11072; tll_ptr prim_ch_t203; tll_ptr recv_msg_t205;
  tll_ptr s_v11070; tll_ptr send_ch_t204; tll_ptr send_ch_t207;
  tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v11067 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v11067, (tll_ptr)1);
  ch_v11068 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v11068);
  __v11069 = recv_msg_t205;
  switch(((tll_node)__v11069)->tag) {
    case 0:
      s_v11070 = ((tll_node)__v11069)->data[0];
      ch_v11071 = ((tll_node)__v11069)->data[1];
      instr_free_struct(__v11069);
      instr_send(&send_ch_t207, ch_v11071, (tll_ptr)0);
      ch_v11072 = send_ch_t207;
      switch_ret_t206 = s_v11070;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v11059) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v11073, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v11073);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v11075, tll_env env) {
  tll_ptr ch_v11080; tll_ptr ch_v11081; tll_ptr ch_v11082; tll_ptr ch_v11083;
  tll_ptr prim_ch_t213; tll_ptr send_ch_t214; tll_ptr send_ch_t215;
  tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v11080 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v11080, (tll_ptr)1);
  ch_v11081 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v11081, env[0]);
  ch_v11082 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v11082, (tll_ptr)0);
  ch_v11083 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v11074) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v11074);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v11084, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v11084);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v11086, tll_env env) {
  tll_ptr ch_v11091; tll_ptr ch_v11092; tll_ptr ch_v11093; tll_ptr ch_v11094;
  tll_ptr prim_ch_t222; tll_ptr send_ch_t223; tll_ptr send_ch_t224;
  tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v11091 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v11091, (tll_ptr)1);
  ch_v11092 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v11092, env[0]);
  ch_v11093 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v11093, (tll_ptr)0);
  ch_v11094 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v11085) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v11085);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v11095, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v11095);
  return call_ret_t228;
}

tll_ptr splitU_i45(tll_ptr zs_v11096) {
  tll_ptr __v11101; tll_ptr call_ret_t240; tll_ptr consUU_t237;
  tll_ptr consUU_t242; tll_ptr consUU_t243; tll_ptr nilUU_t232;
  tll_ptr nilUU_t233; tll_ptr nilUU_t236; tll_ptr nilUU_t238;
  tll_ptr pair_struct_t234; tll_ptr pair_struct_t239;
  tll_ptr pair_struct_t244; tll_ptr switch_ret_t231; tll_ptr switch_ret_t235;
  tll_ptr switch_ret_t241; tll_ptr x_v11097; tll_ptr xs_v11102;
  tll_ptr y_v11099; tll_ptr ys_v11103; tll_ptr zs_v11098; tll_ptr zs_v11100;
  switch(((tll_node)zs_v11096)->tag) {
    case 12:
      instr_struct(&nilUU_t232, 12, 0);
      instr_struct(&nilUU_t233, 12, 0);
      instr_struct(&pair_struct_t234, 0, 2, nilUU_t232, nilUU_t233);
      switch_ret_t231 = pair_struct_t234;
      break;
    case 13:
      x_v11097 = ((tll_node)zs_v11096)->data[0];
      zs_v11098 = ((tll_node)zs_v11096)->data[1];
      switch(((tll_node)zs_v11098)->tag) {
        case 12:
          instr_struct(&nilUU_t236, 12, 0);
          instr_struct(&consUU_t237, 13, 2, x_v11097, nilUU_t236);
          instr_struct(&nilUU_t238, 12, 0);
          instr_struct(&pair_struct_t239, 0, 2, consUU_t237, nilUU_t238);
          switch_ret_t235 = pair_struct_t239;
          break;
        case 13:
          y_v11099 = ((tll_node)zs_v11098)->data[0];
          zs_v11100 = ((tll_node)zs_v11098)->data[1];
          call_ret_t240 = splitU_i45(zs_v11100);
          __v11101 = call_ret_t240;
          switch(((tll_node)__v11101)->tag) {
            case 0:
              xs_v11102 = ((tll_node)__v11101)->data[0];
              ys_v11103 = ((tll_node)__v11101)->data[1];
              instr_free_struct(__v11101);
              instr_struct(&consUU_t242, 13, 2, x_v11097, xs_v11102);
              instr_struct(&consUU_t243, 13, 2, y_v11099, ys_v11103);
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

tll_ptr lam_fun_t246(tll_ptr zs_v11104, tll_env env) {
  tll_ptr call_ret_t245;
  call_ret_t245 = splitU_i45(zs_v11104);
  return call_ret_t245;
}

tll_ptr splitL_i44(tll_ptr zs_v11105) {
  tll_ptr __v11110; tll_ptr call_ret_t257; tll_ptr consUL_t254;
  tll_ptr consUL_t259; tll_ptr consUL_t260; tll_ptr nilUL_t249;
  tll_ptr nilUL_t250; tll_ptr nilUL_t253; tll_ptr nilUL_t255;
  tll_ptr pair_struct_t251; tll_ptr pair_struct_t256;
  tll_ptr pair_struct_t261; tll_ptr switch_ret_t248; tll_ptr switch_ret_t252;
  tll_ptr switch_ret_t258; tll_ptr x_v11106; tll_ptr xs_v11111;
  tll_ptr y_v11108; tll_ptr ys_v11112; tll_ptr zs_v11107; tll_ptr zs_v11109;
  switch(((tll_node)zs_v11105)->tag) {
    case 10:
      instr_free_struct(zs_v11105);
      instr_struct(&nilUL_t249, 10, 0);
      instr_struct(&nilUL_t250, 10, 0);
      instr_struct(&pair_struct_t251, 0, 2, nilUL_t249, nilUL_t250);
      switch_ret_t248 = pair_struct_t251;
      break;
    case 11:
      x_v11106 = ((tll_node)zs_v11105)->data[0];
      zs_v11107 = ((tll_node)zs_v11105)->data[1];
      instr_free_struct(zs_v11105);
      switch(((tll_node)zs_v11107)->tag) {
        case 10:
          instr_free_struct(zs_v11107);
          instr_struct(&nilUL_t253, 10, 0);
          instr_struct(&consUL_t254, 11, 2, x_v11106, nilUL_t253);
          instr_struct(&nilUL_t255, 10, 0);
          instr_struct(&pair_struct_t256, 0, 2, consUL_t254, nilUL_t255);
          switch_ret_t252 = pair_struct_t256;
          break;
        case 11:
          y_v11108 = ((tll_node)zs_v11107)->data[0];
          zs_v11109 = ((tll_node)zs_v11107)->data[1];
          instr_free_struct(zs_v11107);
          call_ret_t257 = splitL_i44(zs_v11109);
          __v11110 = call_ret_t257;
          switch(((tll_node)__v11110)->tag) {
            case 0:
              xs_v11111 = ((tll_node)__v11110)->data[0];
              ys_v11112 = ((tll_node)__v11110)->data[1];
              instr_free_struct(__v11110);
              instr_struct(&consUL_t259, 11, 2, x_v11106, xs_v11111);
              instr_struct(&consUL_t260, 11, 2, y_v11108, ys_v11112);
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

tll_ptr lam_fun_t263(tll_ptr zs_v11113, tll_env env) {
  tll_ptr call_ret_t262;
  call_ret_t262 = splitL_i44(zs_v11113);
  return call_ret_t262;
}

tll_ptr mergeU_i47(tll_ptr xs_v11114, tll_ptr ys_v11115) {
  tll_ptr call_ret_t268; tll_ptr call_ret_t269; tll_ptr call_ret_t272;
  tll_ptr consUU_t267; tll_ptr consUU_t270; tll_ptr consUU_t271;
  tll_ptr consUU_t273; tll_ptr consUU_t274; tll_ptr ifte_ret_t275;
  tll_ptr switch_ret_t265; tll_ptr switch_ret_t266; tll_ptr x_v11116;
  tll_ptr xs0_v11117; tll_ptr y_v11118; tll_ptr ys0_v11119;
  switch(((tll_node)xs_v11114)->tag) {
    case 12:
      switch_ret_t265 = ys_v11115;
      break;
    case 13:
      x_v11116 = ((tll_node)xs_v11114)->data[0];
      xs0_v11117 = ((tll_node)xs_v11114)->data[1];
      switch(((tll_node)ys_v11115)->tag) {
        case 12:
          instr_struct(&consUU_t267, 13, 2, x_v11116, xs0_v11117);
          switch_ret_t266 = consUU_t267;
          break;
        case 13:
          y_v11118 = ((tll_node)ys_v11115)->data[0];
          ys0_v11119 = ((tll_node)ys_v11115)->data[1];
          call_ret_t268 = lten_i4(x_v11116, y_v11118);
          if (call_ret_t268) {
            instr_struct(&consUU_t270, 13, 2, y_v11118, ys0_v11119);
            call_ret_t269 = mergeU_i47(xs0_v11117, consUU_t270);
            instr_struct(&consUU_t271, 13, 2, x_v11116, call_ret_t269);
            ifte_ret_t275 = consUU_t271;
          }
          else {
            instr_struct(&consUU_t273, 13, 2, x_v11116, xs0_v11117);
            call_ret_t272 = mergeU_i47(consUU_t273, ys0_v11119);
            instr_struct(&consUU_t274, 13, 2, y_v11118, call_ret_t272);
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

tll_ptr lam_fun_t277(tll_ptr ys_v11122, tll_env env) {
  tll_ptr call_ret_t276;
  call_ret_t276 = mergeU_i47(env[0], ys_v11122);
  return call_ret_t276;
}

tll_ptr lam_fun_t279(tll_ptr xs_v11120, tll_env env) {
  tll_ptr lam_clo_t278;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 1, xs_v11120);
  return lam_clo_t278;
}

tll_ptr mergeL_i46(tll_ptr xs_v11123, tll_ptr ys_v11124) {
  tll_ptr call_ret_t284; tll_ptr call_ret_t285; tll_ptr call_ret_t288;
  tll_ptr consUL_t283; tll_ptr consUL_t286; tll_ptr consUL_t287;
  tll_ptr consUL_t289; tll_ptr consUL_t290; tll_ptr ifte_ret_t291;
  tll_ptr switch_ret_t281; tll_ptr switch_ret_t282; tll_ptr x_v11125;
  tll_ptr xs0_v11126; tll_ptr y_v11127; tll_ptr ys0_v11128;
  switch(((tll_node)xs_v11123)->tag) {
    case 10:
      instr_free_struct(xs_v11123);
      switch_ret_t281 = ys_v11124;
      break;
    case 11:
      x_v11125 = ((tll_node)xs_v11123)->data[0];
      xs0_v11126 = ((tll_node)xs_v11123)->data[1];
      instr_free_struct(xs_v11123);
      switch(((tll_node)ys_v11124)->tag) {
        case 10:
          instr_free_struct(ys_v11124);
          instr_struct(&consUL_t283, 11, 2, x_v11125, xs0_v11126);
          switch_ret_t282 = consUL_t283;
          break;
        case 11:
          y_v11127 = ((tll_node)ys_v11124)->data[0];
          ys0_v11128 = ((tll_node)ys_v11124)->data[1];
          instr_free_struct(ys_v11124);
          call_ret_t284 = lten_i4(x_v11125, y_v11127);
          if (call_ret_t284) {
            instr_struct(&consUL_t286, 11, 2, y_v11127, ys0_v11128);
            call_ret_t285 = mergeL_i46(xs0_v11126, consUL_t286);
            instr_struct(&consUL_t287, 11, 2, x_v11125, call_ret_t285);
            ifte_ret_t291 = consUL_t287;
          }
          else {
            instr_struct(&consUL_t289, 11, 2, x_v11125, xs0_v11126);
            call_ret_t288 = mergeL_i46(consUL_t289, ys0_v11128);
            instr_struct(&consUL_t290, 11, 2, y_v11127, call_ret_t288);
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

tll_ptr lam_fun_t293(tll_ptr ys_v11131, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = mergeL_i46(env[0], ys_v11131);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v11129, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 1, xs_v11129);
  return lam_clo_t294;
}

tll_ptr msortU_i49(tll_ptr zs_v11132) {
  tll_ptr __v11137; tll_ptr call_ret_t302; tll_ptr call_ret_t306;
  tll_ptr call_ret_t307; tll_ptr call_ret_t308; tll_ptr consUU_t301;
  tll_ptr consUU_t303; tll_ptr consUU_t304; tll_ptr nilUU_t298;
  tll_ptr nilUU_t300; tll_ptr switch_ret_t297; tll_ptr switch_ret_t299;
  tll_ptr switch_ret_t305; tll_ptr x_v11133; tll_ptr xs_v11138;
  tll_ptr y_v11135; tll_ptr ys_v11139; tll_ptr zs_v11134; tll_ptr zs_v11136;
  switch(((tll_node)zs_v11132)->tag) {
    case 12:
      instr_struct(&nilUU_t298, 12, 0);
      switch_ret_t297 = nilUU_t298;
      break;
    case 13:
      x_v11133 = ((tll_node)zs_v11132)->data[0];
      zs_v11134 = ((tll_node)zs_v11132)->data[1];
      switch(((tll_node)zs_v11134)->tag) {
        case 12:
          instr_struct(&nilUU_t300, 12, 0);
          instr_struct(&consUU_t301, 13, 2, x_v11133, nilUU_t300);
          switch_ret_t299 = consUU_t301;
          break;
        case 13:
          y_v11135 = ((tll_node)zs_v11134)->data[0];
          zs_v11136 = ((tll_node)zs_v11134)->data[1];
          instr_struct(&consUU_t303, 13, 2, y_v11135, zs_v11136);
          instr_struct(&consUU_t304, 13, 2, x_v11133, consUU_t303);
          call_ret_t302 = splitU_i45(consUU_t304);
          __v11137 = call_ret_t302;
          switch(((tll_node)__v11137)->tag) {
            case 0:
              xs_v11138 = ((tll_node)__v11137)->data[0];
              ys_v11139 = ((tll_node)__v11137)->data[1];
              instr_free_struct(__v11137);
              call_ret_t307 = msortU_i49(xs_v11138);
              call_ret_t308 = msortU_i49(ys_v11139);
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

tll_ptr lam_fun_t310(tll_ptr zs_v11140, tll_env env) {
  tll_ptr call_ret_t309;
  call_ret_t309 = msortU_i49(zs_v11140);
  return call_ret_t309;
}

tll_ptr msortL_i48(tll_ptr zs_v11141) {
  tll_ptr __v11146; tll_ptr call_ret_t317; tll_ptr call_ret_t321;
  tll_ptr call_ret_t322; tll_ptr call_ret_t323; tll_ptr consUL_t316;
  tll_ptr consUL_t318; tll_ptr consUL_t319; tll_ptr nilUL_t313;
  tll_ptr nilUL_t315; tll_ptr switch_ret_t312; tll_ptr switch_ret_t314;
  tll_ptr switch_ret_t320; tll_ptr x_v11142; tll_ptr xs_v11147;
  tll_ptr y_v11144; tll_ptr ys_v11148; tll_ptr zs_v11143; tll_ptr zs_v11145;
  switch(((tll_node)zs_v11141)->tag) {
    case 10:
      instr_free_struct(zs_v11141);
      instr_struct(&nilUL_t313, 10, 0);
      switch_ret_t312 = nilUL_t313;
      break;
    case 11:
      x_v11142 = ((tll_node)zs_v11141)->data[0];
      zs_v11143 = ((tll_node)zs_v11141)->data[1];
      instr_free_struct(zs_v11141);
      switch(((tll_node)zs_v11143)->tag) {
        case 10:
          instr_free_struct(zs_v11143);
          instr_struct(&nilUL_t315, 10, 0);
          instr_struct(&consUL_t316, 11, 2, x_v11142, nilUL_t315);
          switch_ret_t314 = consUL_t316;
          break;
        case 11:
          y_v11144 = ((tll_node)zs_v11143)->data[0];
          zs_v11145 = ((tll_node)zs_v11143)->data[1];
          instr_free_struct(zs_v11143);
          instr_struct(&consUL_t318, 11, 2, y_v11144, zs_v11145);
          instr_struct(&consUL_t319, 11, 2, x_v11142, consUL_t318);
          call_ret_t317 = splitL_i44(consUL_t319);
          __v11146 = call_ret_t317;
          switch(((tll_node)__v11146)->tag) {
            case 0:
              xs_v11147 = ((tll_node)__v11146)->data[0];
              ys_v11148 = ((tll_node)__v11146)->data[1];
              instr_free_struct(__v11146);
              call_ret_t322 = msortL_i48(xs_v11147);
              call_ret_t323 = msortL_i48(ys_v11148);
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

tll_ptr lam_fun_t325(tll_ptr zs_v11149, tll_env env) {
  tll_ptr call_ret_t324;
  call_ret_t324 = msortL_i48(zs_v11149);
  return call_ret_t324;
}

tll_ptr lam_fun_t328(tll_ptr __v11160, tll_env env) {
  tll_ptr send_ch_t327;
  instr_send(&send_ch_t327, env[1], env[0]);
  return send_ch_t327;
}

tll_ptr lam_fun_t330(tll_ptr x_v11158, tll_env env) {
  tll_ptr lam_clo_t329;
  instr_clo(&lam_clo_t329, &lam_fun_t328, 2, x_v11158, env[0]);
  return lam_clo_t329;
}

tll_ptr lam_fun_t335(tll_ptr __v11153, tll_env env) {
  tll_ptr app_ret_t333; tll_ptr app_ret_t334; tll_ptr c_v11157;
  tll_ptr call_ret_t332; tll_ptr lam_clo_t331;
  instr_clo(&lam_clo_t331, &lam_fun_t330, 1, env[0]);
  call_ret_t332 = msortU_i49(env[1]);
  instr_app(&app_ret_t333, lam_clo_t331, call_ret_t332);
  instr_free_clo(lam_clo_t331);
  instr_app(&app_ret_t334, app_ret_t333, 0);
  instr_free_clo(app_ret_t333);
  c_v11157 = app_ret_t334;
  return 0;
}

tll_ptr cmsort_workerU_i53(tll_ptr n_v11150, tll_ptr zs_v11151, tll_ptr c_v11152) {
  tll_ptr lam_clo_t336;
  instr_clo(&lam_clo_t336, &lam_fun_t335, 2, c_v11152, zs_v11151);
  return lam_clo_t336;
}

tll_ptr lam_fun_t338(tll_ptr c_v11166, tll_env env) {
  tll_ptr call_ret_t337;
  call_ret_t337 = cmsort_workerU_i53(env[1], env[0], c_v11166);
  return call_ret_t337;
}

tll_ptr lam_fun_t340(tll_ptr zs_v11164, tll_env env) {
  tll_ptr lam_clo_t339;
  instr_clo(&lam_clo_t339, &lam_fun_t338, 2, zs_v11164, env[0]);
  return lam_clo_t339;
}

tll_ptr lam_fun_t342(tll_ptr n_v11161, tll_env env) {
  tll_ptr lam_clo_t341;
  instr_clo(&lam_clo_t341, &lam_fun_t340, 1, n_v11161);
  return lam_clo_t341;
}

tll_ptr lam_fun_t345(tll_ptr __v11177, tll_env env) {
  tll_ptr send_ch_t344;
  instr_send(&send_ch_t344, env[1], env[0]);
  return send_ch_t344;
}

tll_ptr lam_fun_t347(tll_ptr x_v11175, tll_env env) {
  tll_ptr lam_clo_t346;
  instr_clo(&lam_clo_t346, &lam_fun_t345, 2, x_v11175, env[0]);
  return lam_clo_t346;
}

tll_ptr lam_fun_t352(tll_ptr __v11170, tll_env env) {
  tll_ptr app_ret_t350; tll_ptr app_ret_t351; tll_ptr c_v11174;
  tll_ptr call_ret_t349; tll_ptr lam_clo_t348;
  instr_clo(&lam_clo_t348, &lam_fun_t347, 1, env[0]);
  call_ret_t349 = msortL_i48(env[1]);
  instr_app(&app_ret_t350, lam_clo_t348, call_ret_t349);
  instr_free_clo(lam_clo_t348);
  instr_app(&app_ret_t351, app_ret_t350, 0);
  instr_free_clo(app_ret_t350);
  c_v11174 = app_ret_t351;
  return 0;
}

tll_ptr cmsort_workerL_i52(tll_ptr n_v11167, tll_ptr zs_v11168, tll_ptr c_v11169) {
  tll_ptr lam_clo_t353;
  instr_clo(&lam_clo_t353, &lam_fun_t352, 2, c_v11169, zs_v11168);
  return lam_clo_t353;
}

tll_ptr lam_fun_t355(tll_ptr c_v11183, tll_env env) {
  tll_ptr call_ret_t354;
  call_ret_t354 = cmsort_workerL_i52(env[1], env[0], c_v11183);
  return call_ret_t354;
}

tll_ptr lam_fun_t357(tll_ptr zs_v11181, tll_env env) {
  tll_ptr lam_clo_t356;
  instr_clo(&lam_clo_t356, &lam_fun_t355, 2, zs_v11181, env[0]);
  return lam_clo_t356;
}

tll_ptr lam_fun_t359(tll_ptr n_v11178, tll_env env) {
  tll_ptr lam_clo_t358;
  instr_clo(&lam_clo_t358, &lam_fun_t357, 1, n_v11178);
  return lam_clo_t358;
}

tll_ptr fork_fun_t363(tll_env env) {
  tll_ptr app_ret_t362; tll_ptr call_ret_t361; tll_ptr fork_ret_t365;
  call_ret_t361 = cmsort_workerU_i53((tll_ptr)0, env[1], env[0]);
  instr_app(&app_ret_t362, call_ret_t361, 0);
  instr_free_clo(call_ret_t361);
  fork_ret_t365 = app_ret_t362;
  instr_free_thread(env);
  return fork_ret_t365;
}

tll_ptr lam_fun_t369(tll_ptr __v11185, tll_env env) {
  tll_ptr __v11194; tll_ptr __v11197; tll_ptr c_v11192; tll_ptr c_v11196;
  tll_ptr close_tmp_t368; tll_ptr fork_ch_t364; tll_ptr recv_msg_t366;
  tll_ptr switch_ret_t367; tll_ptr zs1_v11195;
  instr_fork(&fork_ch_t364, &fork_fun_t363, 1, env[0]);
  c_v11192 = fork_ch_t364;
  instr_recv(&recv_msg_t366, c_v11192);
  __v11194 = recv_msg_t366;
  switch(((tll_node)__v11194)->tag) {
    case 0:
      zs1_v11195 = ((tll_node)__v11194)->data[0];
      c_v11196 = ((tll_node)__v11194)->data[1];
      instr_free_struct(__v11194);
      instr_close(&close_tmp_t368, c_v11196);
      __v11197 = close_tmp_t368;
      switch_ret_t367 = zs1_v11195;
      break;
  }
  return switch_ret_t367;
}

tll_ptr cmsortU_i55(tll_ptr zs0_v11184) {
  tll_ptr lam_clo_t370;
  instr_clo(&lam_clo_t370, &lam_fun_t369, 1, zs0_v11184);
  return lam_clo_t370;
}

tll_ptr lam_fun_t372(tll_ptr zs0_v11198, tll_env env) {
  tll_ptr call_ret_t371;
  call_ret_t371 = cmsortU_i55(zs0_v11198);
  return call_ret_t371;
}

tll_ptr fork_fun_t376(tll_env env) {
  tll_ptr app_ret_t375; tll_ptr call_ret_t374; tll_ptr fork_ret_t378;
  call_ret_t374 = cmsort_workerL_i52((tll_ptr)0, env[1], env[0]);
  instr_app(&app_ret_t375, call_ret_t374, 0);
  instr_free_clo(call_ret_t374);
  fork_ret_t378 = app_ret_t375;
  instr_free_thread(env);
  return fork_ret_t378;
}

tll_ptr lam_fun_t382(tll_ptr __v11200, tll_env env) {
  tll_ptr __v11209; tll_ptr __v11212; tll_ptr c_v11207; tll_ptr c_v11211;
  tll_ptr close_tmp_t381; tll_ptr fork_ch_t377; tll_ptr recv_msg_t379;
  tll_ptr switch_ret_t380; tll_ptr zs1_v11210;
  instr_fork(&fork_ch_t377, &fork_fun_t376, 1, env[0]);
  c_v11207 = fork_ch_t377;
  instr_recv(&recv_msg_t379, c_v11207);
  __v11209 = recv_msg_t379;
  switch(((tll_node)__v11209)->tag) {
    case 0:
      zs1_v11210 = ((tll_node)__v11209)->data[0];
      c_v11211 = ((tll_node)__v11209)->data[1];
      instr_free_struct(__v11209);
      instr_close(&close_tmp_t381, c_v11211);
      __v11212 = close_tmp_t381;
      switch_ret_t380 = zs1_v11210;
      break;
  }
  return switch_ret_t380;
}

tll_ptr cmsortL_i54(tll_ptr zs0_v11199) {
  tll_ptr lam_clo_t383;
  instr_clo(&lam_clo_t383, &lam_fun_t382, 1, zs0_v11199);
  return lam_clo_t383;
}

tll_ptr lam_fun_t385(tll_ptr zs0_v11213, tll_env env) {
  tll_ptr call_ret_t384;
  call_ret_t384 = cmsortL_i54(zs0_v11213);
  return call_ret_t384;
}

tll_ptr mkListU_i57(tll_ptr n_v11214) {
  tll_ptr add_ret_t388; tll_ptr call_ret_t387; tll_ptr consUU_t389;
  tll_ptr ifte_ret_t391; tll_ptr nilUU_t390;
  if (n_v11214) {
    add_ret_t388 = n_v11214 - 1;
    call_ret_t387 = mkListU_i57(add_ret_t388);
    instr_struct(&consUU_t389, 13, 2, n_v11214, call_ret_t387);
    ifte_ret_t391 = consUU_t389;
  }
  else {
    instr_struct(&nilUU_t390, 12, 0);
    ifte_ret_t391 = nilUU_t390;
  }
  return ifte_ret_t391;
}

tll_ptr lam_fun_t393(tll_ptr n_v11215, tll_env env) {
  tll_ptr call_ret_t392;
  call_ret_t392 = mkListU_i57(n_v11215);
  return call_ret_t392;
}

tll_ptr mkListL_i56(tll_ptr n_v11216) {
  tll_ptr add_ret_t396; tll_ptr call_ret_t395; tll_ptr consUL_t397;
  tll_ptr ifte_ret_t399; tll_ptr nilUL_t398;
  if (n_v11216) {
    add_ret_t396 = n_v11216 - 1;
    call_ret_t395 = mkListL_i56(add_ret_t396);
    instr_struct(&consUL_t397, 11, 2, n_v11216, call_ret_t395);
    ifte_ret_t399 = consUL_t397;
  }
  else {
    instr_struct(&nilUL_t398, 10, 0);
    ifte_ret_t399 = nilUL_t398;
  }
  return ifte_ret_t399;
}

tll_ptr lam_fun_t401(tll_ptr n_v11217, tll_env env) {
  tll_ptr call_ret_t400;
  call_ret_t400 = mkListL_i56(n_v11217);
  return call_ret_t400;
}

int main() {
  instr_init();
  tll_ptr app_ret_t405; tll_ptr call_ret_t403; tll_ptr call_ret_t404;
  tll_ptr lam_clo_t101; tll_ptr lam_clo_t111; tll_ptr lam_clo_t119;
  tll_ptr lam_clo_t12; tll_ptr lam_clo_t127; tll_ptr lam_clo_t133;
  tll_ptr lam_clo_t146; tll_ptr lam_clo_t159; tll_ptr lam_clo_t16;
  tll_ptr lam_clo_t172; tll_ptr lam_clo_t182; tll_ptr lam_clo_t192;
  tll_ptr lam_clo_t202; tll_ptr lam_clo_t212; tll_ptr lam_clo_t221;
  tll_ptr lam_clo_t230; tll_ptr lam_clo_t247; tll_ptr lam_clo_t26;
  tll_ptr lam_clo_t264; tll_ptr lam_clo_t280; tll_ptr lam_clo_t296;
  tll_ptr lam_clo_t311; tll_ptr lam_clo_t326; tll_ptr lam_clo_t343;
  tll_ptr lam_clo_t360; tll_ptr lam_clo_t37; tll_ptr lam_clo_t373;
  tll_ptr lam_clo_t386; tll_ptr lam_clo_t394; tll_ptr lam_clo_t402;
  tll_ptr lam_clo_t48; tll_ptr lam_clo_t58; tll_ptr lam_clo_t6;
  tll_ptr lam_clo_t69; tll_ptr lam_clo_t74; tll_ptr lam_clo_t83;
  tll_ptr lam_clo_t92; tll_ptr sorted_v11219; tll_ptr test_v11218;
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
  instr_clo(&lam_clo_t343, &lam_fun_t342, 0);
  cmsort_workerUclo_i89 = lam_clo_t343;
  instr_clo(&lam_clo_t360, &lam_fun_t359, 0);
  cmsort_workerLclo_i90 = lam_clo_t360;
  instr_clo(&lam_clo_t373, &lam_fun_t372, 0);
  cmsortUclo_i91 = lam_clo_t373;
  instr_clo(&lam_clo_t386, &lam_fun_t385, 0);
  cmsortLclo_i92 = lam_clo_t386;
  instr_clo(&lam_clo_t394, &lam_fun_t393, 0);
  mkListUclo_i93 = lam_clo_t394;
  instr_clo(&lam_clo_t402, &lam_fun_t401, 0);
  mkListLclo_i94 = lam_clo_t402;
  call_ret_t403 = mkListU_i57((tll_ptr)10000);
  test_v11218 = call_ret_t403;
  call_ret_t404 = cmsortU_i55(test_v11218);
  instr_app(&app_ret_t405, call_ret_t404, 0);
  instr_free_clo(call_ret_t404);
  sorted_v11219 = app_ret_t405;
  return 0;
}

