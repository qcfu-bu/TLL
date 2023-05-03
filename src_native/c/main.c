#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v23203, tll_ptr b2_v23204);
tll_ptr orb_i2(tll_ptr b1_v23208, tll_ptr b2_v23209);
tll_ptr notb_i3(tll_ptr b_v23213);
tll_ptr lten_i4(tll_ptr x_v23215, tll_ptr y_v23216);
tll_ptr gten_i5(tll_ptr x_v23220, tll_ptr y_v23221);
tll_ptr ltn_i6(tll_ptr x_v23225, tll_ptr y_v23226);
tll_ptr gtn_i7(tll_ptr x_v23230, tll_ptr y_v23231);
tll_ptr eqn_i8(tll_ptr x_v23235, tll_ptr y_v23236);
tll_ptr pred_i9(tll_ptr x_v23240);
tll_ptr addn_i10(tll_ptr x_v23242, tll_ptr y_v23243);
tll_ptr subn_i11(tll_ptr x_v23247, tll_ptr y_v23248);
tll_ptr muln_i12(tll_ptr x_v23252, tll_ptr y_v23253);
tll_ptr divn_i13(tll_ptr x_v23257, tll_ptr y_v23258);
tll_ptr modn_i14(tll_ptr x_v23262, tll_ptr y_v23263);
tll_ptr cats_i15(tll_ptr s1_v23267, tll_ptr s2_v23268);
tll_ptr strlen_i16(tll_ptr s_v23274);
tll_ptr lenUU_i44(tll_ptr A_v23278, tll_ptr xs_v23279);
tll_ptr lenUL_i43(tll_ptr A_v23287, tll_ptr xs_v23288);
tll_ptr lenLL_i41(tll_ptr A_v23296, tll_ptr xs_v23297);
tll_ptr appendUU_i48(tll_ptr A_v23305, tll_ptr xs_v23306, tll_ptr ys_v23307);
tll_ptr appendUL_i47(tll_ptr A_v23316, tll_ptr xs_v23317, tll_ptr ys_v23318);
tll_ptr appendLL_i45(tll_ptr A_v23327, tll_ptr xs_v23328, tll_ptr ys_v23329);
tll_ptr readline_i25(tll_ptr __v23338);
tll_ptr print_i26(tll_ptr s_v23353);
tll_ptr prerr_i27(tll_ptr s_v23364);
tll_ptr get_at_i29(tll_ptr A_v23375, tll_ptr n_v23376, tll_ptr xs_v23377, tll_ptr a_v23378);
tll_ptr string_of_digit_i30(tll_ptr n_v23393);
tll_ptr string_of_nat_i31(tll_ptr n_v23395);
tll_ptr powm_i33(tll_ptr a_v23399, tll_ptr b_v23400, tll_ptr m_v23401);
tll_ptr client_i38(tll_ptr ch_v23408);
tll_ptr server_i39(tll_ptr ch_v23459);

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

tll_ptr andb_i1(tll_ptr b1_v23203, tll_ptr b2_v23204) {
  tll_ptr ifte_ret_t1;
  if (b1_v23203) {
    ifte_ret_t1 = b2_v23204;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v23207, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v23207);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v23205, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v23205);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v23208, tll_ptr b2_v23209) {
  tll_ptr ifte_ret_t7;
  if (b1_v23208) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v23209;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v23212, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v23212);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v23210, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v23210);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v23213) {
  tll_ptr ifte_ret_t13;
  if (b_v23213) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v23214, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v23214);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v23215, tll_ptr y_v23216) {
  tll_ptr lten_ret_t17;
  instr_lten(&lten_ret_t17, x_v23215, y_v23216);
  return lten_ret_t17;
}

tll_ptr lam_fun_t19(tll_ptr y_v23219, tll_env env) {
  tll_ptr call_ret_t18;
  call_ret_t18 = lten_i4(env[0], y_v23219);
  return call_ret_t18;
}

tll_ptr lam_fun_t21(tll_ptr x_v23217, tll_env env) {
  tll_ptr lam_clo_t20;
  instr_clo(&lam_clo_t20, &lam_fun_t19, 1, x_v23217);
  return lam_clo_t20;
}

tll_ptr gten_i5(tll_ptr x_v23220, tll_ptr y_v23221) {
  tll_ptr gten_ret_t23;
  instr_gten(&gten_ret_t23, x_v23220, y_v23221);
  return gten_ret_t23;
}

tll_ptr lam_fun_t25(tll_ptr y_v23224, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = gten_i5(env[0], y_v23224);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr x_v23222, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, x_v23222);
  return lam_clo_t26;
}

tll_ptr ltn_i6(tll_ptr x_v23225, tll_ptr y_v23226) {
  tll_ptr ltn_ret_t29;
  instr_ltn(&ltn_ret_t29, x_v23225, y_v23226);
  return ltn_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v23229, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = ltn_i6(env[0], y_v23229);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v23227, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v23227);
  return lam_clo_t32;
}

tll_ptr gtn_i7(tll_ptr x_v23230, tll_ptr y_v23231) {
  tll_ptr gtn_ret_t35;
  instr_gtn(&gtn_ret_t35, x_v23230, y_v23231);
  return gtn_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v23234, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = gtn_i7(env[0], y_v23234);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v23232, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v23232);
  return lam_clo_t38;
}

tll_ptr eqn_i8(tll_ptr x_v23235, tll_ptr y_v23236) {
  tll_ptr eqn_ret_t41;
  instr_eqn(&eqn_ret_t41, x_v23235, y_v23236);
  return eqn_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v23239, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = eqn_i8(env[0], y_v23239);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v23237, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v23237);
  return lam_clo_t44;
}

tll_ptr pred_i9(tll_ptr x_v23240) {
  tll_ptr add_ret_t47; tll_ptr ifte_ret_t48;
  if (x_v23240) {
    add_ret_t47 = x_v23240 - 1;
    ifte_ret_t48 = add_ret_t47;
  }
  else {
    ifte_ret_t48 = (tll_ptr)0;
  }
  return ifte_ret_t48;
}

tll_ptr lam_fun_t50(tll_ptr x_v23241, tll_env env) {
  tll_ptr call_ret_t49;
  call_ret_t49 = pred_i9(x_v23241);
  return call_ret_t49;
}

tll_ptr addn_i10(tll_ptr x_v23242, tll_ptr y_v23243) {
  tll_ptr addn_ret_t52;
  instr_addn(&addn_ret_t52, x_v23242, y_v23243);
  return addn_ret_t52;
}

tll_ptr lam_fun_t54(tll_ptr y_v23246, tll_env env) {
  tll_ptr call_ret_t53;
  call_ret_t53 = addn_i10(env[0], y_v23246);
  return call_ret_t53;
}

tll_ptr lam_fun_t56(tll_ptr x_v23244, tll_env env) {
  tll_ptr lam_clo_t55;
  instr_clo(&lam_clo_t55, &lam_fun_t54, 1, x_v23244);
  return lam_clo_t55;
}

tll_ptr subn_i11(tll_ptr x_v23247, tll_ptr y_v23248) {
  tll_ptr add_ret_t60; tll_ptr call_ret_t58; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t61;
  if (y_v23248) {
    call_ret_t59 = pred_i9(x_v23247);
    add_ret_t60 = y_v23248 - 1;
    call_ret_t58 = subn_i11(call_ret_t59, add_ret_t60);
    ifte_ret_t61 = call_ret_t58;
  }
  else {
    ifte_ret_t61 = x_v23247;
  }
  return ifte_ret_t61;
}

tll_ptr lam_fun_t63(tll_ptr y_v23251, tll_env env) {
  tll_ptr call_ret_t62;
  call_ret_t62 = subn_i11(env[0], y_v23251);
  return call_ret_t62;
}

tll_ptr lam_fun_t65(tll_ptr x_v23249, tll_env env) {
  tll_ptr lam_clo_t64;
  instr_clo(&lam_clo_t64, &lam_fun_t63, 1, x_v23249);
  return lam_clo_t64;
}

tll_ptr muln_i12(tll_ptr x_v23252, tll_ptr y_v23253) {
  tll_ptr muln_ret_t67;
  instr_muln(&muln_ret_t67, x_v23252, y_v23253);
  return muln_ret_t67;
}

tll_ptr lam_fun_t69(tll_ptr y_v23256, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = muln_i12(env[0], y_v23256);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr x_v23254, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, x_v23254);
  return lam_clo_t70;
}

tll_ptr divn_i13(tll_ptr x_v23257, tll_ptr y_v23258) {
  tll_ptr divn_ret_t73;
  instr_divn(&divn_ret_t73, x_v23257, y_v23258);
  return divn_ret_t73;
}

tll_ptr lam_fun_t75(tll_ptr y_v23261, tll_env env) {
  tll_ptr call_ret_t74;
  call_ret_t74 = divn_i13(env[0], y_v23261);
  return call_ret_t74;
}

tll_ptr lam_fun_t77(tll_ptr x_v23259, tll_env env) {
  tll_ptr lam_clo_t76;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 1, x_v23259);
  return lam_clo_t76;
}

tll_ptr modn_i14(tll_ptr x_v23262, tll_ptr y_v23263) {
  tll_ptr modn_ret_t79;
  instr_modn(&modn_ret_t79, x_v23262, y_v23263);
  return modn_ret_t79;
}

tll_ptr lam_fun_t81(tll_ptr y_v23266, tll_env env) {
  tll_ptr call_ret_t80;
  call_ret_t80 = modn_i14(env[0], y_v23266);
  return call_ret_t80;
}

tll_ptr lam_fun_t83(tll_ptr x_v23264, tll_env env) {
  tll_ptr lam_clo_t82;
  instr_clo(&lam_clo_t82, &lam_fun_t81, 1, x_v23264);
  return lam_clo_t82;
}

tll_ptr cats_i15(tll_ptr s1_v23267, tll_ptr s2_v23268) {
  tll_ptr String_t87; tll_ptr c_v23269; tll_ptr call_ret_t86;
  tll_ptr s1_v23270; tll_ptr switch_ret_t85;
  switch(((tll_node)s1_v23267)->tag) {
    case 2:
      switch_ret_t85 = s2_v23268;
      break;
    case 3:
      c_v23269 = ((tll_node)s1_v23267)->data[0];
      s1_v23270 = ((tll_node)s1_v23267)->data[1];
      call_ret_t86 = cats_i15(s1_v23270, s2_v23268);
      instr_struct(&String_t87, 3, 2, c_v23269, call_ret_t86);
      switch_ret_t85 = String_t87;
      break;
  }
  return switch_ret_t85;
}

tll_ptr lam_fun_t89(tll_ptr s2_v23273, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = cats_i15(env[0], s2_v23273);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr s1_v23271, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, s1_v23271);
  return lam_clo_t90;
}

tll_ptr strlen_i16(tll_ptr s_v23274) {
  tll_ptr __v23275; tll_ptr add_ret_t95; tll_ptr call_ret_t94;
  tll_ptr s_v23276; tll_ptr switch_ret_t93;
  switch(((tll_node)s_v23274)->tag) {
    case 2:
      switch_ret_t93 = (tll_ptr)0;
      break;
    case 3:
      __v23275 = ((tll_node)s_v23274)->data[0];
      s_v23276 = ((tll_node)s_v23274)->data[1];
      call_ret_t94 = strlen_i16(s_v23276);
      add_ret_t95 = call_ret_t94 + 1;
      switch_ret_t93 = add_ret_t95;
      break;
  }
  return switch_ret_t93;
}

tll_ptr lam_fun_t97(tll_ptr s_v23277, tll_env env) {
  tll_ptr call_ret_t96;
  call_ret_t96 = strlen_i16(s_v23277);
  return call_ret_t96;
}

tll_ptr lenUU_i44(tll_ptr A_v23278, tll_ptr xs_v23279) {
  tll_ptr add_ret_t104; tll_ptr call_ret_t102; tll_ptr consUU_t105;
  tll_ptr n_v23282; tll_ptr nilUU_t100; tll_ptr pair_struct_t101;
  tll_ptr pair_struct_t106; tll_ptr switch_ret_t103; tll_ptr switch_ret_t99;
  tll_ptr x_v23280; tll_ptr xs_v23281; tll_ptr xs_v23283;
  switch(((tll_node)xs_v23279)->tag) {
    case 12:
      instr_struct(&nilUU_t100, 12, 0);
      instr_struct(&pair_struct_t101, 0, 2, (tll_ptr)0, nilUU_t100);
      switch_ret_t99 = pair_struct_t101;
      break;
    case 13:
      x_v23280 = ((tll_node)xs_v23279)->data[0];
      xs_v23281 = ((tll_node)xs_v23279)->data[1];
      call_ret_t102 = lenUU_i44(0, xs_v23281);
      switch(((tll_node)call_ret_t102)->tag) {
        case 0:
          n_v23282 = ((tll_node)call_ret_t102)->data[0];
          xs_v23283 = ((tll_node)call_ret_t102)->data[1];
          instr_free_struct(call_ret_t102);
          add_ret_t104 = n_v23282 + 1;
          instr_struct(&consUU_t105, 13, 2, x_v23280, xs_v23283);
          instr_struct(&pair_struct_t106, 0, 2, add_ret_t104, consUU_t105);
          switch_ret_t103 = pair_struct_t106;
          break;
      }
      switch_ret_t99 = switch_ret_t103;
      break;
  }
  return switch_ret_t99;
}

tll_ptr lam_fun_t108(tll_ptr xs_v23286, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = lenUU_i44(env[0], xs_v23286);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr A_v23284, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, A_v23284);
  return lam_clo_t109;
}

tll_ptr lenUL_i43(tll_ptr A_v23287, tll_ptr xs_v23288) {
  tll_ptr add_ret_t117; tll_ptr call_ret_t115; tll_ptr consUL_t118;
  tll_ptr n_v23291; tll_ptr nilUL_t113; tll_ptr pair_struct_t114;
  tll_ptr pair_struct_t119; tll_ptr switch_ret_t112; tll_ptr switch_ret_t116;
  tll_ptr x_v23289; tll_ptr xs_v23290; tll_ptr xs_v23292;
  switch(((tll_node)xs_v23288)->tag) {
    case 10:
      instr_free_struct(xs_v23288);
      instr_struct(&nilUL_t113, 10, 0);
      instr_struct(&pair_struct_t114, 0, 2, (tll_ptr)0, nilUL_t113);
      switch_ret_t112 = pair_struct_t114;
      break;
    case 11:
      x_v23289 = ((tll_node)xs_v23288)->data[0];
      xs_v23290 = ((tll_node)xs_v23288)->data[1];
      instr_free_struct(xs_v23288);
      call_ret_t115 = lenUL_i43(0, xs_v23290);
      switch(((tll_node)call_ret_t115)->tag) {
        case 0:
          n_v23291 = ((tll_node)call_ret_t115)->data[0];
          xs_v23292 = ((tll_node)call_ret_t115)->data[1];
          instr_free_struct(call_ret_t115);
          add_ret_t117 = n_v23291 + 1;
          instr_struct(&consUL_t118, 11, 2, x_v23289, xs_v23292);
          instr_struct(&pair_struct_t119, 0, 2, add_ret_t117, consUL_t118);
          switch_ret_t116 = pair_struct_t119;
          break;
      }
      switch_ret_t112 = switch_ret_t116;
      break;
  }
  return switch_ret_t112;
}

tll_ptr lam_fun_t121(tll_ptr xs_v23295, tll_env env) {
  tll_ptr call_ret_t120;
  call_ret_t120 = lenUL_i43(env[0], xs_v23295);
  return call_ret_t120;
}

tll_ptr lam_fun_t123(tll_ptr A_v23293, tll_env env) {
  tll_ptr lam_clo_t122;
  instr_clo(&lam_clo_t122, &lam_fun_t121, 1, A_v23293);
  return lam_clo_t122;
}

tll_ptr lenLL_i41(tll_ptr A_v23296, tll_ptr xs_v23297) {
  tll_ptr add_ret_t130; tll_ptr call_ret_t128; tll_ptr consLL_t131;
  tll_ptr n_v23300; tll_ptr nilLL_t126; tll_ptr pair_struct_t127;
  tll_ptr pair_struct_t132; tll_ptr switch_ret_t125; tll_ptr switch_ret_t129;
  tll_ptr x_v23298; tll_ptr xs_v23299; tll_ptr xs_v23301;
  switch(((tll_node)xs_v23297)->tag) {
    case 6:
      instr_free_struct(xs_v23297);
      instr_struct(&nilLL_t126, 6, 0);
      instr_struct(&pair_struct_t127, 0, 2, (tll_ptr)0, nilLL_t126);
      switch_ret_t125 = pair_struct_t127;
      break;
    case 7:
      x_v23298 = ((tll_node)xs_v23297)->data[0];
      xs_v23299 = ((tll_node)xs_v23297)->data[1];
      instr_free_struct(xs_v23297);
      call_ret_t128 = lenLL_i41(0, xs_v23299);
      switch(((tll_node)call_ret_t128)->tag) {
        case 0:
          n_v23300 = ((tll_node)call_ret_t128)->data[0];
          xs_v23301 = ((tll_node)call_ret_t128)->data[1];
          instr_free_struct(call_ret_t128);
          add_ret_t130 = n_v23300 + 1;
          instr_struct(&consLL_t131, 7, 2, x_v23298, xs_v23301);
          instr_struct(&pair_struct_t132, 0, 2, add_ret_t130, consLL_t131);
          switch_ret_t129 = pair_struct_t132;
          break;
      }
      switch_ret_t125 = switch_ret_t129;
      break;
  }
  return switch_ret_t125;
}

tll_ptr lam_fun_t134(tll_ptr xs_v23304, tll_env env) {
  tll_ptr call_ret_t133;
  call_ret_t133 = lenLL_i41(env[0], xs_v23304);
  return call_ret_t133;
}

tll_ptr lam_fun_t136(tll_ptr A_v23302, tll_env env) {
  tll_ptr lam_clo_t135;
  instr_clo(&lam_clo_t135, &lam_fun_t134, 1, A_v23302);
  return lam_clo_t135;
}

tll_ptr appendUU_i48(tll_ptr A_v23305, tll_ptr xs_v23306, tll_ptr ys_v23307) {
  tll_ptr call_ret_t139; tll_ptr consUU_t140; tll_ptr switch_ret_t138;
  tll_ptr x_v23308; tll_ptr xs_v23309;
  switch(((tll_node)xs_v23306)->tag) {
    case 12:
      switch_ret_t138 = ys_v23307;
      break;
    case 13:
      x_v23308 = ((tll_node)xs_v23306)->data[0];
      xs_v23309 = ((tll_node)xs_v23306)->data[1];
      call_ret_t139 = appendUU_i48(0, xs_v23309, ys_v23307);
      instr_struct(&consUU_t140, 13, 2, x_v23308, call_ret_t139);
      switch_ret_t138 = consUU_t140;
      break;
  }
  return switch_ret_t138;
}

tll_ptr lam_fun_t142(tll_ptr ys_v23315, tll_env env) {
  tll_ptr call_ret_t141;
  call_ret_t141 = appendUU_i48(env[1], env[0], ys_v23315);
  return call_ret_t141;
}

tll_ptr lam_fun_t144(tll_ptr xs_v23313, tll_env env) {
  tll_ptr lam_clo_t143;
  instr_clo(&lam_clo_t143, &lam_fun_t142, 2, xs_v23313, env[0]);
  return lam_clo_t143;
}

tll_ptr lam_fun_t146(tll_ptr A_v23310, tll_env env) {
  tll_ptr lam_clo_t145;
  instr_clo(&lam_clo_t145, &lam_fun_t144, 1, A_v23310);
  return lam_clo_t145;
}

tll_ptr appendUL_i47(tll_ptr A_v23316, tll_ptr xs_v23317, tll_ptr ys_v23318) {
  tll_ptr call_ret_t149; tll_ptr consUL_t150; tll_ptr switch_ret_t148;
  tll_ptr x_v23319; tll_ptr xs_v23320;
  switch(((tll_node)xs_v23317)->tag) {
    case 10:
      instr_free_struct(xs_v23317);
      switch_ret_t148 = ys_v23318;
      break;
    case 11:
      x_v23319 = ((tll_node)xs_v23317)->data[0];
      xs_v23320 = ((tll_node)xs_v23317)->data[1];
      instr_free_struct(xs_v23317);
      call_ret_t149 = appendUL_i47(0, xs_v23320, ys_v23318);
      instr_struct(&consUL_t150, 11, 2, x_v23319, call_ret_t149);
      switch_ret_t148 = consUL_t150;
      break;
  }
  return switch_ret_t148;
}

tll_ptr lam_fun_t152(tll_ptr ys_v23326, tll_env env) {
  tll_ptr call_ret_t151;
  call_ret_t151 = appendUL_i47(env[1], env[0], ys_v23326);
  return call_ret_t151;
}

tll_ptr lam_fun_t154(tll_ptr xs_v23324, tll_env env) {
  tll_ptr lam_clo_t153;
  instr_clo(&lam_clo_t153, &lam_fun_t152, 2, xs_v23324, env[0]);
  return lam_clo_t153;
}

tll_ptr lam_fun_t156(tll_ptr A_v23321, tll_env env) {
  tll_ptr lam_clo_t155;
  instr_clo(&lam_clo_t155, &lam_fun_t154, 1, A_v23321);
  return lam_clo_t155;
}

tll_ptr appendLL_i45(tll_ptr A_v23327, tll_ptr xs_v23328, tll_ptr ys_v23329) {
  tll_ptr call_ret_t159; tll_ptr consLL_t160; tll_ptr switch_ret_t158;
  tll_ptr x_v23330; tll_ptr xs_v23331;
  switch(((tll_node)xs_v23328)->tag) {
    case 6:
      instr_free_struct(xs_v23328);
      switch_ret_t158 = ys_v23329;
      break;
    case 7:
      x_v23330 = ((tll_node)xs_v23328)->data[0];
      xs_v23331 = ((tll_node)xs_v23328)->data[1];
      instr_free_struct(xs_v23328);
      call_ret_t159 = appendLL_i45(0, xs_v23331, ys_v23329);
      instr_struct(&consLL_t160, 7, 2, x_v23330, call_ret_t159);
      switch_ret_t158 = consLL_t160;
      break;
  }
  return switch_ret_t158;
}

tll_ptr lam_fun_t162(tll_ptr ys_v23337, tll_env env) {
  tll_ptr call_ret_t161;
  call_ret_t161 = appendLL_i45(env[1], env[0], ys_v23337);
  return call_ret_t161;
}

tll_ptr lam_fun_t164(tll_ptr xs_v23335, tll_env env) {
  tll_ptr lam_clo_t163;
  instr_clo(&lam_clo_t163, &lam_fun_t162, 2, xs_v23335, env[0]);
  return lam_clo_t163;
}

tll_ptr lam_fun_t166(tll_ptr A_v23332, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, A_v23332);
  return lam_clo_t165;
}

tll_ptr lam_fun_t173(tll_ptr __v23339, tll_env env) {
  tll_ptr __v23348; tll_ptr ch_v23346; tll_ptr ch_v23347; tll_ptr ch_v23350;
  tll_ptr ch_v23351; tll_ptr prim_ch_t168; tll_ptr recv_msg_t170;
  tll_ptr s_v23349; tll_ptr send_ch_t169; tll_ptr send_ch_t172;
  tll_ptr switch_ret_t171;
  instr_open(&prim_ch_t168, &proc_stdin);
  ch_v23346 = prim_ch_t168;
  instr_send(&send_ch_t169, ch_v23346, (tll_ptr)1);
  ch_v23347 = send_ch_t169;
  instr_recv(&recv_msg_t170, ch_v23347);
  __v23348 = recv_msg_t170;
  switch(((tll_node)__v23348)->tag) {
    case 0:
      s_v23349 = ((tll_node)__v23348)->data[0];
      ch_v23350 = ((tll_node)__v23348)->data[1];
      instr_free_struct(__v23348);
      instr_send(&send_ch_t172, ch_v23350, (tll_ptr)0);
      ch_v23351 = send_ch_t172;
      switch_ret_t171 = s_v23349;
      break;
  }
  return switch_ret_t171;
}

tll_ptr readline_i25(tll_ptr __v23338) {
  tll_ptr lam_clo_t174;
  instr_clo(&lam_clo_t174, &lam_fun_t173, 0);
  return lam_clo_t174;
}

tll_ptr lam_fun_t176(tll_ptr __v23352, tll_env env) {
  tll_ptr call_ret_t175;
  call_ret_t175 = readline_i25(__v23352);
  return call_ret_t175;
}

tll_ptr lam_fun_t182(tll_ptr __v23354, tll_env env) {
  tll_ptr ch_v23359; tll_ptr ch_v23360; tll_ptr ch_v23361; tll_ptr ch_v23362;
  tll_ptr prim_ch_t178; tll_ptr send_ch_t179; tll_ptr send_ch_t180;
  tll_ptr send_ch_t181;
  instr_open(&prim_ch_t178, &proc_stdout);
  ch_v23359 = prim_ch_t178;
  instr_send(&send_ch_t179, ch_v23359, (tll_ptr)1);
  ch_v23360 = send_ch_t179;
  instr_send(&send_ch_t180, ch_v23360, env[0]);
  ch_v23361 = send_ch_t180;
  instr_send(&send_ch_t181, ch_v23361, (tll_ptr)0);
  ch_v23362 = send_ch_t181;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v23353) {
  tll_ptr lam_clo_t183;
  instr_clo(&lam_clo_t183, &lam_fun_t182, 1, s_v23353);
  return lam_clo_t183;
}

tll_ptr lam_fun_t185(tll_ptr s_v23363, tll_env env) {
  tll_ptr call_ret_t184;
  call_ret_t184 = print_i26(s_v23363);
  return call_ret_t184;
}

tll_ptr lam_fun_t191(tll_ptr __v23365, tll_env env) {
  tll_ptr ch_v23370; tll_ptr ch_v23371; tll_ptr ch_v23372; tll_ptr ch_v23373;
  tll_ptr prim_ch_t187; tll_ptr send_ch_t188; tll_ptr send_ch_t189;
  tll_ptr send_ch_t190;
  instr_open(&prim_ch_t187, &proc_stderr);
  ch_v23370 = prim_ch_t187;
  instr_send(&send_ch_t188, ch_v23370, (tll_ptr)1);
  ch_v23371 = send_ch_t188;
  instr_send(&send_ch_t189, ch_v23371, env[0]);
  ch_v23372 = send_ch_t189;
  instr_send(&send_ch_t190, ch_v23372, (tll_ptr)0);
  ch_v23373 = send_ch_t190;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v23364) {
  tll_ptr lam_clo_t192;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 1, s_v23364);
  return lam_clo_t192;
}

tll_ptr lam_fun_t194(tll_ptr s_v23374, tll_env env) {
  tll_ptr call_ret_t193;
  call_ret_t193 = prerr_i27(s_v23374);
  return call_ret_t193;
}

tll_ptr get_at_i29(tll_ptr A_v23375, tll_ptr n_v23376, tll_ptr xs_v23377, tll_ptr a_v23378) {
  tll_ptr __v23379; tll_ptr __v23382; tll_ptr add_ret_t239;
  tll_ptr call_ret_t238; tll_ptr ifte_ret_t241; tll_ptr switch_ret_t237;
  tll_ptr switch_ret_t240; tll_ptr x_v23381; tll_ptr xs_v23380;
  if (n_v23376) {
    switch(((tll_node)xs_v23377)->tag) {
      case 12:
        switch_ret_t237 = a_v23378;
        break;
      case 13:
        __v23379 = ((tll_node)xs_v23377)->data[0];
        xs_v23380 = ((tll_node)xs_v23377)->data[1];
        add_ret_t239 = n_v23376 - 1;
        call_ret_t238 = get_at_i29(0, add_ret_t239, xs_v23380, a_v23378);
        switch_ret_t237 = call_ret_t238;
        break;
    }
    ifte_ret_t241 = switch_ret_t237;
  }
  else {
    switch(((tll_node)xs_v23377)->tag) {
      case 12:
        switch_ret_t240 = a_v23378;
        break;
      case 13:
        x_v23381 = ((tll_node)xs_v23377)->data[0];
        __v23382 = ((tll_node)xs_v23377)->data[1];
        switch_ret_t240 = x_v23381;
        break;
    }
    ifte_ret_t241 = switch_ret_t240;
  }
  return ifte_ret_t241;
}

tll_ptr lam_fun_t243(tll_ptr a_v23392, tll_env env) {
  tll_ptr call_ret_t242;
  call_ret_t242 = get_at_i29(env[2], env[1], env[0], a_v23392);
  return call_ret_t242;
}

tll_ptr lam_fun_t245(tll_ptr xs_v23390, tll_env env) {
  tll_ptr lam_clo_t244;
  instr_clo(&lam_clo_t244, &lam_fun_t243, 3, xs_v23390, env[0], env[1]);
  return lam_clo_t244;
}

tll_ptr lam_fun_t247(tll_ptr n_v23387, tll_env env) {
  tll_ptr lam_clo_t246;
  instr_clo(&lam_clo_t246, &lam_fun_t245, 2, n_v23387, env[0]);
  return lam_clo_t246;
}

tll_ptr lam_fun_t249(tll_ptr A_v23383, tll_env env) {
  tll_ptr lam_clo_t248;
  instr_clo(&lam_clo_t248, &lam_fun_t247, 1, A_v23383);
  return lam_clo_t248;
}

tll_ptr string_of_digit_i30(tll_ptr n_v23393) {
  tll_ptr EmptyString_t252; tll_ptr call_ret_t251;
  instr_struct(&EmptyString_t252, 2, 0);
  call_ret_t251 = get_at_i29(0, n_v23393, digits_i28, EmptyString_t252);
  return call_ret_t251;
}

tll_ptr lam_fun_t254(tll_ptr n_v23394, tll_env env) {
  tll_ptr call_ret_t253;
  call_ret_t253 = string_of_digit_i30(n_v23394);
  return call_ret_t253;
}

tll_ptr string_of_nat_i31(tll_ptr n_v23395) {
  tll_ptr call_ret_t256; tll_ptr call_ret_t257; tll_ptr call_ret_t258;
  tll_ptr call_ret_t259; tll_ptr call_ret_t260; tll_ptr call_ret_t261;
  tll_ptr ifte_ret_t262; tll_ptr n_v23397; tll_ptr s_v23396;
  call_ret_t257 = modn_i14(n_v23395, (tll_ptr)10);
  call_ret_t256 = string_of_digit_i30(call_ret_t257);
  s_v23396 = call_ret_t256;
  call_ret_t258 = divn_i13(n_v23395, (tll_ptr)10);
  n_v23397 = call_ret_t258;
  call_ret_t259 = ltn_i6((tll_ptr)0, n_v23397);
  if (call_ret_t259) {
    call_ret_t261 = string_of_nat_i31(n_v23397);
    call_ret_t260 = cats_i15(call_ret_t261, s_v23396);
    ifte_ret_t262 = call_ret_t260;
  }
  else {
    ifte_ret_t262 = s_v23396;
  }
  return ifte_ret_t262;
}

tll_ptr lam_fun_t264(tll_ptr n_v23398, tll_env env) {
  tll_ptr call_ret_t263;
  call_ret_t263 = string_of_nat_i31(n_v23398);
  return call_ret_t263;
}

tll_ptr powm_i33(tll_ptr a_v23399, tll_ptr b_v23400, tll_ptr m_v23401) {
  tll_ptr add_ret_t269; tll_ptr call_ret_t266; tll_ptr call_ret_t267;
  tll_ptr call_ret_t268; tll_ptr ifte_ret_t270;
  if (b_v23400) {
    add_ret_t269 = b_v23400 - 1;
    call_ret_t268 = powm_i33(a_v23399, add_ret_t269, m_v23401);
    call_ret_t267 = muln_i12(a_v23399, call_ret_t268);
    call_ret_t266 = modn_i14(call_ret_t267, m_v23401);
    ifte_ret_t270 = call_ret_t266;
  }
  else {
    ifte_ret_t270 = (tll_ptr)1;
  }
  return ifte_ret_t270;
}

tll_ptr lam_fun_t272(tll_ptr m_v23407, tll_env env) {
  tll_ptr call_ret_t271;
  call_ret_t271 = powm_i33(env[1], env[0], m_v23407);
  return call_ret_t271;
}

tll_ptr lam_fun_t274(tll_ptr b_v23405, tll_env env) {
  tll_ptr lam_clo_t273;
  instr_clo(&lam_clo_t273, &lam_fun_t272, 2, b_v23405, env[0]);
  return lam_clo_t273;
}

tll_ptr lam_fun_t276(tll_ptr a_v23402, tll_env env) {
  tll_ptr lam_clo_t275;
  instr_clo(&lam_clo_t275, &lam_fun_t274, 1, a_v23402);
  return lam_clo_t275;
}

tll_ptr lam_fun_t301(tll_ptr __v23409, tll_env env) {
  tll_ptr __v23438; tll_ptr __v23447; tll_ptr call_ret_t298;
  tll_ptr ch_v23435; tll_ptr ch_v23437; tll_ptr ch_v23440; tll_ptr ch_v23442;
  tll_ptr ch_v23444; tll_ptr ch_v23446; tll_ptr ch_v23449; tll_ptr ch_v23451;
  tll_ptr ch_v23453; tll_ptr ch_v23455; tll_ptr ch_v23456;
  tll_ptr close_tmp_t300; tll_ptr e_v23448; tll_ptr n_v23439;
  tll_ptr pair_struct_t278; tll_ptr pair_struct_t280;
  tll_ptr pair_struct_t284; tll_ptr pair_struct_t286;
  tll_ptr pair_struct_t288; tll_ptr pair_struct_t292;
  tll_ptr pair_struct_t294; tll_ptr pair_struct_t296; tll_ptr pf1_v23441;
  tll_ptr pf2_v23445; tll_ptr pf3_v23450; tll_ptr pf4_v23452;
  tll_ptr pf5_v23454; tll_ptr recv_msg_t282; tll_ptr recv_msg_t290;
  tll_ptr send_ch_t299; tll_ptr switch_ret_t279; tll_ptr switch_ret_t281;
  tll_ptr switch_ret_t283; tll_ptr switch_ret_t285; tll_ptr switch_ret_t287;
  tll_ptr switch_ret_t289; tll_ptr switch_ret_t291; tll_ptr switch_ret_t293;
  tll_ptr switch_ret_t295; tll_ptr switch_ret_t297; tll_ptr tot_v23443;
  tll_ptr x_v23434; tll_ptr x_v23457; tll_ptr y_v23436;
  instr_struct(&pair_struct_t278, 0, 2, 0, env[0]);
  switch(((tll_node)pair_struct_t278)->tag) {
    case 0:
      x_v23434 = ((tll_node)pair_struct_t278)->data[0];
      ch_v23435 = ((tll_node)pair_struct_t278)->data[1];
      instr_free_struct(pair_struct_t278);
      instr_struct(&pair_struct_t280, 0, 2, 0, ch_v23435);
      switch(((tll_node)pair_struct_t280)->tag) {
        case 0:
          y_v23436 = ((tll_node)pair_struct_t280)->data[0];
          ch_v23437 = ((tll_node)pair_struct_t280)->data[1];
          instr_free_struct(pair_struct_t280);
          instr_recv(&recv_msg_t282, ch_v23437);
          __v23438 = recv_msg_t282;
          switch(((tll_node)__v23438)->tag) {
            case 0:
              n_v23439 = ((tll_node)__v23438)->data[0];
              ch_v23440 = ((tll_node)__v23438)->data[1];
              instr_free_struct(__v23438);
              instr_struct(&pair_struct_t284, 0, 2, 0, ch_v23440);
              switch(((tll_node)pair_struct_t284)->tag) {
                case 0:
                  pf1_v23441 = ((tll_node)pair_struct_t284)->data[0];
                  ch_v23442 = ((tll_node)pair_struct_t284)->data[1];
                  instr_free_struct(pair_struct_t284);
                  instr_struct(&pair_struct_t286, 0, 2, 0, ch_v23442);
                  switch(((tll_node)pair_struct_t286)->tag) {
                    case 0:
                      tot_v23443 = ((tll_node)pair_struct_t286)->data[0];
                      ch_v23444 = ((tll_node)pair_struct_t286)->data[1];
                      instr_free_struct(pair_struct_t286);
                      instr_struct(&pair_struct_t288, 0, 2, 0, ch_v23444);
                      switch(((tll_node)pair_struct_t288)->tag) {
                        case 0:
                          pf2_v23445 = ((tll_node)pair_struct_t288)->data[0];
                          ch_v23446 = ((tll_node)pair_struct_t288)->data[1];
                          instr_free_struct(pair_struct_t288);
                          instr_recv(&recv_msg_t290, ch_v23446);
                          __v23447 = recv_msg_t290;
                          switch(((tll_node)__v23447)->tag) {
                            case 0:
                              e_v23448 = ((tll_node)__v23447)->data[0];
                              ch_v23449 = ((tll_node)__v23447)->data[1];
                              instr_free_struct(__v23447);
                              instr_struct(&pair_struct_t292, 0, 2,
                                           0, ch_v23449);
                              switch(((tll_node)pair_struct_t292)->tag) {
                                case 0:
                                  pf3_v23450 = ((tll_node)pair_struct_t292)->data[0];
                                  ch_v23451 = ((tll_node)pair_struct_t292)->data[1];
                                  instr_free_struct(pair_struct_t292);
                                  instr_struct(&pair_struct_t294, 0, 2,
                                               0, ch_v23451);
                                  switch(((tll_node)pair_struct_t294)->tag) {
                                    case 0:
                                      pf4_v23452 = ((tll_node)pair_struct_t294)->data[0];
                                      ch_v23453 = ((tll_node)pair_struct_t294)->data[1];
                                      instr_free_struct(pair_struct_t294);
                                      instr_struct(&pair_struct_t296, 0, 2,
                                                   0, ch_v23453);
                                      switch(((tll_node)pair_struct_t296)->tag) {
                                        case 0:
                                          pf5_v23454 = ((tll_node)pair_struct_t296)->data[0];
                                          ch_v23455 = ((tll_node)pair_struct_t296)->data[1];
                                          instr_free_struct(pair_struct_t296);
                                          call_ret_t298 = powm_i33((tll_ptr)123,
                                                                   e_v23448,
                                                                   n_v23439);
                                          x_v23457 = call_ret_t298;
                                          instr_send(&send_ch_t299, ch_v23455, x_v23457);
                                          ch_v23456 = send_ch_t299;
                                          instr_close(&close_tmp_t300, ch_v23456);
                                          switch_ret_t297 = close_tmp_t300;
                                          break;
                                      }
                                      switch_ret_t295 = switch_ret_t297;
                                      break;
                                  }
                                  switch_ret_t293 = switch_ret_t295;
                                  break;
                              }
                              switch_ret_t291 = switch_ret_t293;
                              break;
                          }
                          switch_ret_t289 = switch_ret_t291;
                          break;
                      }
                      switch_ret_t287 = switch_ret_t289;
                      break;
                  }
                  switch_ret_t285 = switch_ret_t287;
                  break;
              }
              switch_ret_t283 = switch_ret_t285;
              break;
          }
          switch_ret_t281 = switch_ret_t283;
          break;
      }
      switch_ret_t279 = switch_ret_t281;
      break;
  }
  return switch_ret_t279;
}

tll_ptr client_i38(tll_ptr ch_v23408) {
  tll_ptr lam_clo_t302;
  instr_clo(&lam_clo_t302, &lam_fun_t301, 1, ch_v23408);
  return lam_clo_t302;
}

tll_ptr lam_fun_t304(tll_ptr ch_v23458, tll_env env) {
  tll_ptr call_ret_t303;
  call_ret_t303 = client_i38(ch_v23458);
  return call_ret_t303;
}

tll_ptr lam_fun_t326(tll_ptr __v23462, tll_env env) {
  tll_ptr C_v23478; tll_ptr Char_t322; tll_ptr EmptyString_t323;
  tll_ptr P0_v23475; tll_ptr P1_v23482; tll_ptr String_t324;
  tll_ptr __v23477; tll_ptr app_ret_t325; tll_ptr call_ret_t318;
  tll_ptr call_ret_t319; tll_ptr call_ret_t320; tll_ptr call_ret_t321;
  tll_ptr ch_v23473; tll_ptr ch_v23474; tll_ptr ch_v23476; tll_ptr ch_v23479;
  tll_ptr ch_v23481; tll_ptr pair_struct_t312; tll_ptr pair_struct_t316;
  tll_ptr pf_v23480; tll_ptr recv_msg_t314; tll_ptr send_ch_t310;
  tll_ptr send_ch_t311; tll_ptr switch_ret_t313; tll_ptr switch_ret_t315;
  tll_ptr switch_ret_t317;
  instr_send(&send_ch_t310, env[1], env[0]);
  ch_v23473 = send_ch_t310;
  instr_send(&send_ch_t311, ch_v23473, (tll_ptr)17);
  ch_v23474 = send_ch_t311;
  instr_struct(&pair_struct_t312, 0, 2, 0, ch_v23474);
  switch(((tll_node)pair_struct_t312)->tag) {
    case 0:
      P0_v23475 = ((tll_node)pair_struct_t312)->data[0];
      ch_v23476 = ((tll_node)pair_struct_t312)->data[1];
      instr_free_struct(pair_struct_t312);
      instr_recv(&recv_msg_t314, ch_v23476);
      __v23477 = recv_msg_t314;
      switch(((tll_node)__v23477)->tag) {
        case 0:
          C_v23478 = ((tll_node)__v23477)->data[0];
          ch_v23479 = ((tll_node)__v23477)->data[1];
          instr_free_struct(__v23477);
          instr_struct(&pair_struct_t316, 0, 2, 0, ch_v23479);
          switch(((tll_node)pair_struct_t316)->tag) {
            case 0:
              pf_v23480 = ((tll_node)pair_struct_t316)->data[0];
              ch_v23481 = ((tll_node)pair_struct_t316)->data[1];
              instr_free_struct(pair_struct_t316);
              call_ret_t318 = powm_i33(C_v23478, (tll_ptr)2753, env[0]);
              P1_v23482 = call_ret_t318;
              call_ret_t321 = string_of_nat_i31(P1_v23482);
              instr_struct(&Char_t322, 1, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t323, 2, 0);
              instr_struct(&String_t324, 3, 2, Char_t322, EmptyString_t323);
              call_ret_t320 = cats_i15(call_ret_t321, String_t324);
              call_ret_t319 = print_i26(call_ret_t320);
              instr_app(&app_ret_t325, call_ret_t319, 0);
              instr_free_clo(call_ret_t319);
              switch_ret_t317 = app_ret_t325;
              break;
          }
          switch_ret_t315 = switch_ret_t317;
          break;
      }
      switch_ret_t313 = switch_ret_t315;
      break;
  }
  return switch_ret_t313;
}

tll_ptr server_i39(tll_ptr ch_v23459) {
  tll_ptr call_ret_t306; tll_ptr call_ret_t307; tll_ptr call_ret_t308;
  tll_ptr call_ret_t309; tll_ptr lam_clo_t327; tll_ptr n_v23460;
  tll_ptr tot_v23461;
  call_ret_t306 = muln_i12((tll_ptr)61, (tll_ptr)53);
  n_v23460 = call_ret_t306;
  call_ret_t308 = subn_i11((tll_ptr)61, (tll_ptr)1);
  call_ret_t309 = subn_i11((tll_ptr)53, (tll_ptr)1);
  call_ret_t307 = muln_i12(call_ret_t308, call_ret_t309);
  tot_v23461 = call_ret_t307;
  instr_clo(&lam_clo_t327, &lam_fun_t326, 2, n_v23460, ch_v23459);
  return lam_clo_t327;
}

tll_ptr lam_fun_t329(tll_ptr ch_v23483, tll_env env) {
  tll_ptr call_ret_t328;
  call_ret_t328 = server_i39(ch_v23483);
  return call_ret_t328;
}

tll_ptr fork_fun_t333(tll_env env) {
  tll_ptr app_ret_t332; tll_ptr call_ret_t331; tll_ptr fork_ret_t335;
  call_ret_t331 = server_i39(env[0]);
  instr_app(&app_ret_t332, call_ret_t331, 0);
  instr_free_clo(call_ret_t331);
  fork_ret_t335 = app_ret_t332;
  instr_free_thread(env);
  return fork_ret_t335;
}

tll_ptr fork_fun_t340(tll_env env) {
  tll_ptr __v23491; tll_ptr app_ret_t339; tll_ptr c0_v23493;
  tll_ptr c_v23492; tll_ptr call_ret_t338; tll_ptr fork_ret_t342;
  tll_ptr recv_msg_t336; tll_ptr switch_ret_t337;
  instr_recv(&recv_msg_t336, env[0]);
  __v23491 = recv_msg_t336;
  switch(((tll_node)__v23491)->tag) {
    case 0:
      c_v23492 = ((tll_node)__v23491)->data[0];
      c0_v23493 = ((tll_node)__v23491)->data[1];
      instr_free_struct(__v23491);
      call_ret_t338 = client_i38(c_v23492);
      instr_app(&app_ret_t339, call_ret_t338, 0);
      instr_free_clo(call_ret_t338);
      switch_ret_t337 = app_ret_t339;
      break;
  }
  fork_ret_t342 = switch_ret_t337;
  instr_free_thread(env);
  return fork_ret_t342;
}

int main() {
  instr_init();
  tll_ptr Char_t196; tll_ptr Char_t199; tll_ptr Char_t202; tll_ptr Char_t205;
  tll_ptr Char_t208; tll_ptr Char_t211; tll_ptr Char_t214; tll_ptr Char_t217;
  tll_ptr Char_t220; tll_ptr Char_t223; tll_ptr EmptyString_t197;
  tll_ptr EmptyString_t200; tll_ptr EmptyString_t203;
  tll_ptr EmptyString_t206; tll_ptr EmptyString_t209;
  tll_ptr EmptyString_t212; tll_ptr EmptyString_t215;
  tll_ptr EmptyString_t218; tll_ptr EmptyString_t221;
  tll_ptr EmptyString_t224; tll_ptr String_t198; tll_ptr String_t201;
  tll_ptr String_t204; tll_ptr String_t207; tll_ptr String_t210;
  tll_ptr String_t213; tll_ptr String_t216; tll_ptr String_t219;
  tll_ptr String_t222; tll_ptr String_t225; tll_ptr __v23495;
  tll_ptr c0_v23486; tll_ptr c0_v23494; tll_ptr c_v23484;
  tll_ptr close_tmp_t344; tll_ptr consUU_t227; tll_ptr consUU_t228;
  tll_ptr consUU_t229; tll_ptr consUU_t230; tll_ptr consUU_t231;
  tll_ptr consUU_t232; tll_ptr consUU_t233; tll_ptr consUU_t234;
  tll_ptr consUU_t235; tll_ptr consUU_t236; tll_ptr fork_ch_t334;
  tll_ptr fork_ch_t341; tll_ptr lam_clo_t111; tll_ptr lam_clo_t12;
  tll_ptr lam_clo_t124; tll_ptr lam_clo_t137; tll_ptr lam_clo_t147;
  tll_ptr lam_clo_t157; tll_ptr lam_clo_t16; tll_ptr lam_clo_t167;
  tll_ptr lam_clo_t177; tll_ptr lam_clo_t186; tll_ptr lam_clo_t195;
  tll_ptr lam_clo_t22; tll_ptr lam_clo_t250; tll_ptr lam_clo_t255;
  tll_ptr lam_clo_t265; tll_ptr lam_clo_t277; tll_ptr lam_clo_t28;
  tll_ptr lam_clo_t305; tll_ptr lam_clo_t330; tll_ptr lam_clo_t34;
  tll_ptr lam_clo_t40; tll_ptr lam_clo_t46; tll_ptr lam_clo_t51;
  tll_ptr lam_clo_t57; tll_ptr lam_clo_t6; tll_ptr lam_clo_t66;
  tll_ptr lam_clo_t72; tll_ptr lam_clo_t78; tll_ptr lam_clo_t84;
  tll_ptr lam_clo_t92; tll_ptr lam_clo_t98; tll_ptr nilUU_t226;
  tll_ptr send_ch_t343; tll_ptr sleep_tmp_t345;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i49 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i50 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i51 = lam_clo_t16;
  instr_clo(&lam_clo_t22, &lam_fun_t21, 0);
  ltenclo_i52 = lam_clo_t22;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  gtenclo_i53 = lam_clo_t28;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 0);
  ltnclo_i54 = lam_clo_t34;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 0);
  gtnclo_i55 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  eqnclo_i56 = lam_clo_t46;
  instr_clo(&lam_clo_t51, &lam_fun_t50, 0);
  predclo_i57 = lam_clo_t51;
  instr_clo(&lam_clo_t57, &lam_fun_t56, 0);
  addnclo_i58 = lam_clo_t57;
  instr_clo(&lam_clo_t66, &lam_fun_t65, 0);
  subnclo_i59 = lam_clo_t66;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  mulnclo_i60 = lam_clo_t72;
  instr_clo(&lam_clo_t78, &lam_fun_t77, 0);
  divnclo_i61 = lam_clo_t78;
  instr_clo(&lam_clo_t84, &lam_fun_t83, 0);
  modnclo_i62 = lam_clo_t84;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  catsclo_i63 = lam_clo_t92;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  strlenclo_i64 = lam_clo_t98;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 0);
  lenUUclo_i65 = lam_clo_t111;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 0);
  lenULclo_i66 = lam_clo_t124;
  instr_clo(&lam_clo_t137, &lam_fun_t136, 0);
  lenLLclo_i67 = lam_clo_t137;
  instr_clo(&lam_clo_t147, &lam_fun_t146, 0);
  appendUUclo_i68 = lam_clo_t147;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 0);
  appendULclo_i69 = lam_clo_t157;
  instr_clo(&lam_clo_t167, &lam_fun_t166, 0);
  appendLLclo_i70 = lam_clo_t167;
  instr_clo(&lam_clo_t177, &lam_fun_t176, 0);
  readlineclo_i71 = lam_clo_t177;
  instr_clo(&lam_clo_t186, &lam_fun_t185, 0);
  printclo_i72 = lam_clo_t186;
  instr_clo(&lam_clo_t195, &lam_fun_t194, 0);
  prerrclo_i73 = lam_clo_t195;
  instr_struct(&Char_t196, 1, 1, (tll_ptr)48);
  instr_struct(&EmptyString_t197, 2, 0);
  instr_struct(&String_t198, 3, 2, Char_t196, EmptyString_t197);
  instr_struct(&Char_t199, 1, 1, (tll_ptr)49);
  instr_struct(&EmptyString_t200, 2, 0);
  instr_struct(&String_t201, 3, 2, Char_t199, EmptyString_t200);
  instr_struct(&Char_t202, 1, 1, (tll_ptr)50);
  instr_struct(&EmptyString_t203, 2, 0);
  instr_struct(&String_t204, 3, 2, Char_t202, EmptyString_t203);
  instr_struct(&Char_t205, 1, 1, (tll_ptr)51);
  instr_struct(&EmptyString_t206, 2, 0);
  instr_struct(&String_t207, 3, 2, Char_t205, EmptyString_t206);
  instr_struct(&Char_t208, 1, 1, (tll_ptr)52);
  instr_struct(&EmptyString_t209, 2, 0);
  instr_struct(&String_t210, 3, 2, Char_t208, EmptyString_t209);
  instr_struct(&Char_t211, 1, 1, (tll_ptr)53);
  instr_struct(&EmptyString_t212, 2, 0);
  instr_struct(&String_t213, 3, 2, Char_t211, EmptyString_t212);
  instr_struct(&Char_t214, 1, 1, (tll_ptr)54);
  instr_struct(&EmptyString_t215, 2, 0);
  instr_struct(&String_t216, 3, 2, Char_t214, EmptyString_t215);
  instr_struct(&Char_t217, 1, 1, (tll_ptr)55);
  instr_struct(&EmptyString_t218, 2, 0);
  instr_struct(&String_t219, 3, 2, Char_t217, EmptyString_t218);
  instr_struct(&Char_t220, 1, 1, (tll_ptr)56);
  instr_struct(&EmptyString_t221, 2, 0);
  instr_struct(&String_t222, 3, 2, Char_t220, EmptyString_t221);
  instr_struct(&Char_t223, 1, 1, (tll_ptr)57);
  instr_struct(&EmptyString_t224, 2, 0);
  instr_struct(&String_t225, 3, 2, Char_t223, EmptyString_t224);
  instr_struct(&nilUU_t226, 12, 0);
  instr_struct(&consUU_t227, 13, 2, String_t225, nilUU_t226);
  instr_struct(&consUU_t228, 13, 2, String_t222, consUU_t227);
  instr_struct(&consUU_t229, 13, 2, String_t219, consUU_t228);
  instr_struct(&consUU_t230, 13, 2, String_t216, consUU_t229);
  instr_struct(&consUU_t231, 13, 2, String_t213, consUU_t230);
  instr_struct(&consUU_t232, 13, 2, String_t210, consUU_t231);
  instr_struct(&consUU_t233, 13, 2, String_t207, consUU_t232);
  instr_struct(&consUU_t234, 13, 2, String_t204, consUU_t233);
  instr_struct(&consUU_t235, 13, 2, String_t201, consUU_t234);
  instr_struct(&consUU_t236, 13, 2, String_t198, consUU_t235);
  digits_i28 = consUU_t236;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 0);
  get_atclo_i74 = lam_clo_t250;
  instr_clo(&lam_clo_t255, &lam_fun_t254, 0);
  string_of_digitclo_i75 = lam_clo_t255;
  instr_clo(&lam_clo_t265, &lam_fun_t264, 0);
  string_of_natclo_i76 = lam_clo_t265;
  instr_clo(&lam_clo_t277, &lam_fun_t276, 0);
  powmclo_i77 = lam_clo_t277;
  instr_clo(&lam_clo_t305, &lam_fun_t304, 0);
  clientclo_i78 = lam_clo_t305;
  instr_clo(&lam_clo_t330, &lam_fun_t329, 0);
  serverclo_i79 = lam_clo_t330;
  instr_fork(&fork_ch_t334, &fork_fun_t333, 0);
  c_v23484 = fork_ch_t334;
  instr_fork(&fork_ch_t341, &fork_fun_t340, 0);
  c0_v23486 = fork_ch_t341;
  instr_send(&send_ch_t343, c0_v23486, c_v23484);
  c0_v23494 = send_ch_t343;
  instr_close(&close_tmp_t344, c0_v23494);
  __v23495 = close_tmp_t344;
  instr_sleep(&sleep_tmp_t345, (tll_ptr)1);
  return 0;
}

