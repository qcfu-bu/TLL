#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v81558, tll_ptr b2_v81559);
tll_ptr orb_i2(tll_ptr b1_v81563, tll_ptr b2_v81564);
tll_ptr notb_i3(tll_ptr b_v81568);
tll_ptr lten_i4(tll_ptr x_v81570, tll_ptr y_v81571);
tll_ptr gten_i5(tll_ptr x_v81575, tll_ptr y_v81576);
tll_ptr ltn_i6(tll_ptr x_v81581, tll_ptr y_v81582);
tll_ptr gtn_i7(tll_ptr x_v81587, tll_ptr y_v81588);
tll_ptr eqn_i8(tll_ptr x_v81592, tll_ptr y_v81593);
tll_ptr pred_i9(tll_ptr x_v81598);
tll_ptr addn_i10(tll_ptr x_v81600, tll_ptr y_v81601);
tll_ptr subn_i11(tll_ptr x_v81605, tll_ptr y_v81606);
tll_ptr muln_i12(tll_ptr x_v81610, tll_ptr y_v81611);
tll_ptr divn_i13(tll_ptr x_v81615, tll_ptr y_v81616);
tll_ptr modn_i14(tll_ptr x_v81620, tll_ptr y_v81621);
tll_ptr cats_i15(tll_ptr s1_v81625, tll_ptr s2_v81626);
tll_ptr strlen_i16(tll_ptr s_v81632);
tll_ptr lenUU_i40(tll_ptr A_v81636, tll_ptr xs_v81637);
tll_ptr lenUL_i39(tll_ptr A_v81645, tll_ptr xs_v81646);
tll_ptr lenLL_i37(tll_ptr A_v81654, tll_ptr xs_v81655);
tll_ptr appendUU_i44(tll_ptr A_v81663, tll_ptr xs_v81664, tll_ptr ys_v81665);
tll_ptr appendUL_i43(tll_ptr A_v81674, tll_ptr xs_v81675, tll_ptr ys_v81676);
tll_ptr appendLL_i41(tll_ptr A_v81685, tll_ptr xs_v81686, tll_ptr ys_v81687);
tll_ptr readline_i25(tll_ptr __v81696);
tll_ptr print_i26(tll_ptr s_v81705);
tll_ptr prerr_i27(tll_ptr s_v81710);
tll_ptr splitU_i46(tll_ptr zs_v81715);
tll_ptr splitL_i45(tll_ptr zs_v81723);
tll_ptr mergeU_i48(tll_ptr xs_v81731, tll_ptr ys_v81732);
tll_ptr mergeL_i47(tll_ptr xs_v81740, tll_ptr ys_v81741);
tll_ptr msortU_i50(tll_ptr zs_v81749);
tll_ptr msortL_i49(tll_ptr zs_v81757);
tll_ptr cmsort_workerU_i54(tll_ptr n_v81765, tll_ptr zs_v81766, tll_ptr c_v81767);
tll_ptr cmsort_workerL_i53(tll_ptr n_v81817, tll_ptr zs_v81818, tll_ptr c_v81819);
tll_ptr cmsortU_i56(tll_ptr zs_v81869);
tll_ptr cmsortL_i55(tll_ptr zs_v81880);
tll_ptr mkListU_i58(tll_ptr n_v81891);
tll_ptr mkListL_i57(tll_ptr n_v81893);
tll_ptr free_i35(tll_ptr A_v81895, tll_ptr ls_v81896);

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

tll_ptr andb_i1(tll_ptr b1_v81558, tll_ptr b2_v81559) {
  tll_ptr ifte_ret_t1;
  if (b1_v81558) {
    ifte_ret_t1 = b2_v81559;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v81562, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v81562);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v81560, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v81560);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v81563, tll_ptr b2_v81564) {
  tll_ptr ifte_ret_t7;
  if (b1_v81563) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v81564;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v81567, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v81567);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v81565, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v81565);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v81568) {
  tll_ptr ifte_ret_t13;
  if (b_v81568) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v81569, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v81569);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v81570, tll_ptr y_v81571) {
  tll_ptr add_ret_t18; tll_ptr add_ret_t19; tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  if (x_v81570) {
    if (y_v81571) {
      add_ret_t18 = x_v81570 - 1;
      add_ret_t19 = y_v81571 - 1;
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

tll_ptr lam_fun_t23(tll_ptr y_v81574, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v81574);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v81572, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v81572);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v81575, tll_ptr y_v81576) {
  tll_ptr __v81577; tll_ptr add_ret_t28; tll_ptr add_ret_t29;
  tll_ptr add_ret_t31; tll_ptr call_ret_t27; tll_ptr ifte_ret_t30;
  tll_ptr ifte_ret_t32; tll_ptr ifte_ret_t33;
  if (x_v81575) {
    if (y_v81576) {
      add_ret_t28 = x_v81575 - 1;
      add_ret_t29 = y_v81576 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t33 = ifte_ret_t30;
  }
  else {
    if (y_v81576) {
      add_ret_t31 = y_v81576 - 1;
      __v81577 = add_ret_t31;
      ifte_ret_t32 = (tll_ptr)0;
    }
    else {
      ifte_ret_t32 = (tll_ptr)1;
    }
    ifte_ret_t33 = ifte_ret_t32;
  }
  return ifte_ret_t33;
}

tll_ptr lam_fun_t35(tll_ptr y_v81580, tll_env env) {
  tll_ptr call_ret_t34;
  call_ret_t34 = gten_i5(env[0], y_v81580);
  return call_ret_t34;
}

tll_ptr lam_fun_t37(tll_ptr x_v81578, tll_env env) {
  tll_ptr lam_clo_t36;
  instr_clo(&lam_clo_t36, &lam_fun_t35, 1, x_v81578);
  return lam_clo_t36;
}

tll_ptr ltn_i6(tll_ptr x_v81581, tll_ptr y_v81582) {
  tll_ptr add_ret_t40; tll_ptr add_ret_t41; tll_ptr add_ret_t43;
  tll_ptr call_ret_t39; tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t44;
  tll_ptr ifte_ret_t45; tll_ptr y_v81583;
  if (x_v81581) {
    if (y_v81582) {
      add_ret_t40 = x_v81581 - 1;
      add_ret_t41 = y_v81582 - 1;
      call_ret_t39 = ltn_i6(add_ret_t40, add_ret_t41);
      ifte_ret_t42 = call_ret_t39;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t45 = ifte_ret_t42;
  }
  else {
    if (y_v81582) {
      add_ret_t43 = y_v81582 - 1;
      y_v81583 = add_ret_t43;
      ifte_ret_t44 = (tll_ptr)1;
    }
    else {
      ifte_ret_t44 = (tll_ptr)0;
    }
    ifte_ret_t45 = ifte_ret_t44;
  }
  return ifte_ret_t45;
}

tll_ptr lam_fun_t47(tll_ptr y_v81586, tll_env env) {
  tll_ptr call_ret_t46;
  call_ret_t46 = ltn_i6(env[0], y_v81586);
  return call_ret_t46;
}

tll_ptr lam_fun_t49(tll_ptr x_v81584, tll_env env) {
  tll_ptr lam_clo_t48;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 1, x_v81584);
  return lam_clo_t48;
}

tll_ptr gtn_i7(tll_ptr x_v81587, tll_ptr y_v81588) {
  tll_ptr add_ret_t52; tll_ptr add_ret_t53; tll_ptr call_ret_t51;
  tll_ptr ifte_ret_t54; tll_ptr ifte_ret_t55;
  if (x_v81587) {
    if (y_v81588) {
      add_ret_t52 = x_v81587 - 1;
      add_ret_t53 = y_v81588 - 1;
      call_ret_t51 = gtn_i7(add_ret_t52, add_ret_t53);
      ifte_ret_t54 = call_ret_t51;
    }
    else {
      ifte_ret_t54 = (tll_ptr)1;
    }
    ifte_ret_t55 = ifte_ret_t54;
  }
  else {
    ifte_ret_t55 = (tll_ptr)0;
  }
  return ifte_ret_t55;
}

tll_ptr lam_fun_t57(tll_ptr y_v81591, tll_env env) {
  tll_ptr call_ret_t56;
  call_ret_t56 = gtn_i7(env[0], y_v81591);
  return call_ret_t56;
}

tll_ptr lam_fun_t59(tll_ptr x_v81589, tll_env env) {
  tll_ptr lam_clo_t58;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 1, x_v81589);
  return lam_clo_t58;
}

tll_ptr eqn_i8(tll_ptr x_v81592, tll_ptr y_v81593) {
  tll_ptr __v81594; tll_ptr add_ret_t62; tll_ptr add_ret_t63;
  tll_ptr add_ret_t65; tll_ptr call_ret_t61; tll_ptr ifte_ret_t64;
  tll_ptr ifte_ret_t66; tll_ptr ifte_ret_t67;
  if (x_v81592) {
    if (y_v81593) {
      add_ret_t62 = x_v81592 - 1;
      add_ret_t63 = y_v81593 - 1;
      call_ret_t61 = eqn_i8(add_ret_t62, add_ret_t63);
      ifte_ret_t64 = call_ret_t61;
    }
    else {
      ifte_ret_t64 = (tll_ptr)0;
    }
    ifte_ret_t67 = ifte_ret_t64;
  }
  else {
    if (y_v81593) {
      add_ret_t65 = y_v81593 - 1;
      __v81594 = add_ret_t65;
      ifte_ret_t66 = (tll_ptr)0;
    }
    else {
      ifte_ret_t66 = (tll_ptr)1;
    }
    ifte_ret_t67 = ifte_ret_t66;
  }
  return ifte_ret_t67;
}

tll_ptr lam_fun_t69(tll_ptr y_v81597, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = eqn_i8(env[0], y_v81597);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr x_v81595, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, x_v81595);
  return lam_clo_t70;
}

tll_ptr pred_i9(tll_ptr x_v81598) {
  tll_ptr add_ret_t73; tll_ptr ifte_ret_t74;
  if (x_v81598) {
    add_ret_t73 = x_v81598 - 1;
    ifte_ret_t74 = add_ret_t73;
  }
  else {
    ifte_ret_t74 = (tll_ptr)0;
  }
  return ifte_ret_t74;
}

tll_ptr lam_fun_t76(tll_ptr x_v81599, tll_env env) {
  tll_ptr call_ret_t75;
  call_ret_t75 = pred_i9(x_v81599);
  return call_ret_t75;
}

tll_ptr addn_i10(tll_ptr x_v81600, tll_ptr y_v81601) {
  tll_ptr add_ret_t79; tll_ptr add_ret_t80; tll_ptr call_ret_t78;
  tll_ptr ifte_ret_t81;
  if (x_v81600) {
    add_ret_t79 = x_v81600 - 1;
    call_ret_t78 = addn_i10(add_ret_t79, y_v81601);
    add_ret_t80 = call_ret_t78 + 1;
    ifte_ret_t81 = add_ret_t80;
  }
  else {
    ifte_ret_t81 = y_v81601;
  }
  return ifte_ret_t81;
}

tll_ptr lam_fun_t83(tll_ptr y_v81604, tll_env env) {
  tll_ptr call_ret_t82;
  call_ret_t82 = addn_i10(env[0], y_v81604);
  return call_ret_t82;
}

tll_ptr lam_fun_t85(tll_ptr x_v81602, tll_env env) {
  tll_ptr lam_clo_t84;
  instr_clo(&lam_clo_t84, &lam_fun_t83, 1, x_v81602);
  return lam_clo_t84;
}

tll_ptr subn_i11(tll_ptr x_v81605, tll_ptr y_v81606) {
  tll_ptr add_ret_t89; tll_ptr call_ret_t87; tll_ptr call_ret_t88;
  tll_ptr ifte_ret_t90;
  if (y_v81606) {
    call_ret_t88 = pred_i9(x_v81605);
    add_ret_t89 = y_v81606 - 1;
    call_ret_t87 = subn_i11(call_ret_t88, add_ret_t89);
    ifte_ret_t90 = call_ret_t87;
  }
  else {
    ifte_ret_t90 = x_v81605;
  }
  return ifte_ret_t90;
}

tll_ptr lam_fun_t92(tll_ptr y_v81609, tll_env env) {
  tll_ptr call_ret_t91;
  call_ret_t91 = subn_i11(env[0], y_v81609);
  return call_ret_t91;
}

tll_ptr lam_fun_t94(tll_ptr x_v81607, tll_env env) {
  tll_ptr lam_clo_t93;
  instr_clo(&lam_clo_t93, &lam_fun_t92, 1, x_v81607);
  return lam_clo_t93;
}

tll_ptr muln_i12(tll_ptr x_v81610, tll_ptr y_v81611) {
  tll_ptr add_ret_t98; tll_ptr call_ret_t96; tll_ptr call_ret_t97;
  tll_ptr ifte_ret_t99;
  if (x_v81610) {
    add_ret_t98 = x_v81610 - 1;
    call_ret_t97 = muln_i12(add_ret_t98, y_v81611);
    call_ret_t96 = addn_i10(y_v81611, call_ret_t97);
    ifte_ret_t99 = call_ret_t96;
  }
  else {
    ifte_ret_t99 = (tll_ptr)0;
  }
  return ifte_ret_t99;
}

tll_ptr lam_fun_t101(tll_ptr y_v81614, tll_env env) {
  tll_ptr call_ret_t100;
  call_ret_t100 = muln_i12(env[0], y_v81614);
  return call_ret_t100;
}

tll_ptr lam_fun_t103(tll_ptr x_v81612, tll_env env) {
  tll_ptr lam_clo_t102;
  instr_clo(&lam_clo_t102, &lam_fun_t101, 1, x_v81612);
  return lam_clo_t102;
}

tll_ptr divn_i13(tll_ptr x_v81615, tll_ptr y_v81616) {
  tll_ptr add_ret_t108; tll_ptr call_ret_t105; tll_ptr call_ret_t106;
  tll_ptr call_ret_t107; tll_ptr ifte_ret_t109;
  call_ret_t105 = ltn_i6(x_v81615, y_v81616);
  if (call_ret_t105) {
    ifte_ret_t109 = (tll_ptr)0;
  }
  else {
    call_ret_t107 = subn_i11(x_v81615, y_v81616);
    call_ret_t106 = divn_i13(call_ret_t107, y_v81616);
    add_ret_t108 = call_ret_t106 + 1;
    ifte_ret_t109 = add_ret_t108;
  }
  return ifte_ret_t109;
}

tll_ptr lam_fun_t111(tll_ptr y_v81619, tll_env env) {
  tll_ptr call_ret_t110;
  call_ret_t110 = divn_i13(env[0], y_v81619);
  return call_ret_t110;
}

tll_ptr lam_fun_t113(tll_ptr x_v81617, tll_env env) {
  tll_ptr lam_clo_t112;
  instr_clo(&lam_clo_t112, &lam_fun_t111, 1, x_v81617);
  return lam_clo_t112;
}

tll_ptr modn_i14(tll_ptr x_v81620, tll_ptr y_v81621) {
  tll_ptr call_ret_t115; tll_ptr call_ret_t116; tll_ptr call_ret_t117;
  call_ret_t117 = divn_i13(x_v81620, y_v81621);
  call_ret_t116 = muln_i12(call_ret_t117, y_v81621);
  call_ret_t115 = subn_i11(x_v81620, call_ret_t116);
  return call_ret_t115;
}

tll_ptr lam_fun_t119(tll_ptr y_v81624, tll_env env) {
  tll_ptr call_ret_t118;
  call_ret_t118 = modn_i14(env[0], y_v81624);
  return call_ret_t118;
}

tll_ptr lam_fun_t121(tll_ptr x_v81622, tll_env env) {
  tll_ptr lam_clo_t120;
  instr_clo(&lam_clo_t120, &lam_fun_t119, 1, x_v81622);
  return lam_clo_t120;
}

tll_ptr cats_i15(tll_ptr s1_v81625, tll_ptr s2_v81626) {
  tll_ptr String_t125; tll_ptr c_v81627; tll_ptr call_ret_t124;
  tll_ptr s1_v81628; tll_ptr switch_ret_t123;
  switch(((tll_node)s1_v81625)->tag) {
    case 2:
      switch_ret_t123 = s2_v81626;
      break;
    case 3:
      c_v81627 = ((tll_node)s1_v81625)->data[0];
      s1_v81628 = ((tll_node)s1_v81625)->data[1];
      call_ret_t124 = cats_i15(s1_v81628, s2_v81626);
      instr_struct(&String_t125, 3, 2, c_v81627, call_ret_t124);
      switch_ret_t123 = String_t125;
      break;
  }
  return switch_ret_t123;
}

tll_ptr lam_fun_t127(tll_ptr s2_v81631, tll_env env) {
  tll_ptr call_ret_t126;
  call_ret_t126 = cats_i15(env[0], s2_v81631);
  return call_ret_t126;
}

tll_ptr lam_fun_t129(tll_ptr s1_v81629, tll_env env) {
  tll_ptr lam_clo_t128;
  instr_clo(&lam_clo_t128, &lam_fun_t127, 1, s1_v81629);
  return lam_clo_t128;
}

tll_ptr strlen_i16(tll_ptr s_v81632) {
  tll_ptr __v81633; tll_ptr add_ret_t133; tll_ptr call_ret_t132;
  tll_ptr s_v81634; tll_ptr switch_ret_t131;
  switch(((tll_node)s_v81632)->tag) {
    case 2:
      switch_ret_t131 = (tll_ptr)0;
      break;
    case 3:
      __v81633 = ((tll_node)s_v81632)->data[0];
      s_v81634 = ((tll_node)s_v81632)->data[1];
      call_ret_t132 = strlen_i16(s_v81634);
      add_ret_t133 = call_ret_t132 + 1;
      switch_ret_t131 = add_ret_t133;
      break;
  }
  return switch_ret_t131;
}

tll_ptr lam_fun_t135(tll_ptr s_v81635, tll_env env) {
  tll_ptr call_ret_t134;
  call_ret_t134 = strlen_i16(s_v81635);
  return call_ret_t134;
}

tll_ptr lenUU_i40(tll_ptr A_v81636, tll_ptr xs_v81637) {
  tll_ptr add_ret_t142; tll_ptr call_ret_t140; tll_ptr consUU_t143;
  tll_ptr n_v81640; tll_ptr nilUU_t138; tll_ptr pair_struct_t139;
  tll_ptr pair_struct_t144; tll_ptr switch_ret_t137; tll_ptr switch_ret_t141;
  tll_ptr x_v81638; tll_ptr xs_v81639; tll_ptr xs_v81641;
  switch(((tll_node)xs_v81637)->tag) {
    case 13:
      instr_struct(&nilUU_t138, 13, 0);
      instr_struct(&pair_struct_t139, 0, 2, (tll_ptr)0, nilUU_t138);
      switch_ret_t137 = pair_struct_t139;
      break;
    case 14:
      x_v81638 = ((tll_node)xs_v81637)->data[0];
      xs_v81639 = ((tll_node)xs_v81637)->data[1];
      call_ret_t140 = lenUU_i40(0, xs_v81639);
      switch(((tll_node)call_ret_t140)->tag) {
        case 0:
          n_v81640 = ((tll_node)call_ret_t140)->data[0];
          xs_v81641 = ((tll_node)call_ret_t140)->data[1];
          instr_free_struct(call_ret_t140);
          add_ret_t142 = n_v81640 + 1;
          instr_struct(&consUU_t143, 14, 2, x_v81638, xs_v81641);
          instr_struct(&pair_struct_t144, 0, 2, add_ret_t142, consUU_t143);
          switch_ret_t141 = pair_struct_t144;
          break;
      }
      switch_ret_t137 = switch_ret_t141;
      break;
  }
  return switch_ret_t137;
}

tll_ptr lam_fun_t146(tll_ptr xs_v81644, tll_env env) {
  tll_ptr call_ret_t145;
  call_ret_t145 = lenUU_i40(env[0], xs_v81644);
  return call_ret_t145;
}

tll_ptr lam_fun_t148(tll_ptr A_v81642, tll_env env) {
  tll_ptr lam_clo_t147;
  instr_clo(&lam_clo_t147, &lam_fun_t146, 1, A_v81642);
  return lam_clo_t147;
}

tll_ptr lenUL_i39(tll_ptr A_v81645, tll_ptr xs_v81646) {
  tll_ptr add_ret_t155; tll_ptr call_ret_t153; tll_ptr consUL_t156;
  tll_ptr n_v81649; tll_ptr nilUL_t151; tll_ptr pair_struct_t152;
  tll_ptr pair_struct_t157; tll_ptr switch_ret_t150; tll_ptr switch_ret_t154;
  tll_ptr x_v81647; tll_ptr xs_v81648; tll_ptr xs_v81650;
  switch(((tll_node)xs_v81646)->tag) {
    case 11:
      instr_free_struct(xs_v81646);
      instr_struct(&nilUL_t151, 11, 0);
      instr_struct(&pair_struct_t152, 0, 2, (tll_ptr)0, nilUL_t151);
      switch_ret_t150 = pair_struct_t152;
      break;
    case 12:
      x_v81647 = ((tll_node)xs_v81646)->data[0];
      xs_v81648 = ((tll_node)xs_v81646)->data[1];
      instr_free_struct(xs_v81646);
      call_ret_t153 = lenUL_i39(0, xs_v81648);
      switch(((tll_node)call_ret_t153)->tag) {
        case 0:
          n_v81649 = ((tll_node)call_ret_t153)->data[0];
          xs_v81650 = ((tll_node)call_ret_t153)->data[1];
          instr_free_struct(call_ret_t153);
          add_ret_t155 = n_v81649 + 1;
          instr_struct(&consUL_t156, 12, 2, x_v81647, xs_v81650);
          instr_struct(&pair_struct_t157, 0, 2, add_ret_t155, consUL_t156);
          switch_ret_t154 = pair_struct_t157;
          break;
      }
      switch_ret_t150 = switch_ret_t154;
      break;
  }
  return switch_ret_t150;
}

tll_ptr lam_fun_t159(tll_ptr xs_v81653, tll_env env) {
  tll_ptr call_ret_t158;
  call_ret_t158 = lenUL_i39(env[0], xs_v81653);
  return call_ret_t158;
}

tll_ptr lam_fun_t161(tll_ptr A_v81651, tll_env env) {
  tll_ptr lam_clo_t160;
  instr_clo(&lam_clo_t160, &lam_fun_t159, 1, A_v81651);
  return lam_clo_t160;
}

tll_ptr lenLL_i37(tll_ptr A_v81654, tll_ptr xs_v81655) {
  tll_ptr add_ret_t168; tll_ptr call_ret_t166; tll_ptr consLL_t169;
  tll_ptr n_v81658; tll_ptr nilLL_t164; tll_ptr pair_struct_t165;
  tll_ptr pair_struct_t170; tll_ptr switch_ret_t163; tll_ptr switch_ret_t167;
  tll_ptr x_v81656; tll_ptr xs_v81657; tll_ptr xs_v81659;
  switch(((tll_node)xs_v81655)->tag) {
    case 7:
      instr_free_struct(xs_v81655);
      instr_struct(&nilLL_t164, 7, 0);
      instr_struct(&pair_struct_t165, 0, 2, (tll_ptr)0, nilLL_t164);
      switch_ret_t163 = pair_struct_t165;
      break;
    case 8:
      x_v81656 = ((tll_node)xs_v81655)->data[0];
      xs_v81657 = ((tll_node)xs_v81655)->data[1];
      instr_free_struct(xs_v81655);
      call_ret_t166 = lenLL_i37(0, xs_v81657);
      switch(((tll_node)call_ret_t166)->tag) {
        case 0:
          n_v81658 = ((tll_node)call_ret_t166)->data[0];
          xs_v81659 = ((tll_node)call_ret_t166)->data[1];
          instr_free_struct(call_ret_t166);
          add_ret_t168 = n_v81658 + 1;
          instr_struct(&consLL_t169, 8, 2, x_v81656, xs_v81659);
          instr_struct(&pair_struct_t170, 0, 2, add_ret_t168, consLL_t169);
          switch_ret_t167 = pair_struct_t170;
          break;
      }
      switch_ret_t163 = switch_ret_t167;
      break;
  }
  return switch_ret_t163;
}

tll_ptr lam_fun_t172(tll_ptr xs_v81662, tll_env env) {
  tll_ptr call_ret_t171;
  call_ret_t171 = lenLL_i37(env[0], xs_v81662);
  return call_ret_t171;
}

tll_ptr lam_fun_t174(tll_ptr A_v81660, tll_env env) {
  tll_ptr lam_clo_t173;
  instr_clo(&lam_clo_t173, &lam_fun_t172, 1, A_v81660);
  return lam_clo_t173;
}

tll_ptr appendUU_i44(tll_ptr A_v81663, tll_ptr xs_v81664, tll_ptr ys_v81665) {
  tll_ptr call_ret_t177; tll_ptr consUU_t178; tll_ptr switch_ret_t176;
  tll_ptr x_v81666; tll_ptr xs_v81667;
  switch(((tll_node)xs_v81664)->tag) {
    case 13:
      switch_ret_t176 = ys_v81665;
      break;
    case 14:
      x_v81666 = ((tll_node)xs_v81664)->data[0];
      xs_v81667 = ((tll_node)xs_v81664)->data[1];
      call_ret_t177 = appendUU_i44(0, xs_v81667, ys_v81665);
      instr_struct(&consUU_t178, 14, 2, x_v81666, call_ret_t177);
      switch_ret_t176 = consUU_t178;
      break;
  }
  return switch_ret_t176;
}

tll_ptr lam_fun_t180(tll_ptr ys_v81673, tll_env env) {
  tll_ptr call_ret_t179;
  call_ret_t179 = appendUU_i44(env[1], env[0], ys_v81673);
  return call_ret_t179;
}

tll_ptr lam_fun_t182(tll_ptr xs_v81671, tll_env env) {
  tll_ptr lam_clo_t181;
  instr_clo(&lam_clo_t181, &lam_fun_t180, 2, xs_v81671, env[0]);
  return lam_clo_t181;
}

tll_ptr lam_fun_t184(tll_ptr A_v81668, tll_env env) {
  tll_ptr lam_clo_t183;
  instr_clo(&lam_clo_t183, &lam_fun_t182, 1, A_v81668);
  return lam_clo_t183;
}

tll_ptr appendUL_i43(tll_ptr A_v81674, tll_ptr xs_v81675, tll_ptr ys_v81676) {
  tll_ptr call_ret_t187; tll_ptr consUL_t188; tll_ptr switch_ret_t186;
  tll_ptr x_v81677; tll_ptr xs_v81678;
  switch(((tll_node)xs_v81675)->tag) {
    case 11:
      instr_free_struct(xs_v81675);
      switch_ret_t186 = ys_v81676;
      break;
    case 12:
      x_v81677 = ((tll_node)xs_v81675)->data[0];
      xs_v81678 = ((tll_node)xs_v81675)->data[1];
      instr_free_struct(xs_v81675);
      call_ret_t187 = appendUL_i43(0, xs_v81678, ys_v81676);
      instr_struct(&consUL_t188, 12, 2, x_v81677, call_ret_t187);
      switch_ret_t186 = consUL_t188;
      break;
  }
  return switch_ret_t186;
}

tll_ptr lam_fun_t190(tll_ptr ys_v81684, tll_env env) {
  tll_ptr call_ret_t189;
  call_ret_t189 = appendUL_i43(env[1], env[0], ys_v81684);
  return call_ret_t189;
}

tll_ptr lam_fun_t192(tll_ptr xs_v81682, tll_env env) {
  tll_ptr lam_clo_t191;
  instr_clo(&lam_clo_t191, &lam_fun_t190, 2, xs_v81682, env[0]);
  return lam_clo_t191;
}

tll_ptr lam_fun_t194(tll_ptr A_v81679, tll_env env) {
  tll_ptr lam_clo_t193;
  instr_clo(&lam_clo_t193, &lam_fun_t192, 1, A_v81679);
  return lam_clo_t193;
}

tll_ptr appendLL_i41(tll_ptr A_v81685, tll_ptr xs_v81686, tll_ptr ys_v81687) {
  tll_ptr call_ret_t197; tll_ptr consLL_t198; tll_ptr switch_ret_t196;
  tll_ptr x_v81688; tll_ptr xs_v81689;
  switch(((tll_node)xs_v81686)->tag) {
    case 7:
      instr_free_struct(xs_v81686);
      switch_ret_t196 = ys_v81687;
      break;
    case 8:
      x_v81688 = ((tll_node)xs_v81686)->data[0];
      xs_v81689 = ((tll_node)xs_v81686)->data[1];
      instr_free_struct(xs_v81686);
      call_ret_t197 = appendLL_i41(0, xs_v81689, ys_v81687);
      instr_struct(&consLL_t198, 8, 2, x_v81688, call_ret_t197);
      switch_ret_t196 = consLL_t198;
      break;
  }
  return switch_ret_t196;
}

tll_ptr lam_fun_t200(tll_ptr ys_v81695, tll_env env) {
  tll_ptr call_ret_t199;
  call_ret_t199 = appendLL_i41(env[1], env[0], ys_v81695);
  return call_ret_t199;
}

tll_ptr lam_fun_t202(tll_ptr xs_v81693, tll_env env) {
  tll_ptr lam_clo_t201;
  instr_clo(&lam_clo_t201, &lam_fun_t200, 2, xs_v81693, env[0]);
  return lam_clo_t201;
}

tll_ptr lam_fun_t204(tll_ptr A_v81690, tll_env env) {
  tll_ptr lam_clo_t203;
  instr_clo(&lam_clo_t203, &lam_fun_t202, 1, A_v81690);
  return lam_clo_t203;
}

tll_ptr lam_fun_t211(tll_ptr __v81697, tll_env env) {
  tll_ptr ch_v81702; tll_ptr ch_v81703; tll_ptr prim_ch_t208;
  tll_ptr recv_msg_t206; tll_ptr s_v81701; tll_ptr send_ch_t207;
  tll_ptr send_ch_t210; tll_ptr switch_ret_t209;
  instr_open(&prim_ch_t208, &proc_stdin);
  instr_send(&send_ch_t207, prim_ch_t208, (tll_ptr)1);
  instr_recv(&recv_msg_t206, send_ch_t207);
  switch(((tll_node)recv_msg_t206)->tag) {
    case 0:
      s_v81701 = ((tll_node)recv_msg_t206)->data[0];
      ch_v81702 = ((tll_node)recv_msg_t206)->data[1];
      instr_free_struct(recv_msg_t206);
      instr_send(&send_ch_t210, ch_v81702, (tll_ptr)0);
      ch_v81703 = send_ch_t210;
      switch_ret_t209 = s_v81701;
      break;
  }
  return switch_ret_t209;
}

tll_ptr readline_i25(tll_ptr __v81696) {
  tll_ptr lam_clo_t212;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  return lam_clo_t212;
}

tll_ptr lam_fun_t214(tll_ptr __v81704, tll_env env) {
  tll_ptr call_ret_t213;
  call_ret_t213 = readline_i25(__v81704);
  return call_ret_t213;
}

tll_ptr lam_fun_t220(tll_ptr __v81706, tll_env env) {
  tll_ptr ch_v81708; tll_ptr prim_ch_t219; tll_ptr send_ch_t216;
  tll_ptr send_ch_t217; tll_ptr send_ch_t218;
  instr_open(&prim_ch_t219, &proc_stdout);
  instr_send(&send_ch_t218, prim_ch_t219, (tll_ptr)1);
  instr_send(&send_ch_t217, send_ch_t218, env[0]);
  instr_send(&send_ch_t216, send_ch_t217, (tll_ptr)0);
  ch_v81708 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v81705) {
  tll_ptr lam_clo_t221;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 1, s_v81705);
  return lam_clo_t221;
}

tll_ptr lam_fun_t223(tll_ptr s_v81709, tll_env env) {
  tll_ptr call_ret_t222;
  call_ret_t222 = print_i26(s_v81709);
  return call_ret_t222;
}

tll_ptr lam_fun_t229(tll_ptr __v81711, tll_env env) {
  tll_ptr ch_v81713; tll_ptr prim_ch_t228; tll_ptr send_ch_t225;
  tll_ptr send_ch_t226; tll_ptr send_ch_t227;
  instr_open(&prim_ch_t228, &proc_stderr);
  instr_send(&send_ch_t227, prim_ch_t228, (tll_ptr)1);
  instr_send(&send_ch_t226, send_ch_t227, env[0]);
  instr_send(&send_ch_t225, send_ch_t226, (tll_ptr)0);
  ch_v81713 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v81710) {
  tll_ptr lam_clo_t230;
  instr_clo(&lam_clo_t230, &lam_fun_t229, 1, s_v81710);
  return lam_clo_t230;
}

tll_ptr lam_fun_t232(tll_ptr s_v81714, tll_env env) {
  tll_ptr call_ret_t231;
  call_ret_t231 = prerr_i27(s_v81714);
  return call_ret_t231;
}

tll_ptr splitU_i46(tll_ptr zs_v81715) {
  tll_ptr call_ret_t243; tll_ptr consUU_t240; tll_ptr consUU_t245;
  tll_ptr consUU_t246; tll_ptr nilUU_t235; tll_ptr nilUU_t236;
  tll_ptr nilUU_t239; tll_ptr nilUU_t241; tll_ptr pair_struct_t237;
  tll_ptr pair_struct_t242; tll_ptr pair_struct_t247;
  tll_ptr switch_ret_t234; tll_ptr switch_ret_t238; tll_ptr switch_ret_t244;
  tll_ptr x_v81716; tll_ptr xs_v81720; tll_ptr y_v81718; tll_ptr ys_v81721;
  tll_ptr zs_v81717; tll_ptr zs_v81719;
  switch(((tll_node)zs_v81715)->tag) {
    case 13:
      instr_struct(&nilUU_t235, 13, 0);
      instr_struct(&nilUU_t236, 13, 0);
      instr_struct(&pair_struct_t237, 0, 2, nilUU_t235, nilUU_t236);
      switch_ret_t234 = pair_struct_t237;
      break;
    case 14:
      x_v81716 = ((tll_node)zs_v81715)->data[0];
      zs_v81717 = ((tll_node)zs_v81715)->data[1];
      switch(((tll_node)zs_v81717)->tag) {
        case 13:
          instr_struct(&nilUU_t239, 13, 0);
          instr_struct(&consUU_t240, 14, 2, x_v81716, nilUU_t239);
          instr_struct(&nilUU_t241, 13, 0);
          instr_struct(&pair_struct_t242, 0, 2, consUU_t240, nilUU_t241);
          switch_ret_t238 = pair_struct_t242;
          break;
        case 14:
          y_v81718 = ((tll_node)zs_v81717)->data[0];
          zs_v81719 = ((tll_node)zs_v81717)->data[1];
          call_ret_t243 = splitU_i46(zs_v81719);
          switch(((tll_node)call_ret_t243)->tag) {
            case 0:
              xs_v81720 = ((tll_node)call_ret_t243)->data[0];
              ys_v81721 = ((tll_node)call_ret_t243)->data[1];
              instr_free_struct(call_ret_t243);
              instr_struct(&consUU_t245, 14, 2, x_v81716, xs_v81720);
              instr_struct(&consUU_t246, 14, 2, y_v81718, ys_v81721);
              instr_struct(&pair_struct_t247, 0, 2, consUU_t245, consUU_t246);
              switch_ret_t244 = pair_struct_t247;
              break;
          }
          switch_ret_t238 = switch_ret_t244;
          break;
      }
      switch_ret_t234 = switch_ret_t238;
      break;
  }
  return switch_ret_t234;
}

tll_ptr lam_fun_t249(tll_ptr zs_v81722, tll_env env) {
  tll_ptr call_ret_t248;
  call_ret_t248 = splitU_i46(zs_v81722);
  return call_ret_t248;
}

tll_ptr splitL_i45(tll_ptr zs_v81723) {
  tll_ptr call_ret_t260; tll_ptr consUL_t257; tll_ptr consUL_t262;
  tll_ptr consUL_t263; tll_ptr nilUL_t252; tll_ptr nilUL_t253;
  tll_ptr nilUL_t256; tll_ptr nilUL_t258; tll_ptr pair_struct_t254;
  tll_ptr pair_struct_t259; tll_ptr pair_struct_t264;
  tll_ptr switch_ret_t251; tll_ptr switch_ret_t255; tll_ptr switch_ret_t261;
  tll_ptr x_v81724; tll_ptr xs_v81728; tll_ptr y_v81726; tll_ptr ys_v81729;
  tll_ptr zs_v81725; tll_ptr zs_v81727;
  switch(((tll_node)zs_v81723)->tag) {
    case 11:
      instr_free_struct(zs_v81723);
      instr_struct(&nilUL_t252, 11, 0);
      instr_struct(&nilUL_t253, 11, 0);
      instr_struct(&pair_struct_t254, 0, 2, nilUL_t252, nilUL_t253);
      switch_ret_t251 = pair_struct_t254;
      break;
    case 12:
      x_v81724 = ((tll_node)zs_v81723)->data[0];
      zs_v81725 = ((tll_node)zs_v81723)->data[1];
      instr_free_struct(zs_v81723);
      switch(((tll_node)zs_v81725)->tag) {
        case 11:
          instr_free_struct(zs_v81725);
          instr_struct(&nilUL_t256, 11, 0);
          instr_struct(&consUL_t257, 12, 2, x_v81724, nilUL_t256);
          instr_struct(&nilUL_t258, 11, 0);
          instr_struct(&pair_struct_t259, 0, 2, consUL_t257, nilUL_t258);
          switch_ret_t255 = pair_struct_t259;
          break;
        case 12:
          y_v81726 = ((tll_node)zs_v81725)->data[0];
          zs_v81727 = ((tll_node)zs_v81725)->data[1];
          instr_free_struct(zs_v81725);
          call_ret_t260 = splitL_i45(zs_v81727);
          switch(((tll_node)call_ret_t260)->tag) {
            case 0:
              xs_v81728 = ((tll_node)call_ret_t260)->data[0];
              ys_v81729 = ((tll_node)call_ret_t260)->data[1];
              instr_free_struct(call_ret_t260);
              instr_struct(&consUL_t262, 12, 2, x_v81724, xs_v81728);
              instr_struct(&consUL_t263, 12, 2, y_v81726, ys_v81729);
              instr_struct(&pair_struct_t264, 0, 2, consUL_t262, consUL_t263);
              switch_ret_t261 = pair_struct_t264;
              break;
          }
          switch_ret_t255 = switch_ret_t261;
          break;
      }
      switch_ret_t251 = switch_ret_t255;
      break;
  }
  return switch_ret_t251;
}

tll_ptr lam_fun_t266(tll_ptr zs_v81730, tll_env env) {
  tll_ptr call_ret_t265;
  call_ret_t265 = splitL_i45(zs_v81730);
  return call_ret_t265;
}

tll_ptr mergeU_i48(tll_ptr xs_v81731, tll_ptr ys_v81732) {
  tll_ptr call_ret_t271; tll_ptr call_ret_t272; tll_ptr call_ret_t275;
  tll_ptr consUU_t270; tll_ptr consUU_t273; tll_ptr consUU_t274;
  tll_ptr consUU_t276; tll_ptr consUU_t277; tll_ptr ifte_ret_t278;
  tll_ptr switch_ret_t268; tll_ptr switch_ret_t269; tll_ptr x_v81733;
  tll_ptr xs0_v81734; tll_ptr y_v81735; tll_ptr ys0_v81736;
  switch(((tll_node)xs_v81731)->tag) {
    case 13:
      switch_ret_t268 = ys_v81732;
      break;
    case 14:
      x_v81733 = ((tll_node)xs_v81731)->data[0];
      xs0_v81734 = ((tll_node)xs_v81731)->data[1];
      switch(((tll_node)ys_v81732)->tag) {
        case 13:
          instr_struct(&consUU_t270, 14, 2, x_v81733, xs0_v81734);
          switch_ret_t269 = consUU_t270;
          break;
        case 14:
          y_v81735 = ((tll_node)ys_v81732)->data[0];
          ys0_v81736 = ((tll_node)ys_v81732)->data[1];
          call_ret_t271 = lten_i4(x_v81733, y_v81735);
          if (call_ret_t271) {
            instr_struct(&consUU_t273, 14, 2, y_v81735, ys0_v81736);
            call_ret_t272 = mergeU_i48(xs0_v81734, consUU_t273);
            instr_struct(&consUU_t274, 14, 2, x_v81733, call_ret_t272);
            ifte_ret_t278 = consUU_t274;
          }
          else {
            instr_struct(&consUU_t276, 14, 2, x_v81733, xs0_v81734);
            call_ret_t275 = mergeU_i48(consUU_t276, ys0_v81736);
            instr_struct(&consUU_t277, 14, 2, y_v81735, call_ret_t275);
            ifte_ret_t278 = consUU_t277;
          }
          switch_ret_t269 = ifte_ret_t278;
          break;
      }
      switch_ret_t268 = switch_ret_t269;
      break;
  }
  return switch_ret_t268;
}

tll_ptr lam_fun_t280(tll_ptr ys_v81739, tll_env env) {
  tll_ptr call_ret_t279;
  call_ret_t279 = mergeU_i48(env[0], ys_v81739);
  return call_ret_t279;
}

tll_ptr lam_fun_t282(tll_ptr xs_v81737, tll_env env) {
  tll_ptr lam_clo_t281;
  instr_clo(&lam_clo_t281, &lam_fun_t280, 1, xs_v81737);
  return lam_clo_t281;
}

tll_ptr mergeL_i47(tll_ptr xs_v81740, tll_ptr ys_v81741) {
  tll_ptr call_ret_t287; tll_ptr call_ret_t288; tll_ptr call_ret_t291;
  tll_ptr consUL_t286; tll_ptr consUL_t289; tll_ptr consUL_t290;
  tll_ptr consUL_t292; tll_ptr consUL_t293; tll_ptr ifte_ret_t294;
  tll_ptr switch_ret_t284; tll_ptr switch_ret_t285; tll_ptr x_v81742;
  tll_ptr xs0_v81743; tll_ptr y_v81744; tll_ptr ys0_v81745;
  switch(((tll_node)xs_v81740)->tag) {
    case 11:
      instr_free_struct(xs_v81740);
      switch_ret_t284 = ys_v81741;
      break;
    case 12:
      x_v81742 = ((tll_node)xs_v81740)->data[0];
      xs0_v81743 = ((tll_node)xs_v81740)->data[1];
      instr_free_struct(xs_v81740);
      switch(((tll_node)ys_v81741)->tag) {
        case 11:
          instr_free_struct(ys_v81741);
          instr_struct(&consUL_t286, 12, 2, x_v81742, xs0_v81743);
          switch_ret_t285 = consUL_t286;
          break;
        case 12:
          y_v81744 = ((tll_node)ys_v81741)->data[0];
          ys0_v81745 = ((tll_node)ys_v81741)->data[1];
          instr_free_struct(ys_v81741);
          call_ret_t287 = lten_i4(x_v81742, y_v81744);
          if (call_ret_t287) {
            instr_struct(&consUL_t289, 12, 2, y_v81744, ys0_v81745);
            call_ret_t288 = mergeL_i47(xs0_v81743, consUL_t289);
            instr_struct(&consUL_t290, 12, 2, x_v81742, call_ret_t288);
            ifte_ret_t294 = consUL_t290;
          }
          else {
            instr_struct(&consUL_t292, 12, 2, x_v81742, xs0_v81743);
            call_ret_t291 = mergeL_i47(consUL_t292, ys0_v81745);
            instr_struct(&consUL_t293, 12, 2, y_v81744, call_ret_t291);
            ifte_ret_t294 = consUL_t293;
          }
          switch_ret_t285 = ifte_ret_t294;
          break;
      }
      switch_ret_t284 = switch_ret_t285;
      break;
  }
  return switch_ret_t284;
}

tll_ptr lam_fun_t296(tll_ptr ys_v81748, tll_env env) {
  tll_ptr call_ret_t295;
  call_ret_t295 = mergeL_i47(env[0], ys_v81748);
  return call_ret_t295;
}

tll_ptr lam_fun_t298(tll_ptr xs_v81746, tll_env env) {
  tll_ptr lam_clo_t297;
  instr_clo(&lam_clo_t297, &lam_fun_t296, 1, xs_v81746);
  return lam_clo_t297;
}

tll_ptr msortU_i50(tll_ptr zs_v81749) {
  tll_ptr call_ret_t305; tll_ptr call_ret_t309; tll_ptr call_ret_t310;
  tll_ptr call_ret_t311; tll_ptr consUU_t304; tll_ptr consUU_t306;
  tll_ptr consUU_t307; tll_ptr nilUU_t301; tll_ptr nilUU_t303;
  tll_ptr switch_ret_t300; tll_ptr switch_ret_t302; tll_ptr switch_ret_t308;
  tll_ptr x_v81750; tll_ptr xs_v81754; tll_ptr y_v81752; tll_ptr ys_v81755;
  tll_ptr zs_v81751; tll_ptr zs_v81753;
  switch(((tll_node)zs_v81749)->tag) {
    case 13:
      instr_struct(&nilUU_t301, 13, 0);
      switch_ret_t300 = nilUU_t301;
      break;
    case 14:
      x_v81750 = ((tll_node)zs_v81749)->data[0];
      zs_v81751 = ((tll_node)zs_v81749)->data[1];
      switch(((tll_node)zs_v81751)->tag) {
        case 13:
          instr_struct(&nilUU_t303, 13, 0);
          instr_struct(&consUU_t304, 14, 2, x_v81750, nilUU_t303);
          switch_ret_t302 = consUU_t304;
          break;
        case 14:
          y_v81752 = ((tll_node)zs_v81751)->data[0];
          zs_v81753 = ((tll_node)zs_v81751)->data[1];
          instr_struct(&consUU_t306, 14, 2, y_v81752, zs_v81753);
          instr_struct(&consUU_t307, 14, 2, x_v81750, consUU_t306);
          call_ret_t305 = splitU_i46(consUU_t307);
          switch(((tll_node)call_ret_t305)->tag) {
            case 0:
              xs_v81754 = ((tll_node)call_ret_t305)->data[0];
              ys_v81755 = ((tll_node)call_ret_t305)->data[1];
              instr_free_struct(call_ret_t305);
              call_ret_t310 = msortU_i50(xs_v81754);
              call_ret_t311 = msortU_i50(ys_v81755);
              call_ret_t309 = mergeU_i48(call_ret_t310, call_ret_t311);
              switch_ret_t308 = call_ret_t309;
              break;
          }
          switch_ret_t302 = switch_ret_t308;
          break;
      }
      switch_ret_t300 = switch_ret_t302;
      break;
  }
  return switch_ret_t300;
}

tll_ptr lam_fun_t313(tll_ptr zs_v81756, tll_env env) {
  tll_ptr call_ret_t312;
  call_ret_t312 = msortU_i50(zs_v81756);
  return call_ret_t312;
}

tll_ptr msortL_i49(tll_ptr zs_v81757) {
  tll_ptr call_ret_t320; tll_ptr call_ret_t324; tll_ptr call_ret_t325;
  tll_ptr call_ret_t326; tll_ptr consUL_t319; tll_ptr consUL_t321;
  tll_ptr consUL_t322; tll_ptr nilUL_t316; tll_ptr nilUL_t318;
  tll_ptr switch_ret_t315; tll_ptr switch_ret_t317; tll_ptr switch_ret_t323;
  tll_ptr x_v81758; tll_ptr xs_v81762; tll_ptr y_v81760; tll_ptr ys_v81763;
  tll_ptr zs_v81759; tll_ptr zs_v81761;
  switch(((tll_node)zs_v81757)->tag) {
    case 11:
      instr_free_struct(zs_v81757);
      instr_struct(&nilUL_t316, 11, 0);
      switch_ret_t315 = nilUL_t316;
      break;
    case 12:
      x_v81758 = ((tll_node)zs_v81757)->data[0];
      zs_v81759 = ((tll_node)zs_v81757)->data[1];
      instr_free_struct(zs_v81757);
      switch(((tll_node)zs_v81759)->tag) {
        case 11:
          instr_free_struct(zs_v81759);
          instr_struct(&nilUL_t318, 11, 0);
          instr_struct(&consUL_t319, 12, 2, x_v81758, nilUL_t318);
          switch_ret_t317 = consUL_t319;
          break;
        case 12:
          y_v81760 = ((tll_node)zs_v81759)->data[0];
          zs_v81761 = ((tll_node)zs_v81759)->data[1];
          instr_free_struct(zs_v81759);
          instr_struct(&consUL_t321, 12, 2, y_v81760, zs_v81761);
          instr_struct(&consUL_t322, 12, 2, x_v81758, consUL_t321);
          call_ret_t320 = splitL_i45(consUL_t322);
          switch(((tll_node)call_ret_t320)->tag) {
            case 0:
              xs_v81762 = ((tll_node)call_ret_t320)->data[0];
              ys_v81763 = ((tll_node)call_ret_t320)->data[1];
              instr_free_struct(call_ret_t320);
              call_ret_t325 = msortL_i49(xs_v81762);
              call_ret_t326 = msortL_i49(ys_v81763);
              call_ret_t324 = mergeL_i47(call_ret_t325, call_ret_t326);
              switch_ret_t323 = call_ret_t324;
              break;
          }
          switch_ret_t317 = switch_ret_t323;
          break;
      }
      switch_ret_t315 = switch_ret_t317;
      break;
  }
  return switch_ret_t315;
}

tll_ptr lam_fun_t328(tll_ptr zs_v81764, tll_env env) {
  tll_ptr call_ret_t327;
  call_ret_t327 = msortL_i49(zs_v81764);
  return call_ret_t327;
}

tll_ptr lam_fun_t335(tll_ptr __v81769, tll_env env) {
  tll_ptr UniqU_t334; tll_ptr c_v81771; tll_ptr nilUU_t333;
  tll_ptr send_ch_t332;
  instr_struct(&nilUU_t333, 13, 0);
  instr_struct(&UniqU_t334, 16, 2, nilUU_t333, 0);
  instr_send(&send_ch_t332, env[0], UniqU_t334);
  c_v81771 = send_ch_t332;
  return 0;
}

tll_ptr lam_fun_t342(tll_ptr __v81774, tll_env env) {
  tll_ptr UniqU_t341; tll_ptr c_v81776; tll_ptr consUU_t340;
  tll_ptr nilUU_t339; tll_ptr send_ch_t338;
  instr_struct(&nilUU_t339, 13, 0);
  instr_struct(&consUU_t340, 14, 2, env[0], nilUU_t339);
  instr_struct(&UniqU_t341, 16, 2, consUU_t340, 0);
  instr_send(&send_ch_t338, env[1], UniqU_t341);
  c_v81776 = send_ch_t338;
  return 0;
}

tll_ptr fork_fun_t351(tll_env env) {
  tll_ptr app_ret_t350; tll_ptr call_ret_t349; tll_ptr fork_ret_t353;
  call_ret_t349 = cmsort_workerU_i54(env[2], env[1], env[0]);
  instr_app(&app_ret_t350, call_ret_t349, 0);
  instr_free_clo(call_ret_t349);
  fork_ret_t353 = app_ret_t350;
  instr_free_thread(env);
  return fork_ret_t353;
}

tll_ptr fork_fun_t358(tll_env env) {
  tll_ptr app_ret_t357; tll_ptr call_ret_t356; tll_ptr fork_ret_t360;
  call_ret_t356 = cmsort_workerU_i54(env[2], env[1], env[0]);
  instr_app(&app_ret_t357, call_ret_t356, 0);
  instr_free_clo(call_ret_t356);
  fork_ret_t360 = app_ret_t357;
  instr_free_thread(env);
  return fork_ret_t360;
}

tll_ptr lam_fun_t369(tll_ptr __v81781, tll_env env) {
  tll_ptr UniqU_t366; tll_ptr __v81806; tll_ptr __v81807; tll_ptr c_v81805;
  tll_ptr call_ret_t365; tll_ptr close_tmp_t367; tll_ptr close_tmp_t368;
  tll_ptr fork_ch_t352; tll_ptr fork_ch_t359; tll_ptr msg1_v81796;
  tll_ptr msg2_v81799; tll_ptr pf1_v81802; tll_ptr pf2_v81804;
  tll_ptr r1_v81797; tll_ptr r2_v81800; tll_ptr recv_msg_t348;
  tll_ptr recv_msg_t355; tll_ptr send_ch_t364; tll_ptr switch_ret_t354;
  tll_ptr switch_ret_t361; tll_ptr switch_ret_t362; tll_ptr switch_ret_t363;
  tll_ptr xs1_v81801; tll_ptr xs2_v81803;
  instr_fork(&fork_ch_t352, &fork_fun_t351, 2, env[1], env[2]);
  instr_recv(&recv_msg_t348, fork_ch_t352);
  switch(((tll_node)recv_msg_t348)->tag) {
    case 0:
      msg1_v81796 = ((tll_node)recv_msg_t348)->data[0];
      r1_v81797 = ((tll_node)recv_msg_t348)->data[1];
      instr_free_struct(recv_msg_t348);
      instr_fork(&fork_ch_t359, &fork_fun_t358, 2, env[0], env[2]);
      instr_recv(&recv_msg_t355, fork_ch_t359);
      switch(((tll_node)recv_msg_t355)->tag) {
        case 0:
          msg2_v81799 = ((tll_node)recv_msg_t355)->data[0];
          r2_v81800 = ((tll_node)recv_msg_t355)->data[1];
          instr_free_struct(recv_msg_t355);
          switch(((tll_node)msg1_v81796)->tag) {
            case 16:
              xs1_v81801 = ((tll_node)msg1_v81796)->data[0];
              pf1_v81802 = ((tll_node)msg1_v81796)->data[1];
              switch(((tll_node)msg2_v81799)->tag) {
                case 16:
                  xs2_v81803 = ((tll_node)msg2_v81799)->data[0];
                  pf2_v81804 = ((tll_node)msg2_v81799)->data[1];
                  call_ret_t365 = mergeU_i48(xs1_v81801, xs2_v81803);
                  instr_struct(&UniqU_t366, 16, 2, call_ret_t365, 0);
                  instr_send(&send_ch_t364, env[3], UniqU_t366);
                  c_v81805 = send_ch_t364;
                  instr_close(&close_tmp_t367, r1_v81797);
                  __v81806 = close_tmp_t367;
                  instr_close(&close_tmp_t368, r2_v81800);
                  __v81807 = close_tmp_t368;
                  switch_ret_t363 = 0;
                  break;
              }
              switch_ret_t362 = switch_ret_t363;
              break;
          }
          switch_ret_t361 = switch_ret_t362;
          break;
      }
      switch_ret_t354 = switch_ret_t361;
      break;
  }
  return switch_ret_t354;
}

tll_ptr lam_fun_t374(tll_ptr __v81808, tll_env env) {
  tll_ptr UniqU_t373; tll_ptr c_v81810; tll_ptr call_ret_t372;
  tll_ptr send_ch_t371;
  call_ret_t372 = msortU_i50(env[1]);
  instr_struct(&UniqU_t373, 16, 2, call_ret_t372, 0);
  instr_send(&send_ch_t371, env[0], UniqU_t373);
  c_v81810 = send_ch_t371;
  return 0;
}

tll_ptr cmsort_workerU_i54(tll_ptr n_v81765, tll_ptr zs_v81766, tll_ptr c_v81767) {
  tll_ptr add_ret_t330; tll_ptr call_ret_t344; tll_ptr consUU_t345;
  tll_ptr consUU_t346; tll_ptr ifte_ret_t376; tll_ptr lam_clo_t336;
  tll_ptr lam_clo_t343; tll_ptr lam_clo_t370; tll_ptr lam_clo_t375;
  tll_ptr n0_v81768; tll_ptr switch_ret_t331; tll_ptr switch_ret_t337;
  tll_ptr switch_ret_t347; tll_ptr xs0_v81779; tll_ptr ys0_v81780;
  tll_ptr z0_v81772; tll_ptr z1_v81777; tll_ptr zs0_v81773;
  tll_ptr zs1_v81778;
  if (n_v81765) {
    add_ret_t330 = n_v81765 - 1;
    n0_v81768 = add_ret_t330;
    switch(((tll_node)zs_v81766)->tag) {
      case 13:
        instr_clo(&lam_clo_t336, &lam_fun_t335, 1, c_v81767);
        switch_ret_t331 = lam_clo_t336;
        break;
      case 14:
        z0_v81772 = ((tll_node)zs_v81766)->data[0];
        zs0_v81773 = ((tll_node)zs_v81766)->data[1];
        switch(((tll_node)zs0_v81773)->tag) {
          case 13:
            instr_clo(&lam_clo_t343, &lam_fun_t342, 2, z0_v81772, c_v81767);
            switch_ret_t337 = lam_clo_t343;
            break;
          case 14:
            z1_v81777 = ((tll_node)zs0_v81773)->data[0];
            zs1_v81778 = ((tll_node)zs0_v81773)->data[1];
            instr_struct(&consUU_t345, 14, 2, z1_v81777, zs1_v81778);
            instr_struct(&consUU_t346, 14, 2, z0_v81772, consUU_t345);
            call_ret_t344 = splitU_i46(consUU_t346);
            switch(((tll_node)call_ret_t344)->tag) {
              case 0:
                xs0_v81779 = ((tll_node)call_ret_t344)->data[0];
                ys0_v81780 = ((tll_node)call_ret_t344)->data[1];
                instr_free_struct(call_ret_t344);
                instr_clo(&lam_clo_t370, &lam_fun_t369, 4,
                          ys0_v81780, xs0_v81779, n0_v81768, c_v81767);
                switch_ret_t347 = lam_clo_t370;
                break;
            }
            switch_ret_t337 = switch_ret_t347;
            break;
        }
        switch_ret_t331 = switch_ret_t337;
        break;
    }
    ifte_ret_t376 = switch_ret_t331;
  }
  else {
    instr_clo(&lam_clo_t375, &lam_fun_t374, 2, c_v81767, zs_v81766);
    ifte_ret_t376 = lam_clo_t375;
  }
  return ifte_ret_t376;
}

tll_ptr lam_fun_t378(tll_ptr c_v81816, tll_env env) {
  tll_ptr call_ret_t377;
  call_ret_t377 = cmsort_workerU_i54(env[1], env[0], c_v81816);
  return call_ret_t377;
}

tll_ptr lam_fun_t380(tll_ptr zs_v81814, tll_env env) {
  tll_ptr lam_clo_t379;
  instr_clo(&lam_clo_t379, &lam_fun_t378, 2, zs_v81814, env[0]);
  return lam_clo_t379;
}

tll_ptr lam_fun_t382(tll_ptr n_v81811, tll_env env) {
  tll_ptr lam_clo_t381;
  instr_clo(&lam_clo_t381, &lam_fun_t380, 1, n_v81811);
  return lam_clo_t381;
}

tll_ptr lam_fun_t389(tll_ptr __v81821, tll_env env) {
  tll_ptr UniqL_t388; tll_ptr c_v81823; tll_ptr nilUL_t387;
  tll_ptr send_ch_t386;
  instr_struct(&nilUL_t387, 11, 0);
  instr_struct(&UniqL_t388, 15, 2, nilUL_t387, 0);
  instr_send(&send_ch_t386, env[0], UniqL_t388);
  c_v81823 = send_ch_t386;
  return 0;
}

tll_ptr lam_fun_t396(tll_ptr __v81826, tll_env env) {
  tll_ptr UniqL_t395; tll_ptr c_v81828; tll_ptr consUL_t394;
  tll_ptr nilUL_t393; tll_ptr send_ch_t392;
  instr_struct(&nilUL_t393, 11, 0);
  instr_struct(&consUL_t394, 12, 2, env[0], nilUL_t393);
  instr_struct(&UniqL_t395, 15, 2, consUL_t394, 0);
  instr_send(&send_ch_t392, env[1], UniqL_t395);
  c_v81828 = send_ch_t392;
  return 0;
}

tll_ptr fork_fun_t405(tll_env env) {
  tll_ptr app_ret_t404; tll_ptr call_ret_t403; tll_ptr fork_ret_t407;
  call_ret_t403 = cmsort_workerL_i53(env[2], env[1], env[0]);
  instr_app(&app_ret_t404, call_ret_t403, 0);
  instr_free_clo(call_ret_t403);
  fork_ret_t407 = app_ret_t404;
  instr_free_thread(env);
  return fork_ret_t407;
}

tll_ptr fork_fun_t412(tll_env env) {
  tll_ptr app_ret_t411; tll_ptr call_ret_t410; tll_ptr fork_ret_t414;
  call_ret_t410 = cmsort_workerL_i53(env[2], env[1], env[0]);
  instr_app(&app_ret_t411, call_ret_t410, 0);
  instr_free_clo(call_ret_t410);
  fork_ret_t414 = app_ret_t411;
  instr_free_thread(env);
  return fork_ret_t414;
}

tll_ptr lam_fun_t423(tll_ptr __v81833, tll_env env) {
  tll_ptr UniqL_t420; tll_ptr __v81858; tll_ptr __v81859; tll_ptr c_v81857;
  tll_ptr call_ret_t419; tll_ptr close_tmp_t421; tll_ptr close_tmp_t422;
  tll_ptr fork_ch_t406; tll_ptr fork_ch_t413; tll_ptr msg1_v81848;
  tll_ptr msg2_v81851; tll_ptr pf1_v81854; tll_ptr pf2_v81856;
  tll_ptr r1_v81849; tll_ptr r2_v81852; tll_ptr recv_msg_t402;
  tll_ptr recv_msg_t409; tll_ptr send_ch_t418; tll_ptr switch_ret_t408;
  tll_ptr switch_ret_t415; tll_ptr switch_ret_t416; tll_ptr switch_ret_t417;
  tll_ptr xs1_v81853; tll_ptr xs2_v81855;
  instr_fork(&fork_ch_t406, &fork_fun_t405, 2, env[1], env[2]);
  instr_recv(&recv_msg_t402, fork_ch_t406);
  switch(((tll_node)recv_msg_t402)->tag) {
    case 0:
      msg1_v81848 = ((tll_node)recv_msg_t402)->data[0];
      r1_v81849 = ((tll_node)recv_msg_t402)->data[1];
      instr_free_struct(recv_msg_t402);
      instr_fork(&fork_ch_t413, &fork_fun_t412, 2, env[0], env[2]);
      instr_recv(&recv_msg_t409, fork_ch_t413);
      switch(((tll_node)recv_msg_t409)->tag) {
        case 0:
          msg2_v81851 = ((tll_node)recv_msg_t409)->data[0];
          r2_v81852 = ((tll_node)recv_msg_t409)->data[1];
          instr_free_struct(recv_msg_t409);
          switch(((tll_node)msg1_v81848)->tag) {
            case 15:
              xs1_v81853 = ((tll_node)msg1_v81848)->data[0];
              pf1_v81854 = ((tll_node)msg1_v81848)->data[1];
              instr_free_struct(msg1_v81848);
              switch(((tll_node)msg2_v81851)->tag) {
                case 15:
                  xs2_v81855 = ((tll_node)msg2_v81851)->data[0];
                  pf2_v81856 = ((tll_node)msg2_v81851)->data[1];
                  instr_free_struct(msg2_v81851);
                  call_ret_t419 = mergeL_i47(xs1_v81853, xs2_v81855);
                  instr_struct(&UniqL_t420, 15, 2, call_ret_t419, 0);
                  instr_send(&send_ch_t418, env[3], UniqL_t420);
                  c_v81857 = send_ch_t418;
                  instr_close(&close_tmp_t421, r1_v81849);
                  __v81858 = close_tmp_t421;
                  instr_close(&close_tmp_t422, r2_v81852);
                  __v81859 = close_tmp_t422;
                  switch_ret_t417 = 0;
                  break;
              }
              switch_ret_t416 = switch_ret_t417;
              break;
          }
          switch_ret_t415 = switch_ret_t416;
          break;
      }
      switch_ret_t408 = switch_ret_t415;
      break;
  }
  return switch_ret_t408;
}

tll_ptr lam_fun_t428(tll_ptr __v81860, tll_env env) {
  tll_ptr UniqL_t427; tll_ptr c_v81862; tll_ptr call_ret_t426;
  tll_ptr send_ch_t425;
  call_ret_t426 = msortL_i49(env[1]);
  instr_struct(&UniqL_t427, 15, 2, call_ret_t426, 0);
  instr_send(&send_ch_t425, env[0], UniqL_t427);
  c_v81862 = send_ch_t425;
  return 0;
}

tll_ptr cmsort_workerL_i53(tll_ptr n_v81817, tll_ptr zs_v81818, tll_ptr c_v81819) {
  tll_ptr add_ret_t384; tll_ptr call_ret_t398; tll_ptr consUL_t399;
  tll_ptr consUL_t400; tll_ptr ifte_ret_t430; tll_ptr lam_clo_t390;
  tll_ptr lam_clo_t397; tll_ptr lam_clo_t424; tll_ptr lam_clo_t429;
  tll_ptr n0_v81820; tll_ptr switch_ret_t385; tll_ptr switch_ret_t391;
  tll_ptr switch_ret_t401; tll_ptr xs0_v81831; tll_ptr ys0_v81832;
  tll_ptr z0_v81824; tll_ptr z1_v81829; tll_ptr zs0_v81825;
  tll_ptr zs1_v81830;
  if (n_v81817) {
    add_ret_t384 = n_v81817 - 1;
    n0_v81820 = add_ret_t384;
    switch(((tll_node)zs_v81818)->tag) {
      case 11:
        instr_free_struct(zs_v81818);
        instr_clo(&lam_clo_t390, &lam_fun_t389, 1, c_v81819);
        switch_ret_t385 = lam_clo_t390;
        break;
      case 12:
        z0_v81824 = ((tll_node)zs_v81818)->data[0];
        zs0_v81825 = ((tll_node)zs_v81818)->data[1];
        instr_free_struct(zs_v81818);
        switch(((tll_node)zs0_v81825)->tag) {
          case 11:
            instr_free_struct(zs0_v81825);
            instr_clo(&lam_clo_t397, &lam_fun_t396, 2, z0_v81824, c_v81819);
            switch_ret_t391 = lam_clo_t397;
            break;
          case 12:
            z1_v81829 = ((tll_node)zs0_v81825)->data[0];
            zs1_v81830 = ((tll_node)zs0_v81825)->data[1];
            instr_free_struct(zs0_v81825);
            instr_struct(&consUL_t399, 12, 2, z1_v81829, zs1_v81830);
            instr_struct(&consUL_t400, 12, 2, z0_v81824, consUL_t399);
            call_ret_t398 = splitL_i45(consUL_t400);
            switch(((tll_node)call_ret_t398)->tag) {
              case 0:
                xs0_v81831 = ((tll_node)call_ret_t398)->data[0];
                ys0_v81832 = ((tll_node)call_ret_t398)->data[1];
                instr_free_struct(call_ret_t398);
                instr_clo(&lam_clo_t424, &lam_fun_t423, 4,
                          ys0_v81832, xs0_v81831, n0_v81820, c_v81819);
                switch_ret_t401 = lam_clo_t424;
                break;
            }
            switch_ret_t391 = switch_ret_t401;
            break;
        }
        switch_ret_t385 = switch_ret_t391;
        break;
    }
    ifte_ret_t430 = switch_ret_t385;
  }
  else {
    instr_clo(&lam_clo_t429, &lam_fun_t428, 2, c_v81819, zs_v81818);
    ifte_ret_t430 = lam_clo_t429;
  }
  return ifte_ret_t430;
}

tll_ptr lam_fun_t432(tll_ptr c_v81868, tll_env env) {
  tll_ptr call_ret_t431;
  call_ret_t431 = cmsort_workerL_i53(env[1], env[0], c_v81868);
  return call_ret_t431;
}

tll_ptr lam_fun_t434(tll_ptr zs_v81866, tll_env env) {
  tll_ptr lam_clo_t433;
  instr_clo(&lam_clo_t433, &lam_fun_t432, 2, zs_v81866, env[0]);
  return lam_clo_t433;
}

tll_ptr lam_fun_t436(tll_ptr n_v81863, tll_env env) {
  tll_ptr lam_clo_t435;
  instr_clo(&lam_clo_t435, &lam_fun_t434, 1, n_v81863);
  return lam_clo_t435;
}

tll_ptr fork_fun_t441(tll_env env) {
  tll_ptr app_ret_t440; tll_ptr call_ret_t439; tll_ptr fork_ret_t443;
  call_ret_t439 = cmsort_workerU_i54((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t440, call_ret_t439, 0);
  instr_free_clo(call_ret_t439);
  fork_ret_t443 = app_ret_t440;
  instr_free_thread(env);
  return fork_ret_t443;
}

tll_ptr lam_fun_t446(tll_ptr __v81870, tll_env env) {
  tll_ptr __v81878; tll_ptr c_v81877; tll_ptr close_tmp_t445;
  tll_ptr fork_ch_t442; tll_ptr msg_v81876; tll_ptr recv_msg_t438;
  tll_ptr switch_ret_t444;
  instr_fork(&fork_ch_t442, &fork_fun_t441, 1, env[0]);
  instr_recv(&recv_msg_t438, fork_ch_t442);
  switch(((tll_node)recv_msg_t438)->tag) {
    case 0:
      msg_v81876 = ((tll_node)recv_msg_t438)->data[0];
      c_v81877 = ((tll_node)recv_msg_t438)->data[1];
      instr_free_struct(recv_msg_t438);
      instr_close(&close_tmp_t445, c_v81877);
      __v81878 = close_tmp_t445;
      switch_ret_t444 = msg_v81876;
      break;
  }
  return switch_ret_t444;
}

tll_ptr cmsortU_i56(tll_ptr zs_v81869) {
  tll_ptr lam_clo_t447;
  instr_clo(&lam_clo_t447, &lam_fun_t446, 1, zs_v81869);
  return lam_clo_t447;
}

tll_ptr lam_fun_t449(tll_ptr zs_v81879, tll_env env) {
  tll_ptr call_ret_t448;
  call_ret_t448 = cmsortU_i56(zs_v81879);
  return call_ret_t448;
}

tll_ptr fork_fun_t454(tll_env env) {
  tll_ptr app_ret_t453; tll_ptr call_ret_t452; tll_ptr fork_ret_t456;
  call_ret_t452 = cmsort_workerL_i53((tll_ptr)4, env[1], env[0]);
  instr_app(&app_ret_t453, call_ret_t452, 0);
  instr_free_clo(call_ret_t452);
  fork_ret_t456 = app_ret_t453;
  instr_free_thread(env);
  return fork_ret_t456;
}

tll_ptr lam_fun_t459(tll_ptr __v81881, tll_env env) {
  tll_ptr __v81889; tll_ptr c_v81888; tll_ptr close_tmp_t458;
  tll_ptr fork_ch_t455; tll_ptr msg_v81887; tll_ptr recv_msg_t451;
  tll_ptr switch_ret_t457;
  instr_fork(&fork_ch_t455, &fork_fun_t454, 1, env[0]);
  instr_recv(&recv_msg_t451, fork_ch_t455);
  switch(((tll_node)recv_msg_t451)->tag) {
    case 0:
      msg_v81887 = ((tll_node)recv_msg_t451)->data[0];
      c_v81888 = ((tll_node)recv_msg_t451)->data[1];
      instr_free_struct(recv_msg_t451);
      instr_close(&close_tmp_t458, c_v81888);
      __v81889 = close_tmp_t458;
      switch_ret_t457 = msg_v81887;
      break;
  }
  return switch_ret_t457;
}

tll_ptr cmsortL_i55(tll_ptr zs_v81880) {
  tll_ptr lam_clo_t460;
  instr_clo(&lam_clo_t460, &lam_fun_t459, 1, zs_v81880);
  return lam_clo_t460;
}

tll_ptr lam_fun_t462(tll_ptr zs_v81890, tll_env env) {
  tll_ptr call_ret_t461;
  call_ret_t461 = cmsortL_i55(zs_v81890);
  return call_ret_t461;
}

tll_ptr mkListU_i58(tll_ptr n_v81891) {
  tll_ptr add_ret_t465; tll_ptr call_ret_t464; tll_ptr consUU_t466;
  tll_ptr ifte_ret_t468; tll_ptr nilUU_t467;
  if (n_v81891) {
    add_ret_t465 = n_v81891 - 1;
    call_ret_t464 = mkListU_i58(add_ret_t465);
    instr_struct(&consUU_t466, 14, 2, n_v81891, call_ret_t464);
    ifte_ret_t468 = consUU_t466;
  }
  else {
    instr_struct(&nilUU_t467, 13, 0);
    ifte_ret_t468 = nilUU_t467;
  }
  return ifte_ret_t468;
}

tll_ptr lam_fun_t470(tll_ptr n_v81892, tll_env env) {
  tll_ptr call_ret_t469;
  call_ret_t469 = mkListU_i58(n_v81892);
  return call_ret_t469;
}

tll_ptr mkListL_i57(tll_ptr n_v81893) {
  tll_ptr add_ret_t473; tll_ptr call_ret_t472; tll_ptr consUL_t474;
  tll_ptr ifte_ret_t476; tll_ptr nilUL_t475;
  if (n_v81893) {
    add_ret_t473 = n_v81893 - 1;
    call_ret_t472 = mkListL_i57(add_ret_t473);
    instr_struct(&consUL_t474, 12, 2, n_v81893, call_ret_t472);
    ifte_ret_t476 = consUL_t474;
  }
  else {
    instr_struct(&nilUL_t475, 11, 0);
    ifte_ret_t476 = nilUL_t475;
  }
  return ifte_ret_t476;
}

tll_ptr lam_fun_t478(tll_ptr n_v81894, tll_env env) {
  tll_ptr call_ret_t477;
  call_ret_t477 = mkListL_i57(n_v81894);
  return call_ret_t477;
}

tll_ptr free_i35(tll_ptr A_v81895, tll_ptr ls_v81896) {
  tll_ptr __v81897; tll_ptr call_ret_t481; tll_ptr ls_v81898;
  tll_ptr switch_ret_t480;
  switch(((tll_node)ls_v81896)->tag) {
    case 11:
      instr_free_struct(ls_v81896);
      switch_ret_t480 = 0;
      break;
    case 12:
      __v81897 = ((tll_node)ls_v81896)->data[0];
      ls_v81898 = ((tll_node)ls_v81896)->data[1];
      instr_free_struct(ls_v81896);
      call_ret_t481 = free_i35(0, ls_v81898);
      switch_ret_t480 = call_ret_t481;
      break;
  }
  return switch_ret_t480;
}

tll_ptr lam_fun_t483(tll_ptr ls_v81901, tll_env env) {
  tll_ptr call_ret_t482;
  call_ret_t482 = free_i35(env[0], ls_v81901);
  return call_ret_t482;
}

tll_ptr lam_fun_t485(tll_ptr A_v81899, tll_env env) {
  tll_ptr lam_clo_t484;
  instr_clo(&lam_clo_t484, &lam_fun_t483, 1, A_v81899);
  return lam_clo_t484;
}

int main() {
  instr_init();
  tll_ptr __v81903; tll_ptr __v81904; tll_ptr app_ret_t489;
  tll_ptr call_ret_t487; tll_ptr call_ret_t488; tll_ptr call_ret_t491;
  tll_ptr lam_clo_t104; tll_ptr lam_clo_t114; tll_ptr lam_clo_t12;
  tll_ptr lam_clo_t122; tll_ptr lam_clo_t130; tll_ptr lam_clo_t136;
  tll_ptr lam_clo_t149; tll_ptr lam_clo_t16; tll_ptr lam_clo_t162;
  tll_ptr lam_clo_t175; tll_ptr lam_clo_t185; tll_ptr lam_clo_t195;
  tll_ptr lam_clo_t205; tll_ptr lam_clo_t215; tll_ptr lam_clo_t224;
  tll_ptr lam_clo_t233; tll_ptr lam_clo_t250; tll_ptr lam_clo_t26;
  tll_ptr lam_clo_t267; tll_ptr lam_clo_t283; tll_ptr lam_clo_t299;
  tll_ptr lam_clo_t314; tll_ptr lam_clo_t329; tll_ptr lam_clo_t38;
  tll_ptr lam_clo_t383; tll_ptr lam_clo_t437; tll_ptr lam_clo_t450;
  tll_ptr lam_clo_t463; tll_ptr lam_clo_t471; tll_ptr lam_clo_t479;
  tll_ptr lam_clo_t486; tll_ptr lam_clo_t50; tll_ptr lam_clo_t6;
  tll_ptr lam_clo_t60; tll_ptr lam_clo_t72; tll_ptr lam_clo_t77;
  tll_ptr lam_clo_t86; tll_ptr lam_clo_t95; tll_ptr sorted_v81902;
  tll_ptr switch_ret_t490;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i59 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i60 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i61 = lam_clo_t16;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 0);
  ltenclo_i62 = lam_clo_t26;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 0);
  gtenclo_i63 = lam_clo_t38;
  instr_clo(&lam_clo_t50, &lam_fun_t49, 0);
  ltnclo_i64 = lam_clo_t50;
  instr_clo(&lam_clo_t60, &lam_fun_t59, 0);
  gtnclo_i65 = lam_clo_t60;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  eqnclo_i66 = lam_clo_t72;
  instr_clo(&lam_clo_t77, &lam_fun_t76, 0);
  predclo_i67 = lam_clo_t77;
  instr_clo(&lam_clo_t86, &lam_fun_t85, 0);
  addnclo_i68 = lam_clo_t86;
  instr_clo(&lam_clo_t95, &lam_fun_t94, 0);
  subnclo_i69 = lam_clo_t95;
  instr_clo(&lam_clo_t104, &lam_fun_t103, 0);
  mulnclo_i70 = lam_clo_t104;
  instr_clo(&lam_clo_t114, &lam_fun_t113, 0);
  divnclo_i71 = lam_clo_t114;
  instr_clo(&lam_clo_t122, &lam_fun_t121, 0);
  modnclo_i72 = lam_clo_t122;
  instr_clo(&lam_clo_t130, &lam_fun_t129, 0);
  catsclo_i73 = lam_clo_t130;
  instr_clo(&lam_clo_t136, &lam_fun_t135, 0);
  strlenclo_i74 = lam_clo_t136;
  instr_clo(&lam_clo_t149, &lam_fun_t148, 0);
  lenUUclo_i75 = lam_clo_t149;
  instr_clo(&lam_clo_t162, &lam_fun_t161, 0);
  lenULclo_i76 = lam_clo_t162;
  instr_clo(&lam_clo_t175, &lam_fun_t174, 0);
  lenLLclo_i77 = lam_clo_t175;
  instr_clo(&lam_clo_t185, &lam_fun_t184, 0);
  appendUUclo_i78 = lam_clo_t185;
  instr_clo(&lam_clo_t195, &lam_fun_t194, 0);
  appendULclo_i79 = lam_clo_t195;
  instr_clo(&lam_clo_t205, &lam_fun_t204, 0);
  appendLLclo_i80 = lam_clo_t205;
  instr_clo(&lam_clo_t215, &lam_fun_t214, 0);
  readlineclo_i81 = lam_clo_t215;
  instr_clo(&lam_clo_t224, &lam_fun_t223, 0);
  printclo_i82 = lam_clo_t224;
  instr_clo(&lam_clo_t233, &lam_fun_t232, 0);
  prerrclo_i83 = lam_clo_t233;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 0);
  splitUclo_i84 = lam_clo_t250;
  instr_clo(&lam_clo_t267, &lam_fun_t266, 0);
  splitLclo_i85 = lam_clo_t267;
  instr_clo(&lam_clo_t283, &lam_fun_t282, 0);
  mergeUclo_i86 = lam_clo_t283;
  instr_clo(&lam_clo_t299, &lam_fun_t298, 0);
  mergeLclo_i87 = lam_clo_t299;
  instr_clo(&lam_clo_t314, &lam_fun_t313, 0);
  msortUclo_i88 = lam_clo_t314;
  instr_clo(&lam_clo_t329, &lam_fun_t328, 0);
  msortLclo_i89 = lam_clo_t329;
  instr_clo(&lam_clo_t383, &lam_fun_t382, 0);
  cmsort_workerUclo_i90 = lam_clo_t383;
  instr_clo(&lam_clo_t437, &lam_fun_t436, 0);
  cmsort_workerLclo_i91 = lam_clo_t437;
  instr_clo(&lam_clo_t450, &lam_fun_t449, 0);
  cmsortUclo_i92 = lam_clo_t450;
  instr_clo(&lam_clo_t463, &lam_fun_t462, 0);
  cmsortLclo_i93 = lam_clo_t463;
  instr_clo(&lam_clo_t471, &lam_fun_t470, 0);
  mkListUclo_i94 = lam_clo_t471;
  instr_clo(&lam_clo_t479, &lam_fun_t478, 0);
  mkListLclo_i95 = lam_clo_t479;
  instr_clo(&lam_clo_t486, &lam_fun_t485, 0);
  freeclo_i96 = lam_clo_t486;
  call_ret_t488 = mkListL_i57((tll_ptr)2000000);
  call_ret_t487 = cmsortL_i55(call_ret_t488);
  instr_app(&app_ret_t489, call_ret_t487, 0);
  instr_free_clo(call_ret_t487);
  switch(((tll_node)app_ret_t489)->tag) {
    case 15:
      sorted_v81902 = ((tll_node)app_ret_t489)->data[0];
      __v81903 = ((tll_node)app_ret_t489)->data[1];
      instr_free_struct(app_ret_t489);
      call_ret_t491 = free_i35(0, sorted_v81902);
      __v81904 = call_ret_t491;
      switch_ret_t490 = 0;
      break;
  }
  return 0;
}

