#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v104586, tll_ptr b2_v104587);
tll_ptr orb_i2(tll_ptr b1_v104591, tll_ptr b2_v104592);
tll_ptr notb_i3(tll_ptr b_v104596);
tll_ptr lten_i4(tll_ptr x_v104598, tll_ptr y_v104599);
tll_ptr gten_i5(tll_ptr x_v104603, tll_ptr y_v104604);
tll_ptr ltn_i6(tll_ptr x_v104608, tll_ptr y_v104609);
tll_ptr gtn_i7(tll_ptr x_v104613, tll_ptr y_v104614);
tll_ptr eqn_i8(tll_ptr x_v104618, tll_ptr y_v104619);
tll_ptr pred_i9(tll_ptr x_v104623);
tll_ptr addn_i10(tll_ptr x_v104625, tll_ptr y_v104626);
tll_ptr subn_i11(tll_ptr x_v104630, tll_ptr y_v104631);
tll_ptr muln_i12(tll_ptr x_v104635, tll_ptr y_v104636);
tll_ptr divn_i13(tll_ptr x_v104640, tll_ptr y_v104641);
tll_ptr modn_i14(tll_ptr x_v104645, tll_ptr y_v104646);
tll_ptr cats_i15(tll_ptr s1_v104650, tll_ptr s2_v104651);
tll_ptr strlen_i16(tll_ptr s_v104657);
tll_ptr lenUU_i44(tll_ptr A_v104661, tll_ptr xs_v104662);
tll_ptr lenUL_i43(tll_ptr A_v104670, tll_ptr xs_v104671);
tll_ptr lenLL_i41(tll_ptr A_v104679, tll_ptr xs_v104680);
tll_ptr appendUU_i48(tll_ptr A_v104688, tll_ptr xs_v104689, tll_ptr ys_v104690);
tll_ptr appendUL_i47(tll_ptr A_v104699, tll_ptr xs_v104700, tll_ptr ys_v104701);
tll_ptr appendLL_i45(tll_ptr A_v104710, tll_ptr xs_v104711, tll_ptr ys_v104712);
tll_ptr readline_i25(tll_ptr __v104721);
tll_ptr print_i26(tll_ptr s_v104736);
tll_ptr prerr_i27(tll_ptr s_v104747);
tll_ptr splitU_i50(tll_ptr zs_v104758);
tll_ptr splitL_i49(tll_ptr zs_v104767);
tll_ptr mergeU_i52(tll_ptr xs_v104776, tll_ptr ys_v104777);
tll_ptr mergeL_i51(tll_ptr xs_v104785, tll_ptr ys_v104786);
tll_ptr msortU_i54(tll_ptr zs_v104794);
tll_ptr msortL_i53(tll_ptr zs_v104803);
tll_ptr cmsort_workerU_i58(tll_ptr zs_v104812, tll_ptr c_v104813);
tll_ptr cmsort_workerL_i57(tll_ptr zs_v104866, tll_ptr c_v104867);
tll_ptr cmsortU_i60(tll_ptr zs_v104920);
tll_ptr cmsortL_i59(tll_ptr zs_v104935);
tll_ptr get_at_i35(tll_ptr A_v104950, tll_ptr n_v104951, tll_ptr xs_v104952, tll_ptr a_v104953);
tll_ptr string_of_digit_i36(tll_ptr n_v104968);
tll_ptr string_of_nat_i37(tll_ptr n_v104970);
tll_ptr string_of_listU_i62(tll_ptr xs_v104974);
tll_ptr string_of_listL_i61(tll_ptr xs_v104978);
tll_ptr mkListU_i64(tll_ptr n_v104982);
tll_ptr mkListL_i63(tll_ptr n_v104984);

tll_ptr addnclo_i74;
tll_ptr andbclo_i65;
tll_ptr appendLLclo_i86;
tll_ptr appendULclo_i85;
tll_ptr appendUUclo_i84;
tll_ptr catsclo_i79;
tll_ptr cmsortLclo_i99;
tll_ptr cmsortUclo_i98;
tll_ptr cmsort_workerLclo_i97;
tll_ptr cmsort_workerUclo_i96;
tll_ptr digits_i34;
tll_ptr divnclo_i77;
tll_ptr eqnclo_i72;
tll_ptr get_atclo_i100;
tll_ptr gtenclo_i69;
tll_ptr gtnclo_i71;
tll_ptr lenLLclo_i83;
tll_ptr lenULclo_i82;
tll_ptr lenUUclo_i81;
tll_ptr ltenclo_i68;
tll_ptr ltnclo_i70;
tll_ptr mergeLclo_i93;
tll_ptr mergeUclo_i92;
tll_ptr mkListLclo_i106;
tll_ptr mkListUclo_i105;
tll_ptr modnclo_i78;
tll_ptr msortLclo_i95;
tll_ptr msortUclo_i94;
tll_ptr mulnclo_i76;
tll_ptr notbclo_i67;
tll_ptr orbclo_i66;
tll_ptr predclo_i73;
tll_ptr prerrclo_i89;
tll_ptr printclo_i88;
tll_ptr readlineclo_i87;
tll_ptr splitLclo_i91;
tll_ptr splitUclo_i90;
tll_ptr string_of_digitclo_i101;
tll_ptr string_of_listLclo_i104;
tll_ptr string_of_listUclo_i103;
tll_ptr string_of_natclo_i102;
tll_ptr strlenclo_i80;
tll_ptr subnclo_i75;

tll_ptr andb_i1(tll_ptr b1_v104586, tll_ptr b2_v104587) {
  tll_ptr ifte_ret_t1;
  if (b1_v104586) {
    ifte_ret_t1 = b2_v104587;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v104590, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v104590);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v104588, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v104588);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v104591, tll_ptr b2_v104592) {
  tll_ptr ifte_ret_t7;
  if (b1_v104591) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v104592;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v104595, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v104595);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v104593, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v104593);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v104596) {
  tll_ptr ifte_ret_t13;
  if (b_v104596) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v104597, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v104597);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v104598, tll_ptr y_v104599) {
  tll_ptr call_ret_t17; tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  tll_ptr sub_ret_t18; tll_ptr sub_ret_t19;
  if (x_v104598) {
    if (y_v104599) {
      sub_ret_t18 = x_v104598 - 1;
      sub_ret_t19 = y_v104599 - 1;
      call_ret_t17 = lten_i4(sub_ret_t18, sub_ret_t19);
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

tll_ptr lam_fun_t23(tll_ptr y_v104602, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v104602);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v104600, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v104600);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v104603, tll_ptr y_v104604) {
  tll_ptr call_ret_t27; tll_ptr ifte_ret_t30; tll_ptr ifte_ret_t31;
  tll_ptr ifte_ret_t32; tll_ptr sub_ret_t28; tll_ptr sub_ret_t29;
  if (x_v104603) {
    if (y_v104604) {
      sub_ret_t28 = x_v104603 - 1;
      sub_ret_t29 = y_v104604 - 1;
      call_ret_t27 = gten_i5(sub_ret_t28, sub_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v104604) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v104607, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v104607);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v104605, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v104605);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v104608, tll_ptr y_v104609) {
  tll_ptr call_ret_t38; tll_ptr ifte_ret_t41; tll_ptr ifte_ret_t42;
  tll_ptr ifte_ret_t43; tll_ptr sub_ret_t39; tll_ptr sub_ret_t40;
  if (x_v104608) {
    if (y_v104609) {
      sub_ret_t39 = x_v104608 - 1;
      sub_ret_t40 = y_v104609 - 1;
      call_ret_t38 = ltn_i6(sub_ret_t39, sub_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v104609) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v104612, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v104612);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v104610, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v104610);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v104613, tll_ptr y_v104614) {
  tll_ptr call_ret_t49; tll_ptr ifte_ret_t52; tll_ptr ifte_ret_t53;
  tll_ptr sub_ret_t50; tll_ptr sub_ret_t51;
  if (x_v104613) {
    if (y_v104614) {
      sub_ret_t50 = x_v104613 - 1;
      sub_ret_t51 = y_v104614 - 1;
      call_ret_t49 = gtn_i7(sub_ret_t50, sub_ret_t51);
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

tll_ptr lam_fun_t55(tll_ptr y_v104617, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v104617);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v104615, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v104615);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v104618, tll_ptr y_v104619) {
  tll_ptr call_ret_t59; tll_ptr ifte_ret_t62; tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t64; tll_ptr sub_ret_t60; tll_ptr sub_ret_t61;
  if (x_v104618) {
    if (y_v104619) {
      sub_ret_t60 = x_v104618 - 1;
      sub_ret_t61 = y_v104619 - 1;
      call_ret_t59 = eqn_i8(sub_ret_t60, sub_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v104619) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v104622, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v104622);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v104620, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v104620);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v104623) {
  tll_ptr ifte_ret_t71; tll_ptr sub_ret_t70;
  if (x_v104623) {
    sub_ret_t70 = x_v104623 - 1;
    ifte_ret_t71 = sub_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v104624, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v104624);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v104625, tll_ptr y_v104626) {
  tll_ptr add_ret_t77; tll_ptr call_ret_t75; tll_ptr ifte_ret_t78;
  tll_ptr sub_ret_t76;
  if (x_v104625) {
    sub_ret_t76 = x_v104625 - 1;
    call_ret_t75 = addn_i10(sub_ret_t76, y_v104626);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v104626;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v104629, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v104629);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v104627, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v104627);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v104630, tll_ptr y_v104631) {
  tll_ptr call_ret_t84; tll_ptr call_ret_t85; tll_ptr ifte_ret_t87;
  tll_ptr sub_ret_t86;
  if (y_v104631) {
    call_ret_t85 = pred_i9(x_v104630);
    sub_ret_t86 = y_v104631 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, sub_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v104630;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v104634, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v104634);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v104632, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v104632);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v104635, tll_ptr y_v104636) {
  tll_ptr call_ret_t93; tll_ptr call_ret_t94; tll_ptr ifte_ret_t96;
  tll_ptr sub_ret_t95;
  if (x_v104635) {
    sub_ret_t95 = x_v104635 - 1;
    call_ret_t94 = muln_i12(sub_ret_t95, y_v104636);
    call_ret_t93 = addn_i10(y_v104636, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v104639, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v104639);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v104637, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v104637);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v104640, tll_ptr y_v104641) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v104640, y_v104641);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v104640, y_v104641);
    call_ret_t103 = divn_i13(call_ret_t104, y_v104641);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v104644, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v104644);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v104642, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v104642);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v104645, tll_ptr y_v104646) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v104645, y_v104646);
  call_ret_t113 = muln_i12(call_ret_t114, y_v104646);
  call_ret_t112 = subn_i11(x_v104645, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v104649, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v104649);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v104647, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v104647);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v104650, tll_ptr s2_v104651) {
  tll_ptr String_t122; tll_ptr c_v104652; tll_ptr call_ret_t121;
  tll_ptr s1_v104653; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v104650)->tag) {
    case 2:
      switch_ret_t120 = s2_v104651;
      break;
    case 3:
      c_v104652 = ((tll_node)s1_v104650)->data[0];
      s1_v104653 = ((tll_node)s1_v104650)->data[1];
      call_ret_t121 = cats_i15(s1_v104653, s2_v104651);
      instr_struct(&String_t122, 3, 2, c_v104652, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v104656, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v104656);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v104654, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v104654);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v104657) {
  tll_ptr __v104658; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v104659; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v104657)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v104658 = ((tll_node)s_v104657)->data[0];
      s_v104659 = ((tll_node)s_v104657)->data[1];
      call_ret_t129 = strlen_i16(s_v104659);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v104660, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v104660);
  return call_ret_t131;
}

tll_ptr lenUU_i44(tll_ptr A_v104661, tll_ptr xs_v104662) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v104665; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v104663; tll_ptr xs_v104664; tll_ptr xs_v104666;
  switch(((tll_node)xs_v104662)->tag) {
    case 13:
      instr_struct(&nilUU_t135, 13, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 14:
      x_v104663 = ((tll_node)xs_v104662)->data[0];
      xs_v104664 = ((tll_node)xs_v104662)->data[1];
      call_ret_t137 = lenUU_i44(0, xs_v104664);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v104665 = ((tll_node)call_ret_t137)->data[0];
          xs_v104666 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v104665 + 1;
          instr_struct(&consUU_t140, 14, 2, x_v104663, xs_v104666);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v104669, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i44(env[0], xs_v104669);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v104667, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v104667);
  return lam_clo_t144;
}

tll_ptr lenUL_i43(tll_ptr A_v104670, tll_ptr xs_v104671) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v104674; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v104672; tll_ptr xs_v104673; tll_ptr xs_v104675;
  switch(((tll_node)xs_v104671)->tag) {
    case 11:
      instr_free_struct(xs_v104671);
      instr_struct(&nilUL_t148, 11, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 12:
      x_v104672 = ((tll_node)xs_v104671)->data[0];
      xs_v104673 = ((tll_node)xs_v104671)->data[1];
      instr_free_struct(xs_v104671);
      call_ret_t150 = lenUL_i43(0, xs_v104673);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v104674 = ((tll_node)call_ret_t150)->data[0];
          xs_v104675 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v104674 + 1;
          instr_struct(&consUL_t153, 12, 2, x_v104672, xs_v104675);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v104678, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i43(env[0], xs_v104678);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v104676, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v104676);
  return lam_clo_t157;
}

tll_ptr lenLL_i41(tll_ptr A_v104679, tll_ptr xs_v104680) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v104683; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v104681; tll_ptr xs_v104682; tll_ptr xs_v104684;
  switch(((tll_node)xs_v104680)->tag) {
    case 7:
      instr_free_struct(xs_v104680);
      instr_struct(&nilLL_t161, 7, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 8:
      x_v104681 = ((tll_node)xs_v104680)->data[0];
      xs_v104682 = ((tll_node)xs_v104680)->data[1];
      instr_free_struct(xs_v104680);
      call_ret_t163 = lenLL_i41(0, xs_v104682);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v104683 = ((tll_node)call_ret_t163)->data[0];
          xs_v104684 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v104683 + 1;
          instr_struct(&consLL_t166, 8, 2, x_v104681, xs_v104684);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v104687, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i41(env[0], xs_v104687);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v104685, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v104685);
  return lam_clo_t170;
}

tll_ptr appendUU_i48(tll_ptr A_v104688, tll_ptr xs_v104689, tll_ptr ys_v104690) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v104691; tll_ptr xs_v104692;
  switch(((tll_node)xs_v104689)->tag) {
    case 13:
      switch_ret_t173 = ys_v104690;
      break;
    case 14:
      x_v104691 = ((tll_node)xs_v104689)->data[0];
      xs_v104692 = ((tll_node)xs_v104689)->data[1];
      call_ret_t174 = appendUU_i48(0, xs_v104692, ys_v104690);
      instr_struct(&consUU_t175, 14, 2, x_v104691, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v104698, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i48(env[1], env[0], ys_v104698);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v104696, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v104696, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v104693, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v104693);
  return lam_clo_t180;
}

tll_ptr appendUL_i47(tll_ptr A_v104699, tll_ptr xs_v104700, tll_ptr ys_v104701) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v104702; tll_ptr xs_v104703;
  switch(((tll_node)xs_v104700)->tag) {
    case 11:
      instr_free_struct(xs_v104700);
      switch_ret_t183 = ys_v104701;
      break;
    case 12:
      x_v104702 = ((tll_node)xs_v104700)->data[0];
      xs_v104703 = ((tll_node)xs_v104700)->data[1];
      instr_free_struct(xs_v104700);
      call_ret_t184 = appendUL_i47(0, xs_v104703, ys_v104701);
      instr_struct(&consUL_t185, 12, 2, x_v104702, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v104709, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i47(env[1], env[0], ys_v104709);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v104707, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v104707, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v104704, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v104704);
  return lam_clo_t190;
}

tll_ptr appendLL_i45(tll_ptr A_v104710, tll_ptr xs_v104711, tll_ptr ys_v104712) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v104713; tll_ptr xs_v104714;
  switch(((tll_node)xs_v104711)->tag) {
    case 7:
      instr_free_struct(xs_v104711);
      switch_ret_t193 = ys_v104712;
      break;
    case 8:
      x_v104713 = ((tll_node)xs_v104711)->data[0];
      xs_v104714 = ((tll_node)xs_v104711)->data[1];
      instr_free_struct(xs_v104711);
      call_ret_t194 = appendLL_i45(0, xs_v104714, ys_v104712);
      instr_struct(&consLL_t195, 8, 2, x_v104713, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v104720, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i45(env[1], env[0], ys_v104720);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v104718, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v104718, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v104715, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v104715);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v104722, tll_env env) {
  tll_ptr __v104731; tll_ptr ch_v104729; tll_ptr ch_v104730;
  tll_ptr ch_v104733; tll_ptr ch_v104734; tll_ptr prim_ch_t203;
  tll_ptr recv_msg_t205; tll_ptr s_v104732; tll_ptr send_ch_t204;
  tll_ptr send_ch_t207; tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v104729 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v104729, (tll_ptr)1);
  ch_v104730 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v104730);
  __v104731 = recv_msg_t205;
  switch(((tll_node)__v104731)->tag) {
    case 0:
      s_v104732 = ((tll_node)__v104731)->data[0];
      ch_v104733 = ((tll_node)__v104731)->data[1];
      instr_free_struct(__v104731);
      instr_send(&send_ch_t207, ch_v104733, (tll_ptr)0);
      ch_v104734 = send_ch_t207;
      switch_ret_t206 = s_v104732;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v104721) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v104735, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v104735);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v104737, tll_env env) {
  tll_ptr ch_v104742; tll_ptr ch_v104743; tll_ptr ch_v104744;
  tll_ptr ch_v104745; tll_ptr prim_ch_t213; tll_ptr send_ch_t214;
  tll_ptr send_ch_t215; tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v104742 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v104742, (tll_ptr)1);
  ch_v104743 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v104743, env[0]);
  ch_v104744 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v104744, (tll_ptr)0);
  ch_v104745 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v104736) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v104736);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v104746, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v104746);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v104748, tll_env env) {
  tll_ptr ch_v104753; tll_ptr ch_v104754; tll_ptr ch_v104755;
  tll_ptr ch_v104756; tll_ptr prim_ch_t222; tll_ptr send_ch_t223;
  tll_ptr send_ch_t224; tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v104753 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v104753, (tll_ptr)1);
  ch_v104754 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v104754, env[0]);
  ch_v104755 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v104755, (tll_ptr)0);
  ch_v104756 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v104747) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v104747);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v104757, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v104757);
  return call_ret_t228;
}

tll_ptr splitU_i50(tll_ptr zs_v104758) {
  tll_ptr __v104763; tll_ptr call_ret_t240; tll_ptr consUU_t237;
  tll_ptr consUU_t242; tll_ptr consUU_t243; tll_ptr nilUU_t232;
  tll_ptr nilUU_t233; tll_ptr nilUU_t236; tll_ptr nilUU_t238;
  tll_ptr pair_struct_t234; tll_ptr pair_struct_t239;
  tll_ptr pair_struct_t244; tll_ptr switch_ret_t231; tll_ptr switch_ret_t235;
  tll_ptr switch_ret_t241; tll_ptr x_v104759; tll_ptr xs_v104764;
  tll_ptr y_v104761; tll_ptr ys_v104765; tll_ptr zs_v104760;
  tll_ptr zs_v104762;
  switch(((tll_node)zs_v104758)->tag) {
    case 13:
      instr_struct(&nilUU_t232, 13, 0);
      instr_struct(&nilUU_t233, 13, 0);
      instr_struct(&pair_struct_t234, 0, 2, nilUU_t232, nilUU_t233);
      switch_ret_t231 = pair_struct_t234;
      break;
    case 14:
      x_v104759 = ((tll_node)zs_v104758)->data[0];
      zs_v104760 = ((tll_node)zs_v104758)->data[1];
      switch(((tll_node)zs_v104760)->tag) {
        case 13:
          instr_struct(&nilUU_t236, 13, 0);
          instr_struct(&consUU_t237, 14, 2, x_v104759, nilUU_t236);
          instr_struct(&nilUU_t238, 13, 0);
          instr_struct(&pair_struct_t239, 0, 2, consUU_t237, nilUU_t238);
          switch_ret_t235 = pair_struct_t239;
          break;
        case 14:
          y_v104761 = ((tll_node)zs_v104760)->data[0];
          zs_v104762 = ((tll_node)zs_v104760)->data[1];
          call_ret_t240 = splitU_i50(zs_v104762);
          __v104763 = call_ret_t240;
          switch(((tll_node)__v104763)->tag) {
            case 0:
              xs_v104764 = ((tll_node)__v104763)->data[0];
              ys_v104765 = ((tll_node)__v104763)->data[1];
              instr_free_struct(__v104763);
              instr_struct(&consUU_t242, 14, 2, x_v104759, xs_v104764);
              instr_struct(&consUU_t243, 14, 2, y_v104761, ys_v104765);
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

tll_ptr lam_fun_t246(tll_ptr zs_v104766, tll_env env) {
  tll_ptr call_ret_t245;
  call_ret_t245 = splitU_i50(zs_v104766);
  return call_ret_t245;
}

tll_ptr splitL_i49(tll_ptr zs_v104767) {
  tll_ptr __v104772; tll_ptr call_ret_t257; tll_ptr consUL_t254;
  tll_ptr consUL_t259; tll_ptr consUL_t260; tll_ptr nilUL_t249;
  tll_ptr nilUL_t250; tll_ptr nilUL_t253; tll_ptr nilUL_t255;
  tll_ptr pair_struct_t251; tll_ptr pair_struct_t256;
  tll_ptr pair_struct_t261; tll_ptr switch_ret_t248; tll_ptr switch_ret_t252;
  tll_ptr switch_ret_t258; tll_ptr x_v104768; tll_ptr xs_v104773;
  tll_ptr y_v104770; tll_ptr ys_v104774; tll_ptr zs_v104769;
  tll_ptr zs_v104771;
  switch(((tll_node)zs_v104767)->tag) {
    case 11:
      instr_free_struct(zs_v104767);
      instr_struct(&nilUL_t249, 11, 0);
      instr_struct(&nilUL_t250, 11, 0);
      instr_struct(&pair_struct_t251, 0, 2, nilUL_t249, nilUL_t250);
      switch_ret_t248 = pair_struct_t251;
      break;
    case 12:
      x_v104768 = ((tll_node)zs_v104767)->data[0];
      zs_v104769 = ((tll_node)zs_v104767)->data[1];
      instr_free_struct(zs_v104767);
      switch(((tll_node)zs_v104769)->tag) {
        case 11:
          instr_free_struct(zs_v104769);
          instr_struct(&nilUL_t253, 11, 0);
          instr_struct(&consUL_t254, 12, 2, x_v104768, nilUL_t253);
          instr_struct(&nilUL_t255, 11, 0);
          instr_struct(&pair_struct_t256, 0, 2, consUL_t254, nilUL_t255);
          switch_ret_t252 = pair_struct_t256;
          break;
        case 12:
          y_v104770 = ((tll_node)zs_v104769)->data[0];
          zs_v104771 = ((tll_node)zs_v104769)->data[1];
          instr_free_struct(zs_v104769);
          call_ret_t257 = splitL_i49(zs_v104771);
          __v104772 = call_ret_t257;
          switch(((tll_node)__v104772)->tag) {
            case 0:
              xs_v104773 = ((tll_node)__v104772)->data[0];
              ys_v104774 = ((tll_node)__v104772)->data[1];
              instr_free_struct(__v104772);
              instr_struct(&consUL_t259, 12, 2, x_v104768, xs_v104773);
              instr_struct(&consUL_t260, 12, 2, y_v104770, ys_v104774);
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

tll_ptr lam_fun_t263(tll_ptr zs_v104775, tll_env env) {
  tll_ptr call_ret_t262;
  call_ret_t262 = splitL_i49(zs_v104775);
  return call_ret_t262;
}

tll_ptr mergeU_i52(tll_ptr xs_v104776, tll_ptr ys_v104777) {
  tll_ptr call_ret_t268; tll_ptr call_ret_t269; tll_ptr call_ret_t272;
  tll_ptr consUU_t267; tll_ptr consUU_t270; tll_ptr consUU_t271;
  tll_ptr consUU_t273; tll_ptr consUU_t274; tll_ptr ifte_ret_t275;
  tll_ptr switch_ret_t265; tll_ptr switch_ret_t266; tll_ptr x_v104778;
  tll_ptr xs0_v104779; tll_ptr y_v104780; tll_ptr ys0_v104781;
  switch(((tll_node)xs_v104776)->tag) {
    case 13:
      switch_ret_t265 = ys_v104777;
      break;
    case 14:
      x_v104778 = ((tll_node)xs_v104776)->data[0];
      xs0_v104779 = ((tll_node)xs_v104776)->data[1];
      switch(((tll_node)ys_v104777)->tag) {
        case 13:
          instr_struct(&consUU_t267, 14, 2, x_v104778, xs0_v104779);
          switch_ret_t266 = consUU_t267;
          break;
        case 14:
          y_v104780 = ((tll_node)ys_v104777)->data[0];
          ys0_v104781 = ((tll_node)ys_v104777)->data[1];
          call_ret_t268 = lten_i4(x_v104778, y_v104780);
          if (call_ret_t268) {
            instr_struct(&consUU_t270, 14, 2, y_v104780, ys0_v104781);
            call_ret_t269 = mergeU_i52(xs0_v104779, consUU_t270);
            instr_struct(&consUU_t271, 14, 2, x_v104778, call_ret_t269);
            ifte_ret_t275 = consUU_t271;
          }
          else {
            instr_struct(&consUU_t273, 14, 2, x_v104778, xs0_v104779);
            call_ret_t272 = mergeU_i52(consUU_t273, ys0_v104781);
            instr_struct(&consUU_t274, 14, 2, y_v104780, call_ret_t272);
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

tll_ptr lam_fun_t277(tll_ptr ys_v104784, tll_env env) {
  tll_ptr call_ret_t276;
  call_ret_t276 = mergeU_i52(env[0], ys_v104784);
  return call_ret_t276;
}

tll_ptr lam_fun_t279(tll_ptr xs_v104782, tll_env env) {
  tll_ptr lam_clo_t278;
  instr_clo(&lam_clo_t278, &lam_fun_t277, 1, xs_v104782);
  return lam_clo_t278;
}

tll_ptr mergeL_i51(tll_ptr xs_v104785, tll_ptr ys_v104786) {
  tll_ptr call_ret_t284; tll_ptr call_ret_t285; tll_ptr call_ret_t288;
  tll_ptr consUL_t283; tll_ptr consUL_t286; tll_ptr consUL_t287;
  tll_ptr consUL_t289; tll_ptr consUL_t290; tll_ptr ifte_ret_t291;
  tll_ptr switch_ret_t281; tll_ptr switch_ret_t282; tll_ptr x_v104787;
  tll_ptr xs0_v104788; tll_ptr y_v104789; tll_ptr ys0_v104790;
  switch(((tll_node)xs_v104785)->tag) {
    case 11:
      instr_free_struct(xs_v104785);
      switch_ret_t281 = ys_v104786;
      break;
    case 12:
      x_v104787 = ((tll_node)xs_v104785)->data[0];
      xs0_v104788 = ((tll_node)xs_v104785)->data[1];
      instr_free_struct(xs_v104785);
      switch(((tll_node)ys_v104786)->tag) {
        case 11:
          instr_free_struct(ys_v104786);
          instr_struct(&consUL_t283, 12, 2, x_v104787, xs0_v104788);
          switch_ret_t282 = consUL_t283;
          break;
        case 12:
          y_v104789 = ((tll_node)ys_v104786)->data[0];
          ys0_v104790 = ((tll_node)ys_v104786)->data[1];
          instr_free_struct(ys_v104786);
          call_ret_t284 = lten_i4(x_v104787, y_v104789);
          if (call_ret_t284) {
            instr_struct(&consUL_t286, 12, 2, y_v104789, ys0_v104790);
            call_ret_t285 = mergeL_i51(xs0_v104788, consUL_t286);
            instr_struct(&consUL_t287, 12, 2, x_v104787, call_ret_t285);
            ifte_ret_t291 = consUL_t287;
          }
          else {
            instr_struct(&consUL_t289, 12, 2, x_v104787, xs0_v104788);
            call_ret_t288 = mergeL_i51(consUL_t289, ys0_v104790);
            instr_struct(&consUL_t290, 12, 2, y_v104789, call_ret_t288);
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

tll_ptr lam_fun_t293(tll_ptr ys_v104793, tll_env env) {
  tll_ptr call_ret_t292;
  call_ret_t292 = mergeL_i51(env[0], ys_v104793);
  return call_ret_t292;
}

tll_ptr lam_fun_t295(tll_ptr xs_v104791, tll_env env) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 1, xs_v104791);
  return lam_clo_t294;
}

tll_ptr msortU_i54(tll_ptr zs_v104794) {
  tll_ptr __v104799; tll_ptr call_ret_t302; tll_ptr call_ret_t306;
  tll_ptr call_ret_t307; tll_ptr call_ret_t308; tll_ptr consUU_t301;
  tll_ptr consUU_t303; tll_ptr consUU_t304; tll_ptr nilUU_t298;
  tll_ptr nilUU_t300; tll_ptr switch_ret_t297; tll_ptr switch_ret_t299;
  tll_ptr switch_ret_t305; tll_ptr x_v104795; tll_ptr xs_v104800;
  tll_ptr y_v104797; tll_ptr ys_v104801; tll_ptr zs_v104796;
  tll_ptr zs_v104798;
  switch(((tll_node)zs_v104794)->tag) {
    case 13:
      instr_struct(&nilUU_t298, 13, 0);
      switch_ret_t297 = nilUU_t298;
      break;
    case 14:
      x_v104795 = ((tll_node)zs_v104794)->data[0];
      zs_v104796 = ((tll_node)zs_v104794)->data[1];
      switch(((tll_node)zs_v104796)->tag) {
        case 13:
          instr_struct(&nilUU_t300, 13, 0);
          instr_struct(&consUU_t301, 14, 2, x_v104795, nilUU_t300);
          switch_ret_t299 = consUU_t301;
          break;
        case 14:
          y_v104797 = ((tll_node)zs_v104796)->data[0];
          zs_v104798 = ((tll_node)zs_v104796)->data[1];
          instr_struct(&consUU_t303, 14, 2, y_v104797, zs_v104798);
          instr_struct(&consUU_t304, 14, 2, x_v104795, consUU_t303);
          call_ret_t302 = splitU_i50(consUU_t304);
          __v104799 = call_ret_t302;
          switch(((tll_node)__v104799)->tag) {
            case 0:
              xs_v104800 = ((tll_node)__v104799)->data[0];
              ys_v104801 = ((tll_node)__v104799)->data[1];
              instr_free_struct(__v104799);
              call_ret_t307 = msortU_i54(xs_v104800);
              call_ret_t308 = msortU_i54(ys_v104801);
              call_ret_t306 = mergeU_i52(call_ret_t307, call_ret_t308);
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

tll_ptr lam_fun_t310(tll_ptr zs_v104802, tll_env env) {
  tll_ptr call_ret_t309;
  call_ret_t309 = msortU_i54(zs_v104802);
  return call_ret_t309;
}

tll_ptr msortL_i53(tll_ptr zs_v104803) {
  tll_ptr __v104808; tll_ptr call_ret_t317; tll_ptr call_ret_t321;
  tll_ptr call_ret_t322; tll_ptr call_ret_t323; tll_ptr consUL_t316;
  tll_ptr consUL_t318; tll_ptr consUL_t319; tll_ptr nilUL_t313;
  tll_ptr nilUL_t315; tll_ptr switch_ret_t312; tll_ptr switch_ret_t314;
  tll_ptr switch_ret_t320; tll_ptr x_v104804; tll_ptr xs_v104809;
  tll_ptr y_v104806; tll_ptr ys_v104810; tll_ptr zs_v104805;
  tll_ptr zs_v104807;
  switch(((tll_node)zs_v104803)->tag) {
    case 11:
      instr_free_struct(zs_v104803);
      instr_struct(&nilUL_t313, 11, 0);
      switch_ret_t312 = nilUL_t313;
      break;
    case 12:
      x_v104804 = ((tll_node)zs_v104803)->data[0];
      zs_v104805 = ((tll_node)zs_v104803)->data[1];
      instr_free_struct(zs_v104803);
      switch(((tll_node)zs_v104805)->tag) {
        case 11:
          instr_free_struct(zs_v104805);
          instr_struct(&nilUL_t315, 11, 0);
          instr_struct(&consUL_t316, 12, 2, x_v104804, nilUL_t315);
          switch_ret_t314 = consUL_t316;
          break;
        case 12:
          y_v104806 = ((tll_node)zs_v104805)->data[0];
          zs_v104807 = ((tll_node)zs_v104805)->data[1];
          instr_free_struct(zs_v104805);
          instr_struct(&consUL_t318, 12, 2, y_v104806, zs_v104807);
          instr_struct(&consUL_t319, 12, 2, x_v104804, consUL_t318);
          call_ret_t317 = splitL_i49(consUL_t319);
          __v104808 = call_ret_t317;
          switch(((tll_node)__v104808)->tag) {
            case 0:
              xs_v104809 = ((tll_node)__v104808)->data[0];
              ys_v104810 = ((tll_node)__v104808)->data[1];
              instr_free_struct(__v104808);
              call_ret_t322 = msortL_i53(xs_v104809);
              call_ret_t323 = msortL_i53(ys_v104810);
              call_ret_t321 = mergeL_i51(call_ret_t322, call_ret_t323);
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

tll_ptr lam_fun_t325(tll_ptr zs_v104811, tll_env env) {
  tll_ptr call_ret_t324;
  call_ret_t324 = msortL_i53(zs_v104811);
  return call_ret_t324;
}

tll_ptr lam_fun_t331(tll_ptr __v104814, tll_env env) {
  tll_ptr UniqU_t330; tll_ptr c_v104816; tll_ptr nilUU_t329;
  tll_ptr send_ch_t328;
  instr_struct(&nilUU_t329, 13, 0);
  instr_struct(&UniqU_t330, 16, 2, nilUU_t329, 0);
  instr_send(&send_ch_t328, env[0], UniqU_t330);
  c_v104816 = send_ch_t328;
  return 0;
}

tll_ptr lam_fun_t338(tll_ptr __v104819, tll_env env) {
  tll_ptr UniqU_t337; tll_ptr c_v104821; tll_ptr consUU_t336;
  tll_ptr nilUU_t335; tll_ptr send_ch_t334;
  instr_struct(&nilUU_t335, 13, 0);
  instr_struct(&consUU_t336, 14, 2, env[0], nilUU_t335);
  instr_struct(&UniqU_t337, 16, 2, consUU_t336, 0);
  instr_send(&send_ch_t334, env[1], UniqU_t337);
  c_v104821 = send_ch_t334;
  return 0;
}

tll_ptr fork_fun_t346(tll_env env) {
  tll_ptr app_ret_t345; tll_ptr call_ret_t344; tll_ptr fork_ret_t348;
  call_ret_t344 = cmsort_workerU_i58(env[1], env[0]);
  instr_app(&app_ret_t345, call_ret_t344, 0);
  instr_free_clo(call_ret_t344);
  fork_ret_t348 = app_ret_t345;
  instr_free_thread(env);
  return fork_ret_t348;
}

tll_ptr fork_fun_t351(tll_env env) {
  tll_ptr app_ret_t350; tll_ptr call_ret_t349; tll_ptr fork_ret_t353;
  call_ret_t349 = cmsort_workerU_i58(env[1], env[0]);
  instr_app(&app_ret_t350, call_ret_t349, 0);
  instr_free_clo(call_ret_t349);
  fork_ret_t353 = app_ret_t350;
  instr_free_thread(env);
  return fork_ret_t353;
}

tll_ptr lam_fun_t365(tll_ptr __v104826, tll_env env) {
  tll_ptr UniqU_t362; tll_ptr __v104849; tll_ptr __v104852;
  tll_ptr __v104861; tll_ptr __v104862; tll_ptr c_v104860;
  tll_ptr call_ret_t360; tll_ptr close_tmp_t363; tll_ptr close_tmp_t364;
  tll_ptr fork_ch_t347; tll_ptr fork_ch_t352; tll_ptr msg1_v104850;
  tll_ptr msg2_v104853; tll_ptr pf1_v104856; tll_ptr pf2_v104858;
  tll_ptr r1_v104845; tll_ptr r1_v104851; tll_ptr r2_v104847;
  tll_ptr r2_v104854; tll_ptr recv_msg_t354; tll_ptr recv_msg_t356;
  tll_ptr send_ch_t361; tll_ptr switch_ret_t355; tll_ptr switch_ret_t357;
  tll_ptr switch_ret_t358; tll_ptr switch_ret_t359; tll_ptr xs1_v104855;
  tll_ptr xs2_v104857; tll_ptr zs_v104859;
  instr_fork(&fork_ch_t347, &fork_fun_t346, 1, env[1]);
  r1_v104845 = fork_ch_t347;
  instr_fork(&fork_ch_t352, &fork_fun_t351, 1, env[0]);
  r2_v104847 = fork_ch_t352;
  instr_recv(&recv_msg_t354, r1_v104845);
  __v104849 = recv_msg_t354;
  switch(((tll_node)__v104849)->tag) {
    case 0:
      msg1_v104850 = ((tll_node)__v104849)->data[0];
      r1_v104851 = ((tll_node)__v104849)->data[1];
      instr_free_struct(__v104849);
      instr_recv(&recv_msg_t356, r2_v104847);
      __v104852 = recv_msg_t356;
      switch(((tll_node)__v104852)->tag) {
        case 0:
          msg2_v104853 = ((tll_node)__v104852)->data[0];
          r2_v104854 = ((tll_node)__v104852)->data[1];
          instr_free_struct(__v104852);
          switch(((tll_node)msg1_v104850)->tag) {
            case 16:
              xs1_v104855 = ((tll_node)msg1_v104850)->data[0];
              pf1_v104856 = ((tll_node)msg1_v104850)->data[1];
              switch(((tll_node)msg2_v104853)->tag) {
                case 16:
                  xs2_v104857 = ((tll_node)msg2_v104853)->data[0];
                  pf2_v104858 = ((tll_node)msg2_v104853)->data[1];
                  call_ret_t360 = mergeU_i52(xs1_v104855, xs2_v104857);
                  zs_v104859 = call_ret_t360;
                  instr_struct(&UniqU_t362, 16, 2, zs_v104859, 0);
                  instr_send(&send_ch_t361, env[2], UniqU_t362);
                  c_v104860 = send_ch_t361;
                  instr_close(&close_tmp_t363, r1_v104851);
                  __v104861 = close_tmp_t363;
                  instr_close(&close_tmp_t364, r2_v104854);
                  __v104862 = close_tmp_t364;
                  switch_ret_t359 = 0;
                  break;
              }
              switch_ret_t358 = switch_ret_t359;
              break;
          }
          switch_ret_t357 = switch_ret_t358;
          break;
      }
      switch_ret_t355 = switch_ret_t357;
      break;
  }
  return switch_ret_t355;
}

tll_ptr cmsort_workerU_i58(tll_ptr zs_v104812, tll_ptr c_v104813) {
  tll_ptr call_ret_t340; tll_ptr consUU_t341; tll_ptr consUU_t342;
  tll_ptr lam_clo_t332; tll_ptr lam_clo_t339; tll_ptr lam_clo_t366;
  tll_ptr switch_ret_t327; tll_ptr switch_ret_t333; tll_ptr switch_ret_t343;
  tll_ptr xs0_v104824; tll_ptr ys0_v104825; tll_ptr z0_v104817;
  tll_ptr z1_v104822; tll_ptr zs0_v104818; tll_ptr zs1_v104823;
  switch(((tll_node)zs_v104812)->tag) {
    case 13:
      instr_clo(&lam_clo_t332, &lam_fun_t331, 1, c_v104813);
      switch_ret_t327 = lam_clo_t332;
      break;
    case 14:
      z0_v104817 = ((tll_node)zs_v104812)->data[0];
      zs0_v104818 = ((tll_node)zs_v104812)->data[1];
      switch(((tll_node)zs0_v104818)->tag) {
        case 13:
          instr_clo(&lam_clo_t339, &lam_fun_t338, 2, z0_v104817, c_v104813);
          switch_ret_t333 = lam_clo_t339;
          break;
        case 14:
          z1_v104822 = ((tll_node)zs0_v104818)->data[0];
          zs1_v104823 = ((tll_node)zs0_v104818)->data[1];
          instr_struct(&consUU_t341, 14, 2, z1_v104822, zs1_v104823);
          instr_struct(&consUU_t342, 14, 2, z0_v104817, consUU_t341);
          call_ret_t340 = splitU_i50(consUU_t342);
          switch(((tll_node)call_ret_t340)->tag) {
            case 0:
              xs0_v104824 = ((tll_node)call_ret_t340)->data[0];
              ys0_v104825 = ((tll_node)call_ret_t340)->data[1];
              instr_free_struct(call_ret_t340);
              instr_clo(&lam_clo_t366, &lam_fun_t365, 3,
                        ys0_v104825, xs0_v104824, c_v104813);
              switch_ret_t343 = lam_clo_t366;
              break;
          }
          switch_ret_t333 = switch_ret_t343;
          break;
      }
      switch_ret_t327 = switch_ret_t333;
      break;
  }
  return switch_ret_t327;
}

tll_ptr lam_fun_t368(tll_ptr c_v104865, tll_env env) {
  tll_ptr call_ret_t367;
  call_ret_t367 = cmsort_workerU_i58(env[0], c_v104865);
  return call_ret_t367;
}

tll_ptr lam_fun_t370(tll_ptr zs_v104863, tll_env env) {
  tll_ptr lam_clo_t369;
  instr_clo(&lam_clo_t369, &lam_fun_t368, 1, zs_v104863);
  return lam_clo_t369;
}

tll_ptr lam_fun_t376(tll_ptr __v104868, tll_env env) {
  tll_ptr UniqL_t375; tll_ptr c_v104870; tll_ptr nilUL_t374;
  tll_ptr send_ch_t373;
  instr_struct(&nilUL_t374, 11, 0);
  instr_struct(&UniqL_t375, 15, 2, nilUL_t374, 0);
  instr_send(&send_ch_t373, env[0], UniqL_t375);
  c_v104870 = send_ch_t373;
  return 0;
}

tll_ptr lam_fun_t383(tll_ptr __v104873, tll_env env) {
  tll_ptr UniqL_t382; tll_ptr c_v104875; tll_ptr consUL_t381;
  tll_ptr nilUL_t380; tll_ptr send_ch_t379;
  instr_struct(&nilUL_t380, 11, 0);
  instr_struct(&consUL_t381, 12, 2, env[0], nilUL_t380);
  instr_struct(&UniqL_t382, 15, 2, consUL_t381, 0);
  instr_send(&send_ch_t379, env[1], UniqL_t382);
  c_v104875 = send_ch_t379;
  return 0;
}

tll_ptr fork_fun_t391(tll_env env) {
  tll_ptr app_ret_t390; tll_ptr call_ret_t389; tll_ptr fork_ret_t393;
  call_ret_t389 = cmsort_workerL_i57(env[1], env[0]);
  instr_app(&app_ret_t390, call_ret_t389, 0);
  instr_free_clo(call_ret_t389);
  fork_ret_t393 = app_ret_t390;
  instr_free_thread(env);
  return fork_ret_t393;
}

tll_ptr fork_fun_t396(tll_env env) {
  tll_ptr app_ret_t395; tll_ptr call_ret_t394; tll_ptr fork_ret_t398;
  call_ret_t394 = cmsort_workerL_i57(env[1], env[0]);
  instr_app(&app_ret_t395, call_ret_t394, 0);
  instr_free_clo(call_ret_t394);
  fork_ret_t398 = app_ret_t395;
  instr_free_thread(env);
  return fork_ret_t398;
}

tll_ptr lam_fun_t410(tll_ptr __v104880, tll_env env) {
  tll_ptr UniqL_t407; tll_ptr __v104903; tll_ptr __v104906;
  tll_ptr __v104915; tll_ptr __v104916; tll_ptr c_v104914;
  tll_ptr call_ret_t405; tll_ptr close_tmp_t408; tll_ptr close_tmp_t409;
  tll_ptr fork_ch_t392; tll_ptr fork_ch_t397; tll_ptr msg1_v104904;
  tll_ptr msg2_v104907; tll_ptr pf1_v104910; tll_ptr pf2_v104912;
  tll_ptr r1_v104899; tll_ptr r1_v104905; tll_ptr r2_v104901;
  tll_ptr r2_v104908; tll_ptr recv_msg_t399; tll_ptr recv_msg_t401;
  tll_ptr send_ch_t406; tll_ptr switch_ret_t400; tll_ptr switch_ret_t402;
  tll_ptr switch_ret_t403; tll_ptr switch_ret_t404; tll_ptr xs1_v104909;
  tll_ptr xs2_v104911; tll_ptr zs_v104913;
  instr_fork(&fork_ch_t392, &fork_fun_t391, 1, env[1]);
  r1_v104899 = fork_ch_t392;
  instr_fork(&fork_ch_t397, &fork_fun_t396, 1, env[0]);
  r2_v104901 = fork_ch_t397;
  instr_recv(&recv_msg_t399, r1_v104899);
  __v104903 = recv_msg_t399;
  switch(((tll_node)__v104903)->tag) {
    case 0:
      msg1_v104904 = ((tll_node)__v104903)->data[0];
      r1_v104905 = ((tll_node)__v104903)->data[1];
      instr_free_struct(__v104903);
      instr_recv(&recv_msg_t401, r2_v104901);
      __v104906 = recv_msg_t401;
      switch(((tll_node)__v104906)->tag) {
        case 0:
          msg2_v104907 = ((tll_node)__v104906)->data[0];
          r2_v104908 = ((tll_node)__v104906)->data[1];
          instr_free_struct(__v104906);
          switch(((tll_node)msg1_v104904)->tag) {
            case 15:
              xs1_v104909 = ((tll_node)msg1_v104904)->data[0];
              pf1_v104910 = ((tll_node)msg1_v104904)->data[1];
              instr_free_struct(msg1_v104904);
              switch(((tll_node)msg2_v104907)->tag) {
                case 15:
                  xs2_v104911 = ((tll_node)msg2_v104907)->data[0];
                  pf2_v104912 = ((tll_node)msg2_v104907)->data[1];
                  instr_free_struct(msg2_v104907);
                  call_ret_t405 = mergeL_i51(xs1_v104909, xs2_v104911);
                  zs_v104913 = call_ret_t405;
                  instr_struct(&UniqL_t407, 15, 2, zs_v104913, 0);
                  instr_send(&send_ch_t406, env[2], UniqL_t407);
                  c_v104914 = send_ch_t406;
                  instr_close(&close_tmp_t408, r1_v104905);
                  __v104915 = close_tmp_t408;
                  instr_close(&close_tmp_t409, r2_v104908);
                  __v104916 = close_tmp_t409;
                  switch_ret_t404 = 0;
                  break;
              }
              switch_ret_t403 = switch_ret_t404;
              break;
          }
          switch_ret_t402 = switch_ret_t403;
          break;
      }
      switch_ret_t400 = switch_ret_t402;
      break;
  }
  return switch_ret_t400;
}

tll_ptr cmsort_workerL_i57(tll_ptr zs_v104866, tll_ptr c_v104867) {
  tll_ptr call_ret_t385; tll_ptr consUL_t386; tll_ptr consUL_t387;
  tll_ptr lam_clo_t377; tll_ptr lam_clo_t384; tll_ptr lam_clo_t411;
  tll_ptr switch_ret_t372; tll_ptr switch_ret_t378; tll_ptr switch_ret_t388;
  tll_ptr xs0_v104878; tll_ptr ys0_v104879; tll_ptr z0_v104871;
  tll_ptr z1_v104876; tll_ptr zs0_v104872; tll_ptr zs1_v104877;
  switch(((tll_node)zs_v104866)->tag) {
    case 11:
      instr_free_struct(zs_v104866);
      instr_clo(&lam_clo_t377, &lam_fun_t376, 1, c_v104867);
      switch_ret_t372 = lam_clo_t377;
      break;
    case 12:
      z0_v104871 = ((tll_node)zs_v104866)->data[0];
      zs0_v104872 = ((tll_node)zs_v104866)->data[1];
      instr_free_struct(zs_v104866);
      switch(((tll_node)zs0_v104872)->tag) {
        case 11:
          instr_free_struct(zs0_v104872);
          instr_clo(&lam_clo_t384, &lam_fun_t383, 2, z0_v104871, c_v104867);
          switch_ret_t378 = lam_clo_t384;
          break;
        case 12:
          z1_v104876 = ((tll_node)zs0_v104872)->data[0];
          zs1_v104877 = ((tll_node)zs0_v104872)->data[1];
          instr_free_struct(zs0_v104872);
          instr_struct(&consUL_t386, 12, 2, z1_v104876, zs1_v104877);
          instr_struct(&consUL_t387, 12, 2, z0_v104871, consUL_t386);
          call_ret_t385 = splitL_i49(consUL_t387);
          switch(((tll_node)call_ret_t385)->tag) {
            case 0:
              xs0_v104878 = ((tll_node)call_ret_t385)->data[0];
              ys0_v104879 = ((tll_node)call_ret_t385)->data[1];
              instr_free_struct(call_ret_t385);
              instr_clo(&lam_clo_t411, &lam_fun_t410, 3,
                        ys0_v104879, xs0_v104878, c_v104867);
              switch_ret_t388 = lam_clo_t411;
              break;
          }
          switch_ret_t378 = switch_ret_t388;
          break;
      }
      switch_ret_t372 = switch_ret_t378;
      break;
  }
  return switch_ret_t372;
}

tll_ptr lam_fun_t413(tll_ptr c_v104919, tll_env env) {
  tll_ptr call_ret_t412;
  call_ret_t412 = cmsort_workerL_i57(env[0], c_v104919);
  return call_ret_t412;
}

tll_ptr lam_fun_t415(tll_ptr zs_v104917, tll_env env) {
  tll_ptr lam_clo_t414;
  instr_clo(&lam_clo_t414, &lam_fun_t413, 1, zs_v104917);
  return lam_clo_t414;
}

tll_ptr fork_fun_t419(tll_env env) {
  tll_ptr app_ret_t418; tll_ptr call_ret_t417; tll_ptr fork_ret_t421;
  call_ret_t417 = cmsort_workerU_i58(env[1], env[0]);
  instr_app(&app_ret_t418, call_ret_t417, 0);
  instr_free_clo(call_ret_t417);
  fork_ret_t421 = app_ret_t418;
  instr_free_thread(env);
  return fork_ret_t421;
}

tll_ptr lam_fun_t425(tll_ptr __v104921, tll_env env) {
  tll_ptr __v104930; tll_ptr __v104933; tll_ptr c_v104928; tll_ptr c_v104932;
  tll_ptr close_tmp_t424; tll_ptr fork_ch_t420; tll_ptr msg_v104931;
  tll_ptr recv_msg_t422; tll_ptr switch_ret_t423;
  instr_fork(&fork_ch_t420, &fork_fun_t419, 1, env[0]);
  c_v104928 = fork_ch_t420;
  instr_recv(&recv_msg_t422, c_v104928);
  __v104930 = recv_msg_t422;
  switch(((tll_node)__v104930)->tag) {
    case 0:
      msg_v104931 = ((tll_node)__v104930)->data[0];
      c_v104932 = ((tll_node)__v104930)->data[1];
      instr_free_struct(__v104930);
      instr_close(&close_tmp_t424, c_v104932);
      __v104933 = close_tmp_t424;
      switch_ret_t423 = msg_v104931;
      break;
  }
  return switch_ret_t423;
}

tll_ptr cmsortU_i60(tll_ptr zs_v104920) {
  tll_ptr lam_clo_t426;
  instr_clo(&lam_clo_t426, &lam_fun_t425, 1, zs_v104920);
  return lam_clo_t426;
}

tll_ptr lam_fun_t428(tll_ptr zs_v104934, tll_env env) {
  tll_ptr call_ret_t427;
  call_ret_t427 = cmsortU_i60(zs_v104934);
  return call_ret_t427;
}

tll_ptr fork_fun_t432(tll_env env) {
  tll_ptr app_ret_t431; tll_ptr call_ret_t430; tll_ptr fork_ret_t434;
  call_ret_t430 = cmsort_workerL_i57(env[1], env[0]);
  instr_app(&app_ret_t431, call_ret_t430, 0);
  instr_free_clo(call_ret_t430);
  fork_ret_t434 = app_ret_t431;
  instr_free_thread(env);
  return fork_ret_t434;
}

tll_ptr lam_fun_t438(tll_ptr __v104936, tll_env env) {
  tll_ptr __v104945; tll_ptr __v104948; tll_ptr c_v104943; tll_ptr c_v104947;
  tll_ptr close_tmp_t437; tll_ptr fork_ch_t433; tll_ptr msg_v104946;
  tll_ptr recv_msg_t435; tll_ptr switch_ret_t436;
  instr_fork(&fork_ch_t433, &fork_fun_t432, 1, env[0]);
  c_v104943 = fork_ch_t433;
  instr_recv(&recv_msg_t435, c_v104943);
  __v104945 = recv_msg_t435;
  switch(((tll_node)__v104945)->tag) {
    case 0:
      msg_v104946 = ((tll_node)__v104945)->data[0];
      c_v104947 = ((tll_node)__v104945)->data[1];
      instr_free_struct(__v104945);
      instr_close(&close_tmp_t437, c_v104947);
      __v104948 = close_tmp_t437;
      switch_ret_t436 = msg_v104946;
      break;
  }
  return switch_ret_t436;
}

tll_ptr cmsortL_i59(tll_ptr zs_v104935) {
  tll_ptr lam_clo_t439;
  instr_clo(&lam_clo_t439, &lam_fun_t438, 1, zs_v104935);
  return lam_clo_t439;
}

tll_ptr lam_fun_t441(tll_ptr zs_v104949, tll_env env) {
  tll_ptr call_ret_t440;
  call_ret_t440 = cmsortL_i59(zs_v104949);
  return call_ret_t440;
}

tll_ptr get_at_i35(tll_ptr A_v104950, tll_ptr n_v104951, tll_ptr xs_v104952, tll_ptr a_v104953) {
  tll_ptr __v104954; tll_ptr __v104957; tll_ptr call_ret_t485;
  tll_ptr ifte_ret_t488; tll_ptr sub_ret_t486; tll_ptr switch_ret_t484;
  tll_ptr switch_ret_t487; tll_ptr x_v104956; tll_ptr xs_v104955;
  if (n_v104951) {
    switch(((tll_node)xs_v104952)->tag) {
      case 13:
        switch_ret_t484 = a_v104953;
        break;
      case 14:
        __v104954 = ((tll_node)xs_v104952)->data[0];
        xs_v104955 = ((tll_node)xs_v104952)->data[1];
        sub_ret_t486 = n_v104951 - 1;
        call_ret_t485 = get_at_i35(0, sub_ret_t486, xs_v104955, a_v104953);
        switch_ret_t484 = call_ret_t485;
        break;
    }
    ifte_ret_t488 = switch_ret_t484;
  }
  else {
    switch(((tll_node)xs_v104952)->tag) {
      case 13:
        switch_ret_t487 = a_v104953;
        break;
      case 14:
        x_v104956 = ((tll_node)xs_v104952)->data[0];
        __v104957 = ((tll_node)xs_v104952)->data[1];
        switch_ret_t487 = x_v104956;
        break;
    }
    ifte_ret_t488 = switch_ret_t487;
  }
  return ifte_ret_t488;
}

tll_ptr lam_fun_t490(tll_ptr a_v104967, tll_env env) {
  tll_ptr call_ret_t489;
  call_ret_t489 = get_at_i35(env[2], env[1], env[0], a_v104967);
  return call_ret_t489;
}

tll_ptr lam_fun_t492(tll_ptr xs_v104965, tll_env env) {
  tll_ptr lam_clo_t491;
  instr_clo(&lam_clo_t491, &lam_fun_t490, 3, xs_v104965, env[0], env[1]);
  return lam_clo_t491;
}

tll_ptr lam_fun_t494(tll_ptr n_v104962, tll_env env) {
  tll_ptr lam_clo_t493;
  instr_clo(&lam_clo_t493, &lam_fun_t492, 2, n_v104962, env[0]);
  return lam_clo_t493;
}

tll_ptr lam_fun_t496(tll_ptr A_v104958, tll_env env) {
  tll_ptr lam_clo_t495;
  instr_clo(&lam_clo_t495, &lam_fun_t494, 1, A_v104958);
  return lam_clo_t495;
}

tll_ptr string_of_digit_i36(tll_ptr n_v104968) {
  tll_ptr EmptyString_t499; tll_ptr call_ret_t498;
  instr_struct(&EmptyString_t499, 2, 0);
  call_ret_t498 = get_at_i35(0, n_v104968, digits_i34, EmptyString_t499);
  return call_ret_t498;
}

tll_ptr lam_fun_t501(tll_ptr n_v104969, tll_env env) {
  tll_ptr call_ret_t500;
  call_ret_t500 = string_of_digit_i36(n_v104969);
  return call_ret_t500;
}

tll_ptr string_of_nat_i37(tll_ptr n_v104970) {
  tll_ptr call_ret_t503; tll_ptr call_ret_t504; tll_ptr call_ret_t505;
  tll_ptr call_ret_t506; tll_ptr call_ret_t507; tll_ptr call_ret_t508;
  tll_ptr ifte_ret_t509; tll_ptr n_v104972; tll_ptr s_v104971;
  call_ret_t504 = modn_i14(n_v104970, (tll_ptr)10);
  call_ret_t503 = string_of_digit_i36(call_ret_t504);
  s_v104971 = call_ret_t503;
  call_ret_t505 = divn_i13(n_v104970, (tll_ptr)10);
  n_v104972 = call_ret_t505;
  call_ret_t506 = ltn_i6((tll_ptr)0, n_v104972);
  if (call_ret_t506) {
    call_ret_t508 = string_of_nat_i37(n_v104972);
    call_ret_t507 = cats_i15(call_ret_t508, s_v104971);
    ifte_ret_t509 = call_ret_t507;
  }
  else {
    ifte_ret_t509 = s_v104971;
  }
  return ifte_ret_t509;
}

tll_ptr lam_fun_t511(tll_ptr n_v104973, tll_env env) {
  tll_ptr call_ret_t510;
  call_ret_t510 = string_of_nat_i37(n_v104973);
  return call_ret_t510;
}

tll_ptr string_of_listU_i62(tll_ptr xs_v104974) {
  tll_ptr Char_t514; tll_ptr Char_t515; tll_ptr Char_t516; tll_ptr Char_t524;
  tll_ptr Char_t525; tll_ptr Char_t526; tll_ptr Char_t527;
  tll_ptr EmptyString_t517; tll_ptr EmptyString_t528; tll_ptr String_t518;
  tll_ptr String_t519; tll_ptr String_t520; tll_ptr String_t529;
  tll_ptr String_t530; tll_ptr String_t531; tll_ptr String_t532;
  tll_ptr call_ret_t521; tll_ptr call_ret_t522; tll_ptr call_ret_t523;
  tll_ptr call_ret_t533; tll_ptr switch_ret_t513; tll_ptr x_v104975;
  tll_ptr xs_v104976;
  switch(((tll_node)xs_v104974)->tag) {
    case 13:
      instr_struct(&Char_t514, 1, 1, (tll_ptr)110);
      instr_struct(&Char_t515, 1, 1, (tll_ptr)105);
      instr_struct(&Char_t516, 1, 1, (tll_ptr)108);
      instr_struct(&EmptyString_t517, 2, 0);
      instr_struct(&String_t518, 3, 2, Char_t516, EmptyString_t517);
      instr_struct(&String_t519, 3, 2, Char_t515, String_t518);
      instr_struct(&String_t520, 3, 2, Char_t514, String_t519);
      switch_ret_t513 = String_t520;
      break;
    case 14:
      x_v104975 = ((tll_node)xs_v104974)->data[0];
      xs_v104976 = ((tll_node)xs_v104974)->data[1];
      call_ret_t523 = string_of_nat_i37(x_v104975);
      instr_struct(&Char_t524, 1, 1, (tll_ptr)32);
      instr_struct(&Char_t525, 1, 1, (tll_ptr)58);
      instr_struct(&Char_t526, 1, 1, (tll_ptr)58);
      instr_struct(&Char_t527, 1, 1, (tll_ptr)32);
      instr_struct(&EmptyString_t528, 2, 0);
      instr_struct(&String_t529, 3, 2, Char_t527, EmptyString_t528);
      instr_struct(&String_t530, 3, 2, Char_t526, String_t529);
      instr_struct(&String_t531, 3, 2, Char_t525, String_t530);
      instr_struct(&String_t532, 3, 2, Char_t524, String_t531);
      call_ret_t522 = cats_i15(call_ret_t523, String_t532);
      call_ret_t533 = string_of_listU_i62(xs_v104976);
      call_ret_t521 = cats_i15(call_ret_t522, call_ret_t533);
      switch_ret_t513 = call_ret_t521;
      break;
  }
  return switch_ret_t513;
}

tll_ptr lam_fun_t535(tll_ptr xs_v104977, tll_env env) {
  tll_ptr call_ret_t534;
  call_ret_t534 = string_of_listU_i62(xs_v104977);
  return call_ret_t534;
}

tll_ptr string_of_listL_i61(tll_ptr xs_v104978) {
  tll_ptr Char_t538; tll_ptr Char_t539; tll_ptr Char_t540; tll_ptr Char_t548;
  tll_ptr Char_t549; tll_ptr Char_t550; tll_ptr Char_t551;
  tll_ptr EmptyString_t541; tll_ptr EmptyString_t552; tll_ptr String_t542;
  tll_ptr String_t543; tll_ptr String_t544; tll_ptr String_t553;
  tll_ptr String_t554; tll_ptr String_t555; tll_ptr String_t556;
  tll_ptr call_ret_t545; tll_ptr call_ret_t546; tll_ptr call_ret_t547;
  tll_ptr call_ret_t557; tll_ptr switch_ret_t537; tll_ptr x_v104979;
  tll_ptr xs_v104980;
  switch(((tll_node)xs_v104978)->tag) {
    case 11:
      instr_free_struct(xs_v104978);
      instr_struct(&Char_t538, 1, 1, (tll_ptr)110);
      instr_struct(&Char_t539, 1, 1, (tll_ptr)105);
      instr_struct(&Char_t540, 1, 1, (tll_ptr)108);
      instr_struct(&EmptyString_t541, 2, 0);
      instr_struct(&String_t542, 3, 2, Char_t540, EmptyString_t541);
      instr_struct(&String_t543, 3, 2, Char_t539, String_t542);
      instr_struct(&String_t544, 3, 2, Char_t538, String_t543);
      switch_ret_t537 = String_t544;
      break;
    case 12:
      x_v104979 = ((tll_node)xs_v104978)->data[0];
      xs_v104980 = ((tll_node)xs_v104978)->data[1];
      instr_free_struct(xs_v104978);
      call_ret_t547 = string_of_nat_i37(x_v104979);
      instr_struct(&Char_t548, 1, 1, (tll_ptr)32);
      instr_struct(&Char_t549, 1, 1, (tll_ptr)58);
      instr_struct(&Char_t550, 1, 1, (tll_ptr)58);
      instr_struct(&Char_t551, 1, 1, (tll_ptr)32);
      instr_struct(&EmptyString_t552, 2, 0);
      instr_struct(&String_t553, 3, 2, Char_t551, EmptyString_t552);
      instr_struct(&String_t554, 3, 2, Char_t550, String_t553);
      instr_struct(&String_t555, 3, 2, Char_t549, String_t554);
      instr_struct(&String_t556, 3, 2, Char_t548, String_t555);
      call_ret_t546 = cats_i15(call_ret_t547, String_t556);
      call_ret_t557 = string_of_listL_i61(xs_v104980);
      call_ret_t545 = cats_i15(call_ret_t546, call_ret_t557);
      switch_ret_t537 = call_ret_t545;
      break;
  }
  return switch_ret_t537;
}

tll_ptr lam_fun_t559(tll_ptr xs_v104981, tll_env env) {
  tll_ptr call_ret_t558;
  call_ret_t558 = string_of_listL_i61(xs_v104981);
  return call_ret_t558;
}

tll_ptr mkListU_i64(tll_ptr n_v104982) {
  tll_ptr call_ret_t561; tll_ptr consUU_t563; tll_ptr ifte_ret_t565;
  tll_ptr nilUU_t564; tll_ptr sub_ret_t562;
  if (n_v104982) {
    sub_ret_t562 = n_v104982 - 1;
    call_ret_t561 = mkListU_i64(sub_ret_t562);
    instr_struct(&consUU_t563, 14, 2, n_v104982, call_ret_t561);
    ifte_ret_t565 = consUU_t563;
  }
  else {
    instr_struct(&nilUU_t564, 13, 0);
    ifte_ret_t565 = nilUU_t564;
  }
  return ifte_ret_t565;
}

tll_ptr lam_fun_t567(tll_ptr n_v104983, tll_env env) {
  tll_ptr call_ret_t566;
  call_ret_t566 = mkListU_i64(n_v104983);
  return call_ret_t566;
}

tll_ptr mkListL_i63(tll_ptr n_v104984) {
  tll_ptr call_ret_t569; tll_ptr consUL_t571; tll_ptr ifte_ret_t573;
  tll_ptr nilUL_t572; tll_ptr sub_ret_t570;
  if (n_v104984) {
    sub_ret_t570 = n_v104984 - 1;
    call_ret_t569 = mkListL_i63(sub_ret_t570);
    instr_struct(&consUL_t571, 12, 2, n_v104984, call_ret_t569);
    ifte_ret_t573 = consUL_t571;
  }
  else {
    instr_struct(&nilUL_t572, 11, 0);
    ifte_ret_t573 = nilUL_t572;
  }
  return ifte_ret_t573;
}

tll_ptr lam_fun_t575(tll_ptr n_v104985, tll_env env) {
  tll_ptr call_ret_t574;
  call_ret_t574 = mkListL_i63(n_v104985);
  return call_ret_t574;
}

int main() {
  instr_init();
  tll_ptr Char_t443; tll_ptr Char_t446; tll_ptr Char_t449; tll_ptr Char_t452;
  tll_ptr Char_t455; tll_ptr Char_t458; tll_ptr Char_t461; tll_ptr Char_t464;
  tll_ptr Char_t467; tll_ptr Char_t470; tll_ptr EmptyString_t444;
  tll_ptr EmptyString_t447; tll_ptr EmptyString_t450;
  tll_ptr EmptyString_t453; tll_ptr EmptyString_t456;
  tll_ptr EmptyString_t459; tll_ptr EmptyString_t462;
  tll_ptr EmptyString_t465; tll_ptr EmptyString_t468;
  tll_ptr EmptyString_t471; tll_ptr String_t445; tll_ptr String_t448;
  tll_ptr String_t451; tll_ptr String_t454; tll_ptr String_t457;
  tll_ptr String_t460; tll_ptr String_t463; tll_ptr String_t466;
  tll_ptr String_t469; tll_ptr String_t472; tll_ptr call_ret_t577;
  tll_ptr call_ret_t578; tll_ptr consUU_t474; tll_ptr consUU_t475;
  tll_ptr consUU_t476; tll_ptr consUU_t477; tll_ptr consUU_t478;
  tll_ptr consUU_t479; tll_ptr consUU_t480; tll_ptr consUU_t481;
  tll_ptr consUU_t482; tll_ptr consUU_t483; tll_ptr lam_clo_t101;
  tll_ptr lam_clo_t111; tll_ptr lam_clo_t119; tll_ptr lam_clo_t12;
  tll_ptr lam_clo_t127; tll_ptr lam_clo_t133; tll_ptr lam_clo_t146;
  tll_ptr lam_clo_t159; tll_ptr lam_clo_t16; tll_ptr lam_clo_t172;
  tll_ptr lam_clo_t182; tll_ptr lam_clo_t192; tll_ptr lam_clo_t202;
  tll_ptr lam_clo_t212; tll_ptr lam_clo_t221; tll_ptr lam_clo_t230;
  tll_ptr lam_clo_t247; tll_ptr lam_clo_t26; tll_ptr lam_clo_t264;
  tll_ptr lam_clo_t280; tll_ptr lam_clo_t296; tll_ptr lam_clo_t311;
  tll_ptr lam_clo_t326; tll_ptr lam_clo_t37; tll_ptr lam_clo_t371;
  tll_ptr lam_clo_t416; tll_ptr lam_clo_t429; tll_ptr lam_clo_t442;
  tll_ptr lam_clo_t48; tll_ptr lam_clo_t497; tll_ptr lam_clo_t502;
  tll_ptr lam_clo_t512; tll_ptr lam_clo_t536; tll_ptr lam_clo_t560;
  tll_ptr lam_clo_t568; tll_ptr lam_clo_t576; tll_ptr lam_clo_t58;
  tll_ptr lam_clo_t6; tll_ptr lam_clo_t69; tll_ptr lam_clo_t74;
  tll_ptr lam_clo_t83; tll_ptr lam_clo_t92; tll_ptr nilUU_t473;
  tll_ptr sorted_v104987; tll_ptr test_v104986;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i65 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i66 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i67 = lam_clo_t16;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 0);
  ltenclo_i68 = lam_clo_t26;
  instr_clo(&lam_clo_t37, &lam_fun_t36, 0);
  gtenclo_i69 = lam_clo_t37;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  ltnclo_i70 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  gtnclo_i71 = lam_clo_t58;
  instr_clo(&lam_clo_t69, &lam_fun_t68, 0);
  eqnclo_i72 = lam_clo_t69;
  instr_clo(&lam_clo_t74, &lam_fun_t73, 0);
  predclo_i73 = lam_clo_t74;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i74 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i75 = lam_clo_t92;
  instr_clo(&lam_clo_t101, &lam_fun_t100, 0);
  mulnclo_i76 = lam_clo_t101;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 0);
  divnclo_i77 = lam_clo_t111;
  instr_clo(&lam_clo_t119, &lam_fun_t118, 0);
  modnclo_i78 = lam_clo_t119;
  instr_clo(&lam_clo_t127, &lam_fun_t126, 0);
  catsclo_i79 = lam_clo_t127;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 0);
  strlenclo_i80 = lam_clo_t133;
  instr_clo(&lam_clo_t146, &lam_fun_t145, 0);
  lenUUclo_i81 = lam_clo_t146;
  instr_clo(&lam_clo_t159, &lam_fun_t158, 0);
  lenULclo_i82 = lam_clo_t159;
  instr_clo(&lam_clo_t172, &lam_fun_t171, 0);
  lenLLclo_i83 = lam_clo_t172;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 0);
  appendUUclo_i84 = lam_clo_t182;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 0);
  appendULclo_i85 = lam_clo_t192;
  instr_clo(&lam_clo_t202, &lam_fun_t201, 0);
  appendLLclo_i86 = lam_clo_t202;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  readlineclo_i87 = lam_clo_t212;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 0);
  printclo_i88 = lam_clo_t221;
  instr_clo(&lam_clo_t230, &lam_fun_t229, 0);
  prerrclo_i89 = lam_clo_t230;
  instr_clo(&lam_clo_t247, &lam_fun_t246, 0);
  splitUclo_i90 = lam_clo_t247;
  instr_clo(&lam_clo_t264, &lam_fun_t263, 0);
  splitLclo_i91 = lam_clo_t264;
  instr_clo(&lam_clo_t280, &lam_fun_t279, 0);
  mergeUclo_i92 = lam_clo_t280;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 0);
  mergeLclo_i93 = lam_clo_t296;
  instr_clo(&lam_clo_t311, &lam_fun_t310, 0);
  msortUclo_i94 = lam_clo_t311;
  instr_clo(&lam_clo_t326, &lam_fun_t325, 0);
  msortLclo_i95 = lam_clo_t326;
  instr_clo(&lam_clo_t371, &lam_fun_t370, 0);
  cmsort_workerUclo_i96 = lam_clo_t371;
  instr_clo(&lam_clo_t416, &lam_fun_t415, 0);
  cmsort_workerLclo_i97 = lam_clo_t416;
  instr_clo(&lam_clo_t429, &lam_fun_t428, 0);
  cmsortUclo_i98 = lam_clo_t429;
  instr_clo(&lam_clo_t442, &lam_fun_t441, 0);
  cmsortLclo_i99 = lam_clo_t442;
  instr_struct(&Char_t443, 1, 1, (tll_ptr)48);
  instr_struct(&EmptyString_t444, 2, 0);
  instr_struct(&String_t445, 3, 2, Char_t443, EmptyString_t444);
  instr_struct(&Char_t446, 1, 1, (tll_ptr)49);
  instr_struct(&EmptyString_t447, 2, 0);
  instr_struct(&String_t448, 3, 2, Char_t446, EmptyString_t447);
  instr_struct(&Char_t449, 1, 1, (tll_ptr)50);
  instr_struct(&EmptyString_t450, 2, 0);
  instr_struct(&String_t451, 3, 2, Char_t449, EmptyString_t450);
  instr_struct(&Char_t452, 1, 1, (tll_ptr)51);
  instr_struct(&EmptyString_t453, 2, 0);
  instr_struct(&String_t454, 3, 2, Char_t452, EmptyString_t453);
  instr_struct(&Char_t455, 1, 1, (tll_ptr)52);
  instr_struct(&EmptyString_t456, 2, 0);
  instr_struct(&String_t457, 3, 2, Char_t455, EmptyString_t456);
  instr_struct(&Char_t458, 1, 1, (tll_ptr)53);
  instr_struct(&EmptyString_t459, 2, 0);
  instr_struct(&String_t460, 3, 2, Char_t458, EmptyString_t459);
  instr_struct(&Char_t461, 1, 1, (tll_ptr)54);
  instr_struct(&EmptyString_t462, 2, 0);
  instr_struct(&String_t463, 3, 2, Char_t461, EmptyString_t462);
  instr_struct(&Char_t464, 1, 1, (tll_ptr)55);
  instr_struct(&EmptyString_t465, 2, 0);
  instr_struct(&String_t466, 3, 2, Char_t464, EmptyString_t465);
  instr_struct(&Char_t467, 1, 1, (tll_ptr)56);
  instr_struct(&EmptyString_t468, 2, 0);
  instr_struct(&String_t469, 3, 2, Char_t467, EmptyString_t468);
  instr_struct(&Char_t470, 1, 1, (tll_ptr)57);
  instr_struct(&EmptyString_t471, 2, 0);
  instr_struct(&String_t472, 3, 2, Char_t470, EmptyString_t471);
  instr_struct(&nilUU_t473, 13, 0);
  instr_struct(&consUU_t474, 14, 2, String_t472, nilUU_t473);
  instr_struct(&consUU_t475, 14, 2, String_t469, consUU_t474);
  instr_struct(&consUU_t476, 14, 2, String_t466, consUU_t475);
  instr_struct(&consUU_t477, 14, 2, String_t463, consUU_t476);
  instr_struct(&consUU_t478, 14, 2, String_t460, consUU_t477);
  instr_struct(&consUU_t479, 14, 2, String_t457, consUU_t478);
  instr_struct(&consUU_t480, 14, 2, String_t454, consUU_t479);
  instr_struct(&consUU_t481, 14, 2, String_t451, consUU_t480);
  instr_struct(&consUU_t482, 14, 2, String_t448, consUU_t481);
  instr_struct(&consUU_t483, 14, 2, String_t445, consUU_t482);
  digits_i34 = consUU_t483;
  instr_clo(&lam_clo_t497, &lam_fun_t496, 0);
  get_atclo_i100 = lam_clo_t497;
  instr_clo(&lam_clo_t502, &lam_fun_t501, 0);
  string_of_digitclo_i101 = lam_clo_t502;
  instr_clo(&lam_clo_t512, &lam_fun_t511, 0);
  string_of_natclo_i102 = lam_clo_t512;
  instr_clo(&lam_clo_t536, &lam_fun_t535, 0);
  string_of_listUclo_i103 = lam_clo_t536;
  instr_clo(&lam_clo_t560, &lam_fun_t559, 0);
  string_of_listLclo_i104 = lam_clo_t560;
  instr_clo(&lam_clo_t568, &lam_fun_t567, 0);
  mkListUclo_i105 = lam_clo_t568;
  instr_clo(&lam_clo_t576, &lam_fun_t575, 0);
  mkListLclo_i106 = lam_clo_t576;
  call_ret_t577 = mkListU_i64((tll_ptr)100000);
  test_v104986 = call_ret_t577;
  call_ret_t578 = msortU_i54(test_v104986);
  sorted_v104987 = call_ret_t578;
  return 0;
}

