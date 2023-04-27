#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v10678, tll_ptr b2_v10679);
tll_ptr orb_i2(tll_ptr b1_v10683, tll_ptr b2_v10684);
tll_ptr notb_i3(tll_ptr b_v10688);
tll_ptr lten_i4(tll_ptr x_v10690, tll_ptr y_v10691);
tll_ptr gten_i5(tll_ptr x_v10695, tll_ptr y_v10696);
tll_ptr ltn_i6(tll_ptr x_v10700, tll_ptr y_v10701);
tll_ptr gtn_i7(tll_ptr x_v10705, tll_ptr y_v10706);
tll_ptr eqn_i8(tll_ptr x_v10710, tll_ptr y_v10711);
tll_ptr pred_i9(tll_ptr x_v10715);
tll_ptr addn_i10(tll_ptr x_v10717, tll_ptr y_v10718);
tll_ptr subn_i11(tll_ptr x_v10722, tll_ptr y_v10723);
tll_ptr muln_i12(tll_ptr x_v10727, tll_ptr y_v10728);
tll_ptr divn_i13(tll_ptr x_v10732, tll_ptr y_v10733);
tll_ptr modn_i14(tll_ptr x_v10737, tll_ptr y_v10738);
tll_ptr cats_i15(tll_ptr s1_v10742, tll_ptr s2_v10743);
tll_ptr strlen_i16(tll_ptr s_v10749);
tll_ptr lenUU_i43(tll_ptr A_v10753, tll_ptr xs_v10754);
tll_ptr lenUL_i42(tll_ptr A_v10762, tll_ptr xs_v10763);
tll_ptr lenLL_i40(tll_ptr A_v10771, tll_ptr xs_v10772);
tll_ptr appendUU_i47(tll_ptr A_v10780, tll_ptr xs_v10781, tll_ptr ys_v10782);
tll_ptr appendUL_i46(tll_ptr A_v10791, tll_ptr xs_v10792, tll_ptr ys_v10793);
tll_ptr appendLL_i44(tll_ptr A_v10802, tll_ptr xs_v10803, tll_ptr ys_v10804);
tll_ptr readline_i25(tll_ptr __v10813);
tll_ptr print_i26(tll_ptr s_v10828);
tll_ptr prerr_i27(tll_ptr s_v10839);
tll_ptr get_at_i29(tll_ptr A_v10850, tll_ptr n_v10851, tll_ptr xs_v10852, tll_ptr a_v10853);
tll_ptr string_of_digit_i30(tll_ptr n_v10868);
tll_ptr string_of_nat_i31(tll_ptr n_v10870);
tll_ptr pow_i32(tll_ptr n_v10874, tll_ptr m_v10875);
tll_ptr alice_i36(tll_ptr a_v10879, tll_ptr p_v10880, tll_ptr g_v10881, tll_ptr ch_v10882);
tll_ptr bob_i37(tll_ptr b_v10914, tll_ptr p_v10915, tll_ptr g_v10916, tll_ptr ch_v10917);
tll_ptr key_exchange_i38(tll_ptr __v10951);

tll_ptr addnclo_i57;
tll_ptr aliceclo_i77;
tll_ptr andbclo_i48;
tll_ptr appendLLclo_i69;
tll_ptr appendULclo_i68;
tll_ptr appendUUclo_i67;
tll_ptr bobclo_i78;
tll_ptr catsclo_i62;
tll_ptr digits_i28;
tll_ptr divnclo_i60;
tll_ptr eqnclo_i55;
tll_ptr get_atclo_i73;
tll_ptr gtenclo_i52;
tll_ptr gtnclo_i54;
tll_ptr key_exchangeclo_i79;
tll_ptr lenLLclo_i66;
tll_ptr lenULclo_i65;
tll_ptr lenUUclo_i64;
tll_ptr ltenclo_i51;
tll_ptr ltnclo_i53;
tll_ptr modnclo_i61;
tll_ptr mulnclo_i59;
tll_ptr notbclo_i50;
tll_ptr orbclo_i49;
tll_ptr powclo_i76;
tll_ptr predclo_i56;
tll_ptr prerrclo_i72;
tll_ptr printclo_i71;
tll_ptr readlineclo_i70;
tll_ptr string_of_digitclo_i74;
tll_ptr string_of_natclo_i75;
tll_ptr strlenclo_i63;
tll_ptr subnclo_i58;

tll_ptr andb_i1(tll_ptr b1_v10678, tll_ptr b2_v10679) {
  tll_ptr ifte_ret_t1;
  if (b1_v10678) {
    ifte_ret_t1 = b2_v10679;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v10682, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v10682);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v10680, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v10680);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v10683, tll_ptr b2_v10684) {
  tll_ptr ifte_ret_t7;
  if (b1_v10683) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v10684;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v10687, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v10687);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v10685, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v10685);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v10688) {
  tll_ptr ifte_ret_t13;
  if (b_v10688) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v10689, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v10689);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v10690, tll_ptr y_v10691) {
  tll_ptr add_ret_t18; tll_ptr add_ret_t19; tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  if (x_v10690) {
    if (y_v10691) {
      add_ret_t18 = x_v10690 - 1;
      add_ret_t19 = y_v10691 - 1;
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

tll_ptr lam_fun_t23(tll_ptr y_v10694, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v10694);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v10692, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v10692);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v10695, tll_ptr y_v10696) {
  tll_ptr add_ret_t28; tll_ptr add_ret_t29; tll_ptr call_ret_t27;
  tll_ptr ifte_ret_t30; tll_ptr ifte_ret_t31; tll_ptr ifte_ret_t32;
  if (x_v10695) {
    if (y_v10696) {
      add_ret_t28 = x_v10695 - 1;
      add_ret_t29 = y_v10696 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v10696) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v10699, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v10699);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v10697, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v10697);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v10700, tll_ptr y_v10701) {
  tll_ptr add_ret_t39; tll_ptr add_ret_t40; tll_ptr call_ret_t38;
  tll_ptr ifte_ret_t41; tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t43;
  if (x_v10700) {
    if (y_v10701) {
      add_ret_t39 = x_v10700 - 1;
      add_ret_t40 = y_v10701 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v10701) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v10704, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v10704);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v10702, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v10702);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v10705, tll_ptr y_v10706) {
  tll_ptr add_ret_t50; tll_ptr add_ret_t51; tll_ptr call_ret_t49;
  tll_ptr ifte_ret_t52; tll_ptr ifte_ret_t53;
  if (x_v10705) {
    if (y_v10706) {
      add_ret_t50 = x_v10705 - 1;
      add_ret_t51 = y_v10706 - 1;
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

tll_ptr lam_fun_t55(tll_ptr y_v10709, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v10709);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v10707, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v10707);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v10710, tll_ptr y_v10711) {
  tll_ptr add_ret_t60; tll_ptr add_ret_t61; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t62; tll_ptr ifte_ret_t63; tll_ptr ifte_ret_t64;
  if (x_v10710) {
    if (y_v10711) {
      add_ret_t60 = x_v10710 - 1;
      add_ret_t61 = y_v10711 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v10711) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v10714, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v10714);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v10712, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v10712);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v10715) {
  tll_ptr add_ret_t70; tll_ptr ifte_ret_t71;
  if (x_v10715) {
    add_ret_t70 = x_v10715 - 1;
    ifte_ret_t71 = add_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v10716, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v10716);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v10717, tll_ptr y_v10718) {
  tll_ptr add_ret_t76; tll_ptr add_ret_t77; tll_ptr call_ret_t75;
  tll_ptr ifte_ret_t78;
  if (x_v10717) {
    add_ret_t76 = x_v10717 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v10718);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v10718;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v10721, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v10721);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v10719, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v10719);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v10722, tll_ptr y_v10723) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v10723) {
    call_ret_t85 = pred_i9(x_v10722);
    add_ret_t86 = y_v10723 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v10722;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v10726, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v10726);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v10724, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v10724);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v10727, tll_ptr y_v10728) {
  tll_ptr add_ret_t95; tll_ptr call_ret_t93; tll_ptr call_ret_t94;
  tll_ptr ifte_ret_t96;
  if (x_v10727) {
    add_ret_t95 = x_v10727 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v10728);
    call_ret_t93 = addn_i10(y_v10728, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v10731, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v10731);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v10729, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v10729);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v10732, tll_ptr y_v10733) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v10732, y_v10733);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v10732, y_v10733);
    call_ret_t103 = divn_i13(call_ret_t104, y_v10733);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v10736, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v10736);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v10734, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v10734);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v10737, tll_ptr y_v10738) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v10737, y_v10738);
  call_ret_t113 = muln_i12(call_ret_t114, y_v10738);
  call_ret_t112 = subn_i11(x_v10737, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v10741, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v10741);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v10739, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v10739);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v10742, tll_ptr s2_v10743) {
  tll_ptr String_t122; tll_ptr c_v10744; tll_ptr call_ret_t121;
  tll_ptr s1_v10745; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v10742)->tag) {
    case 2:
      switch_ret_t120 = s2_v10743;
      break;
    case 3:
      c_v10744 = ((tll_node)s1_v10742)->data[0];
      s1_v10745 = ((tll_node)s1_v10742)->data[1];
      call_ret_t121 = cats_i15(s1_v10745, s2_v10743);
      instr_struct(&String_t122, 3, 2, c_v10744, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v10748, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v10748);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v10746, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v10746);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v10749) {
  tll_ptr __v10750; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v10751; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v10749)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v10750 = ((tll_node)s_v10749)->data[0];
      s_v10751 = ((tll_node)s_v10749)->data[1];
      call_ret_t129 = strlen_i16(s_v10751);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v10752, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v10752);
  return call_ret_t131;
}

tll_ptr lenUU_i43(tll_ptr A_v10753, tll_ptr xs_v10754) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v10757; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v10755; tll_ptr xs_v10756; tll_ptr xs_v10758;
  switch(((tll_node)xs_v10754)->tag) {
    case 12:
      instr_struct(&nilUU_t135, 12, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 13:
      x_v10755 = ((tll_node)xs_v10754)->data[0];
      xs_v10756 = ((tll_node)xs_v10754)->data[1];
      call_ret_t137 = lenUU_i43(0, xs_v10756);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v10757 = ((tll_node)call_ret_t137)->data[0];
          xs_v10758 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v10757 + 1;
          instr_struct(&consUU_t140, 13, 2, x_v10755, xs_v10758);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v10761, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i43(env[0], xs_v10761);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v10759, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v10759);
  return lam_clo_t144;
}

tll_ptr lenUL_i42(tll_ptr A_v10762, tll_ptr xs_v10763) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v10766; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v10764; tll_ptr xs_v10765; tll_ptr xs_v10767;
  switch(((tll_node)xs_v10763)->tag) {
    case 10:
      instr_free_struct(xs_v10763);
      instr_struct(&nilUL_t148, 10, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 11:
      x_v10764 = ((tll_node)xs_v10763)->data[0];
      xs_v10765 = ((tll_node)xs_v10763)->data[1];
      instr_free_struct(xs_v10763);
      call_ret_t150 = lenUL_i42(0, xs_v10765);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v10766 = ((tll_node)call_ret_t150)->data[0];
          xs_v10767 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v10766 + 1;
          instr_struct(&consUL_t153, 11, 2, x_v10764, xs_v10767);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v10770, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i42(env[0], xs_v10770);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v10768, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v10768);
  return lam_clo_t157;
}

tll_ptr lenLL_i40(tll_ptr A_v10771, tll_ptr xs_v10772) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v10775; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v10773; tll_ptr xs_v10774; tll_ptr xs_v10776;
  switch(((tll_node)xs_v10772)->tag) {
    case 6:
      instr_free_struct(xs_v10772);
      instr_struct(&nilLL_t161, 6, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 7:
      x_v10773 = ((tll_node)xs_v10772)->data[0];
      xs_v10774 = ((tll_node)xs_v10772)->data[1];
      instr_free_struct(xs_v10772);
      call_ret_t163 = lenLL_i40(0, xs_v10774);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v10775 = ((tll_node)call_ret_t163)->data[0];
          xs_v10776 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v10775 + 1;
          instr_struct(&consLL_t166, 7, 2, x_v10773, xs_v10776);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v10779, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i40(env[0], xs_v10779);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v10777, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v10777);
  return lam_clo_t170;
}

tll_ptr appendUU_i47(tll_ptr A_v10780, tll_ptr xs_v10781, tll_ptr ys_v10782) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v10783; tll_ptr xs_v10784;
  switch(((tll_node)xs_v10781)->tag) {
    case 12:
      switch_ret_t173 = ys_v10782;
      break;
    case 13:
      x_v10783 = ((tll_node)xs_v10781)->data[0];
      xs_v10784 = ((tll_node)xs_v10781)->data[1];
      call_ret_t174 = appendUU_i47(0, xs_v10784, ys_v10782);
      instr_struct(&consUU_t175, 13, 2, x_v10783, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v10790, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i47(env[1], env[0], ys_v10790);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v10788, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v10788, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v10785, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v10785);
  return lam_clo_t180;
}

tll_ptr appendUL_i46(tll_ptr A_v10791, tll_ptr xs_v10792, tll_ptr ys_v10793) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v10794; tll_ptr xs_v10795;
  switch(((tll_node)xs_v10792)->tag) {
    case 10:
      instr_free_struct(xs_v10792);
      switch_ret_t183 = ys_v10793;
      break;
    case 11:
      x_v10794 = ((tll_node)xs_v10792)->data[0];
      xs_v10795 = ((tll_node)xs_v10792)->data[1];
      instr_free_struct(xs_v10792);
      call_ret_t184 = appendUL_i46(0, xs_v10795, ys_v10793);
      instr_struct(&consUL_t185, 11, 2, x_v10794, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v10801, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i46(env[1], env[0], ys_v10801);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v10799, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v10799, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v10796, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v10796);
  return lam_clo_t190;
}

tll_ptr appendLL_i44(tll_ptr A_v10802, tll_ptr xs_v10803, tll_ptr ys_v10804) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v10805; tll_ptr xs_v10806;
  switch(((tll_node)xs_v10803)->tag) {
    case 6:
      instr_free_struct(xs_v10803);
      switch_ret_t193 = ys_v10804;
      break;
    case 7:
      x_v10805 = ((tll_node)xs_v10803)->data[0];
      xs_v10806 = ((tll_node)xs_v10803)->data[1];
      instr_free_struct(xs_v10803);
      call_ret_t194 = appendLL_i44(0, xs_v10806, ys_v10804);
      instr_struct(&consLL_t195, 7, 2, x_v10805, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v10812, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i44(env[1], env[0], ys_v10812);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v10810, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v10810, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v10807, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v10807);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v10814, tll_env env) {
  tll_ptr __v10823; tll_ptr ch_v10821; tll_ptr ch_v10822; tll_ptr ch_v10825;
  tll_ptr ch_v10826; tll_ptr prim_ch_t203; tll_ptr recv_msg_t205;
  tll_ptr s_v10824; tll_ptr send_ch_t204; tll_ptr send_ch_t207;
  tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v10821 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v10821, (tll_ptr)1);
  ch_v10822 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v10822);
  __v10823 = recv_msg_t205;
  switch(((tll_node)__v10823)->tag) {
    case 0:
      s_v10824 = ((tll_node)__v10823)->data[0];
      ch_v10825 = ((tll_node)__v10823)->data[1];
      instr_free_struct(__v10823);
      instr_send(&send_ch_t207, ch_v10825, (tll_ptr)0);
      ch_v10826 = send_ch_t207;
      switch_ret_t206 = s_v10824;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v10813) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v10827, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v10827);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v10829, tll_env env) {
  tll_ptr ch_v10834; tll_ptr ch_v10835; tll_ptr ch_v10836; tll_ptr ch_v10837;
  tll_ptr prim_ch_t213; tll_ptr send_ch_t214; tll_ptr send_ch_t215;
  tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v10834 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v10834, (tll_ptr)1);
  ch_v10835 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v10835, env[0]);
  ch_v10836 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v10836, (tll_ptr)0);
  ch_v10837 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v10828) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v10828);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v10838, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v10838);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v10840, tll_env env) {
  tll_ptr ch_v10845; tll_ptr ch_v10846; tll_ptr ch_v10847; tll_ptr ch_v10848;
  tll_ptr prim_ch_t222; tll_ptr send_ch_t223; tll_ptr send_ch_t224;
  tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v10845 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v10845, (tll_ptr)1);
  ch_v10846 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v10846, env[0]);
  ch_v10847 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v10847, (tll_ptr)0);
  ch_v10848 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v10839) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v10839);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v10849, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v10849);
  return call_ret_t228;
}

tll_ptr get_at_i29(tll_ptr A_v10850, tll_ptr n_v10851, tll_ptr xs_v10852, tll_ptr a_v10853) {
  tll_ptr __v10854; tll_ptr __v10857; tll_ptr add_ret_t274;
  tll_ptr call_ret_t273; tll_ptr ifte_ret_t276; tll_ptr switch_ret_t272;
  tll_ptr switch_ret_t275; tll_ptr x_v10856; tll_ptr xs_v10855;
  if (n_v10851) {
    switch(((tll_node)xs_v10852)->tag) {
      case 12:
        switch_ret_t272 = a_v10853;
        break;
      case 13:
        __v10854 = ((tll_node)xs_v10852)->data[0];
        xs_v10855 = ((tll_node)xs_v10852)->data[1];
        add_ret_t274 = n_v10851 - 1;
        call_ret_t273 = get_at_i29(0, add_ret_t274, xs_v10855, a_v10853);
        switch_ret_t272 = call_ret_t273;
        break;
    }
    ifte_ret_t276 = switch_ret_t272;
  }
  else {
    switch(((tll_node)xs_v10852)->tag) {
      case 12:
        switch_ret_t275 = a_v10853;
        break;
      case 13:
        x_v10856 = ((tll_node)xs_v10852)->data[0];
        __v10857 = ((tll_node)xs_v10852)->data[1];
        switch_ret_t275 = x_v10856;
        break;
    }
    ifte_ret_t276 = switch_ret_t275;
  }
  return ifte_ret_t276;
}

tll_ptr lam_fun_t278(tll_ptr a_v10867, tll_env env) {
  tll_ptr call_ret_t277;
  call_ret_t277 = get_at_i29(env[2], env[1], env[0], a_v10867);
  return call_ret_t277;
}

tll_ptr lam_fun_t280(tll_ptr xs_v10865, tll_env env) {
  tll_ptr lam_clo_t279;
  instr_clo(&lam_clo_t279, &lam_fun_t278, 3, xs_v10865, env[0], env[1]);
  return lam_clo_t279;
}

tll_ptr lam_fun_t282(tll_ptr n_v10862, tll_env env) {
  tll_ptr lam_clo_t281;
  instr_clo(&lam_clo_t281, &lam_fun_t280, 2, n_v10862, env[0]);
  return lam_clo_t281;
}

tll_ptr lam_fun_t284(tll_ptr A_v10858, tll_env env) {
  tll_ptr lam_clo_t283;
  instr_clo(&lam_clo_t283, &lam_fun_t282, 1, A_v10858);
  return lam_clo_t283;
}

tll_ptr string_of_digit_i30(tll_ptr n_v10868) {
  tll_ptr EmptyString_t287; tll_ptr call_ret_t286;
  instr_struct(&EmptyString_t287, 2, 0);
  call_ret_t286 = get_at_i29(0, n_v10868, digits_i28, EmptyString_t287);
  return call_ret_t286;
}

tll_ptr lam_fun_t289(tll_ptr n_v10869, tll_env env) {
  tll_ptr call_ret_t288;
  call_ret_t288 = string_of_digit_i30(n_v10869);
  return call_ret_t288;
}

tll_ptr string_of_nat_i31(tll_ptr n_v10870) {
  tll_ptr call_ret_t291; tll_ptr call_ret_t292; tll_ptr call_ret_t293;
  tll_ptr call_ret_t294; tll_ptr call_ret_t295; tll_ptr call_ret_t296;
  tll_ptr ifte_ret_t297; tll_ptr n_v10872; tll_ptr s_v10871;
  call_ret_t292 = modn_i14(n_v10870, (tll_ptr)10);
  call_ret_t291 = string_of_digit_i30(call_ret_t292);
  s_v10871 = call_ret_t291;
  call_ret_t293 = divn_i13(n_v10870, (tll_ptr)10);
  n_v10872 = call_ret_t293;
  call_ret_t294 = ltn_i6((tll_ptr)0, n_v10872);
  if (call_ret_t294) {
    call_ret_t296 = string_of_nat_i31(n_v10872);
    call_ret_t295 = cats_i15(call_ret_t296, s_v10871);
    ifte_ret_t297 = call_ret_t295;
  }
  else {
    ifte_ret_t297 = s_v10871;
  }
  return ifte_ret_t297;
}

tll_ptr lam_fun_t299(tll_ptr n_v10873, tll_env env) {
  tll_ptr call_ret_t298;
  call_ret_t298 = string_of_nat_i31(n_v10873);
  return call_ret_t298;
}

tll_ptr pow_i32(tll_ptr n_v10874, tll_ptr m_v10875) {
  tll_ptr add_ret_t303; tll_ptr call_ret_t301; tll_ptr call_ret_t302;
  tll_ptr ifte_ret_t304;
  if (m_v10875) {
    add_ret_t303 = m_v10875 - 1;
    call_ret_t302 = pow_i32(n_v10874, add_ret_t303);
    call_ret_t301 = muln_i12(n_v10874, call_ret_t302);
    ifte_ret_t304 = call_ret_t301;
  }
  else {
    ifte_ret_t304 = (tll_ptr)1;
  }
  return ifte_ret_t304;
}

tll_ptr lam_fun_t306(tll_ptr m_v10878, tll_env env) {
  tll_ptr call_ret_t305;
  call_ret_t305 = pow_i32(env[0], m_v10878);
  return call_ret_t305;
}

tll_ptr lam_fun_t308(tll_ptr n_v10876, tll_env env) {
  tll_ptr lam_clo_t307;
  instr_clo(&lam_clo_t307, &lam_fun_t306, 1, n_v10876);
  return lam_clo_t307;
}

tll_ptr lam_fun_t328(tll_ptr __v10883, tll_env env) {
  tll_ptr B_v10899; tll_ptr Char_t324; tll_ptr EmptyString_t325;
  tll_ptr String_t326; tll_ptr __v10898; tll_ptr app_ret_t327;
  tll_ptr b_v10896; tll_ptr call_ret_t310; tll_ptr call_ret_t311;
  tll_ptr call_ret_t319; tll_ptr call_ret_t320; tll_ptr call_ret_t321;
  tll_ptr call_ret_t322; tll_ptr call_ret_t323; tll_ptr ch_v10894;
  tll_ptr ch_v10897; tll_ptr ch_v10900; tll_ptr ch_v10902;
  tll_ptr pair_struct_t313; tll_ptr pair_struct_t317; tll_ptr pf_v10901;
  tll_ptr recv_msg_t315; tll_ptr s_v10903; tll_ptr send_ch_t312;
  tll_ptr switch_ret_t314; tll_ptr switch_ret_t316; tll_ptr switch_ret_t318;
  tll_ptr x_v10895;
  call_ret_t311 = pow_i32(env[1], env[3]);
  call_ret_t310 = modn_i14(call_ret_t311, env[2]);
  x_v10895 = call_ret_t310;
  instr_send(&send_ch_t312, env[0], x_v10895);
  ch_v10894 = send_ch_t312;
  instr_struct(&pair_struct_t313, 0, 2, 0, ch_v10894);
  switch(((tll_node)pair_struct_t313)->tag) {
    case 0:
      b_v10896 = ((tll_node)pair_struct_t313)->data[0];
      ch_v10897 = ((tll_node)pair_struct_t313)->data[1];
      instr_free_struct(pair_struct_t313);
      instr_recv(&recv_msg_t315, ch_v10897);
      __v10898 = recv_msg_t315;
      switch(((tll_node)__v10898)->tag) {
        case 0:
          B_v10899 = ((tll_node)__v10898)->data[0];
          ch_v10900 = ((tll_node)__v10898)->data[1];
          instr_free_struct(__v10898);
          instr_struct(&pair_struct_t317, 0, 2, 0, ch_v10900);
          switch(((tll_node)pair_struct_t317)->tag) {
            case 0:
              pf_v10901 = ((tll_node)pair_struct_t317)->data[0];
              ch_v10902 = ((tll_node)pair_struct_t317)->data[1];
              instr_free_struct(pair_struct_t317);
              call_ret_t320 = pow_i32(B_v10899, env[3]);
              call_ret_t319 = modn_i14(call_ret_t320, env[2]);
              s_v10903 = call_ret_t319;
              call_ret_t323 = string_of_nat_i31(s_v10903);
              instr_struct(&Char_t324, 1, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t325, 2, 0);
              instr_struct(&String_t326, 3, 2, Char_t324, EmptyString_t325);
              call_ret_t322 = cats_i15(call_ret_t323, String_t326);
              call_ret_t321 = print_i26(call_ret_t322);
              instr_app(&app_ret_t327, call_ret_t321, 0);
              instr_free_clo(call_ret_t321);
              switch_ret_t318 = app_ret_t327;
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

tll_ptr alice_i36(tll_ptr a_v10879, tll_ptr p_v10880, tll_ptr g_v10881, tll_ptr ch_v10882) {
  tll_ptr lam_clo_t329;
  instr_clo(&lam_clo_t329, &lam_fun_t328, 4,
            ch_v10882, g_v10881, p_v10880, a_v10879);
  return lam_clo_t329;
}

tll_ptr lam_fun_t331(tll_ptr ch_v10913, tll_env env) {
  tll_ptr call_ret_t330;
  call_ret_t330 = alice_i36(env[2], env[1], env[0], ch_v10913);
  return call_ret_t330;
}

tll_ptr lam_fun_t333(tll_ptr g_v10911, tll_env env) {
  tll_ptr lam_clo_t332;
  instr_clo(&lam_clo_t332, &lam_fun_t331, 3, g_v10911, env[0], env[1]);
  return lam_clo_t332;
}

tll_ptr lam_fun_t335(tll_ptr p_v10908, tll_env env) {
  tll_ptr lam_clo_t334;
  instr_clo(&lam_clo_t334, &lam_fun_t333, 2, p_v10908, env[0]);
  return lam_clo_t334;
}

tll_ptr lam_fun_t337(tll_ptr a_v10904, tll_env env) {
  tll_ptr lam_clo_t336;
  instr_clo(&lam_clo_t336, &lam_fun_t335, 1, a_v10904);
  return lam_clo_t336;
}

tll_ptr lam_fun_t358(tll_ptr __v10918, tll_env env) {
  tll_ptr A_v10933; tll_ptr Char_t354; tll_ptr EmptyString_t355;
  tll_ptr String_t356; tll_ptr __v10932; tll_ptr __v10940; tll_ptr a_v10930;
  tll_ptr app_ret_t357; tll_ptr call_ret_t345; tll_ptr call_ret_t346;
  tll_ptr call_ret_t348; tll_ptr call_ret_t349; tll_ptr call_ret_t351;
  tll_ptr call_ret_t352; tll_ptr call_ret_t353; tll_ptr ch_v10931;
  tll_ptr ch_v10934; tll_ptr ch_v10936; tll_ptr ch_v10937;
  tll_ptr close_tmp_t350; tll_ptr pair_struct_t339; tll_ptr pair_struct_t343;
  tll_ptr pf_v10935; tll_ptr recv_msg_t341; tll_ptr s_v10939;
  tll_ptr send_ch_t347; tll_ptr switch_ret_t340; tll_ptr switch_ret_t342;
  tll_ptr switch_ret_t344; tll_ptr x_v10938;
  instr_struct(&pair_struct_t339, 0, 2, 0, env[0]);
  switch(((tll_node)pair_struct_t339)->tag) {
    case 0:
      a_v10930 = ((tll_node)pair_struct_t339)->data[0];
      ch_v10931 = ((tll_node)pair_struct_t339)->data[1];
      instr_free_struct(pair_struct_t339);
      instr_recv(&recv_msg_t341, ch_v10931);
      __v10932 = recv_msg_t341;
      switch(((tll_node)__v10932)->tag) {
        case 0:
          A_v10933 = ((tll_node)__v10932)->data[0];
          ch_v10934 = ((tll_node)__v10932)->data[1];
          instr_free_struct(__v10932);
          instr_struct(&pair_struct_t343, 0, 2, 0, ch_v10934);
          switch(((tll_node)pair_struct_t343)->tag) {
            case 0:
              pf_v10935 = ((tll_node)pair_struct_t343)->data[0];
              ch_v10936 = ((tll_node)pair_struct_t343)->data[1];
              instr_free_struct(pair_struct_t343);
              call_ret_t346 = pow_i32(env[1], env[3]);
              call_ret_t345 = modn_i14(call_ret_t346, env[2]);
              x_v10938 = call_ret_t345;
              instr_send(&send_ch_t347, ch_v10936, x_v10938);
              ch_v10937 = send_ch_t347;
              call_ret_t349 = pow_i32(A_v10933, env[3]);
              call_ret_t348 = modn_i14(call_ret_t349, env[2]);
              s_v10939 = call_ret_t348;
              instr_close(&close_tmp_t350, ch_v10937);
              __v10940 = close_tmp_t350;
              call_ret_t353 = string_of_nat_i31(s_v10939);
              instr_struct(&Char_t354, 1, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t355, 2, 0);
              instr_struct(&String_t356, 3, 2, Char_t354, EmptyString_t355);
              call_ret_t352 = cats_i15(call_ret_t353, String_t356);
              call_ret_t351 = print_i26(call_ret_t352);
              instr_app(&app_ret_t357, call_ret_t351, 0);
              instr_free_clo(call_ret_t351);
              switch_ret_t344 = app_ret_t357;
              break;
          }
          switch_ret_t342 = switch_ret_t344;
          break;
      }
      switch_ret_t340 = switch_ret_t342;
      break;
  }
  return switch_ret_t340;
}

tll_ptr bob_i37(tll_ptr b_v10914, tll_ptr p_v10915, tll_ptr g_v10916, tll_ptr ch_v10917) {
  tll_ptr lam_clo_t359;
  instr_clo(&lam_clo_t359, &lam_fun_t358, 4,
            ch_v10917, g_v10916, p_v10915, b_v10914);
  return lam_clo_t359;
}

tll_ptr lam_fun_t361(tll_ptr ch_v10950, tll_env env) {
  tll_ptr call_ret_t360;
  call_ret_t360 = bob_i37(env[2], env[1], env[0], ch_v10950);
  return call_ret_t360;
}

tll_ptr lam_fun_t363(tll_ptr g_v10948, tll_env env) {
  tll_ptr lam_clo_t362;
  instr_clo(&lam_clo_t362, &lam_fun_t361, 3, g_v10948, env[0], env[1]);
  return lam_clo_t362;
}

tll_ptr lam_fun_t365(tll_ptr p_v10945, tll_env env) {
  tll_ptr lam_clo_t364;
  instr_clo(&lam_clo_t364, &lam_fun_t363, 2, p_v10945, env[0]);
  return lam_clo_t364;
}

tll_ptr lam_fun_t367(tll_ptr b_v10941, tll_env env) {
  tll_ptr lam_clo_t366;
  instr_clo(&lam_clo_t366, &lam_fun_t365, 1, b_v10941);
  return lam_clo_t366;
}

tll_ptr fork_fun_t371(tll_env env) {
  tll_ptr app_ret_t370; tll_ptr call_ret_t369; tll_ptr fork_ret_t373;
  call_ret_t369 = alice_i36((tll_ptr)4, (tll_ptr)23, (tll_ptr)5, env[0]);
  instr_app(&app_ret_t370, call_ret_t369, 0);
  instr_free_clo(call_ret_t369);
  fork_ret_t373 = app_ret_t370;
  instr_free_thread(env);
  return fork_ret_t373;
}

tll_ptr fork_fun_t378(tll_env env) {
  tll_ptr __v10968; tll_ptr app_ret_t377; tll_ptr c0_v10970;
  tll_ptr c_v10969; tll_ptr call_ret_t376; tll_ptr fork_ret_t380;
  tll_ptr recv_msg_t374; tll_ptr switch_ret_t375;
  instr_recv(&recv_msg_t374, env[0]);
  __v10968 = recv_msg_t374;
  switch(((tll_node)__v10968)->tag) {
    case 0:
      c_v10969 = ((tll_node)__v10968)->data[0];
      c0_v10970 = ((tll_node)__v10968)->data[1];
      instr_free_struct(__v10968);
      call_ret_t376 = bob_i37((tll_ptr)3, (tll_ptr)23, (tll_ptr)5, c_v10969);
      instr_app(&app_ret_t377, call_ret_t376, 0);
      instr_free_clo(call_ret_t376);
      switch_ret_t375 = app_ret_t377;
      break;
  }
  fork_ret_t380 = switch_ret_t375;
  instr_free_thread(env);
  return fork_ret_t380;
}

tll_ptr lam_fun_t383(tll_ptr __v10952, tll_env env) {
  tll_ptr c0_v10963; tll_ptr c0_v10971; tll_ptr c_v10961;
  tll_ptr close_tmp_t382; tll_ptr fork_ch_t372; tll_ptr fork_ch_t379;
  tll_ptr send_ch_t381;
  instr_fork(&fork_ch_t372, &fork_fun_t371, 0);
  c_v10961 = fork_ch_t372;
  instr_fork(&fork_ch_t379, &fork_fun_t378, 0);
  c0_v10963 = fork_ch_t379;
  instr_send(&send_ch_t381, c0_v10963, c_v10961);
  c0_v10971 = send_ch_t381;
  instr_close(&close_tmp_t382, c0_v10971);
  return close_tmp_t382;
}

tll_ptr key_exchange_i38(tll_ptr __v10951) {
  tll_ptr lam_clo_t384;
  instr_clo(&lam_clo_t384, &lam_fun_t383, 0);
  return lam_clo_t384;
}

tll_ptr lam_fun_t386(tll_ptr __v10972, tll_env env) {
  tll_ptr call_ret_t385;
  call_ret_t385 = key_exchange_i38(__v10972);
  return call_ret_t385;
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
  tll_ptr String_t257; tll_ptr String_t260; tll_ptr __v10973;
  tll_ptr app_ret_t389; tll_ptr call_ret_t388; tll_ptr consUU_t262;
  tll_ptr consUU_t263; tll_ptr consUU_t264; tll_ptr consUU_t265;
  tll_ptr consUU_t266; tll_ptr consUU_t267; tll_ptr consUU_t268;
  tll_ptr consUU_t269; tll_ptr consUU_t270; tll_ptr consUU_t271;
  tll_ptr lam_clo_t101; tll_ptr lam_clo_t111; tll_ptr lam_clo_t119;
  tll_ptr lam_clo_t12; tll_ptr lam_clo_t127; tll_ptr lam_clo_t133;
  tll_ptr lam_clo_t146; tll_ptr lam_clo_t159; tll_ptr lam_clo_t16;
  tll_ptr lam_clo_t172; tll_ptr lam_clo_t182; tll_ptr lam_clo_t192;
  tll_ptr lam_clo_t202; tll_ptr lam_clo_t212; tll_ptr lam_clo_t221;
  tll_ptr lam_clo_t230; tll_ptr lam_clo_t26; tll_ptr lam_clo_t285;
  tll_ptr lam_clo_t290; tll_ptr lam_clo_t300; tll_ptr lam_clo_t309;
  tll_ptr lam_clo_t338; tll_ptr lam_clo_t368; tll_ptr lam_clo_t37;
  tll_ptr lam_clo_t387; tll_ptr lam_clo_t48; tll_ptr lam_clo_t58;
  tll_ptr lam_clo_t6; tll_ptr lam_clo_t69; tll_ptr lam_clo_t74;
  tll_ptr lam_clo_t83; tll_ptr lam_clo_t92; tll_ptr nilUU_t261;
  tll_ptr sleep_tmp_t390;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i48 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i49 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i50 = lam_clo_t16;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 0);
  ltenclo_i51 = lam_clo_t26;
  instr_clo(&lam_clo_t37, &lam_fun_t36, 0);
  gtenclo_i52 = lam_clo_t37;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  ltnclo_i53 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  gtnclo_i54 = lam_clo_t58;
  instr_clo(&lam_clo_t69, &lam_fun_t68, 0);
  eqnclo_i55 = lam_clo_t69;
  instr_clo(&lam_clo_t74, &lam_fun_t73, 0);
  predclo_i56 = lam_clo_t74;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i57 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i58 = lam_clo_t92;
  instr_clo(&lam_clo_t101, &lam_fun_t100, 0);
  mulnclo_i59 = lam_clo_t101;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 0);
  divnclo_i60 = lam_clo_t111;
  instr_clo(&lam_clo_t119, &lam_fun_t118, 0);
  modnclo_i61 = lam_clo_t119;
  instr_clo(&lam_clo_t127, &lam_fun_t126, 0);
  catsclo_i62 = lam_clo_t127;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 0);
  strlenclo_i63 = lam_clo_t133;
  instr_clo(&lam_clo_t146, &lam_fun_t145, 0);
  lenUUclo_i64 = lam_clo_t146;
  instr_clo(&lam_clo_t159, &lam_fun_t158, 0);
  lenULclo_i65 = lam_clo_t159;
  instr_clo(&lam_clo_t172, &lam_fun_t171, 0);
  lenLLclo_i66 = lam_clo_t172;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 0);
  appendUUclo_i67 = lam_clo_t182;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 0);
  appendULclo_i68 = lam_clo_t192;
  instr_clo(&lam_clo_t202, &lam_fun_t201, 0);
  appendLLclo_i69 = lam_clo_t202;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  readlineclo_i70 = lam_clo_t212;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 0);
  printclo_i71 = lam_clo_t221;
  instr_clo(&lam_clo_t230, &lam_fun_t229, 0);
  prerrclo_i72 = lam_clo_t230;
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
  get_atclo_i73 = lam_clo_t285;
  instr_clo(&lam_clo_t290, &lam_fun_t289, 0);
  string_of_digitclo_i74 = lam_clo_t290;
  instr_clo(&lam_clo_t300, &lam_fun_t299, 0);
  string_of_natclo_i75 = lam_clo_t300;
  instr_clo(&lam_clo_t309, &lam_fun_t308, 0);
  powclo_i76 = lam_clo_t309;
  instr_clo(&lam_clo_t338, &lam_fun_t337, 0);
  aliceclo_i77 = lam_clo_t338;
  instr_clo(&lam_clo_t368, &lam_fun_t367, 0);
  bobclo_i78 = lam_clo_t368;
  instr_clo(&lam_clo_t387, &lam_fun_t386, 0);
  key_exchangeclo_i79 = lam_clo_t387;
  call_ret_t388 = key_exchange_i38(0);
  instr_app(&app_ret_t389, call_ret_t388, 0);
  instr_free_clo(call_ret_t388);
  __v10973 = app_ret_t389;
  instr_sleep(&sleep_tmp_t390, (tll_ptr)1);
  return 0;
}

