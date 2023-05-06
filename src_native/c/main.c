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
  tll_ptr lten_ret_t17;
  instr_lten(&lten_ret_t17, x_v10690, y_v10691);
  return lten_ret_t17;
}

tll_ptr lam_fun_t19(tll_ptr y_v10694, tll_env env) {
  tll_ptr call_ret_t18;
  call_ret_t18 = lten_i4(env[0], y_v10694);
  return call_ret_t18;
}

tll_ptr lam_fun_t21(tll_ptr x_v10692, tll_env env) {
  tll_ptr lam_clo_t20;
  instr_clo(&lam_clo_t20, &lam_fun_t19, 1, x_v10692);
  return lam_clo_t20;
}

tll_ptr gten_i5(tll_ptr x_v10695, tll_ptr y_v10696) {
  tll_ptr gten_ret_t23;
  instr_gten(&gten_ret_t23, x_v10695, y_v10696);
  return gten_ret_t23;
}

tll_ptr lam_fun_t25(tll_ptr y_v10699, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = gten_i5(env[0], y_v10699);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr x_v10697, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, x_v10697);
  return lam_clo_t26;
}

tll_ptr ltn_i6(tll_ptr x_v10700, tll_ptr y_v10701) {
  tll_ptr ltn_ret_t29;
  instr_ltn(&ltn_ret_t29, x_v10700, y_v10701);
  return ltn_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v10704, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = ltn_i6(env[0], y_v10704);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v10702, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v10702);
  return lam_clo_t32;
}

tll_ptr gtn_i7(tll_ptr x_v10705, tll_ptr y_v10706) {
  tll_ptr gtn_ret_t35;
  instr_gtn(&gtn_ret_t35, x_v10705, y_v10706);
  return gtn_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v10709, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = gtn_i7(env[0], y_v10709);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v10707, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v10707);
  return lam_clo_t38;
}

tll_ptr eqn_i8(tll_ptr x_v10710, tll_ptr y_v10711) {
  tll_ptr eqn_ret_t41;
  instr_eqn(&eqn_ret_t41, x_v10710, y_v10711);
  return eqn_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v10714, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = eqn_i8(env[0], y_v10714);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v10712, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v10712);
  return lam_clo_t44;
}

tll_ptr pred_i9(tll_ptr x_v10715) {
  tll_ptr add_ret_t47; tll_ptr ifte_ret_t48;
  if (x_v10715) {
    add_ret_t47 = x_v10715 - 1;
    ifte_ret_t48 = add_ret_t47;
  }
  else {
    ifte_ret_t48 = (tll_ptr)0;
  }
  return ifte_ret_t48;
}

tll_ptr lam_fun_t50(tll_ptr x_v10716, tll_env env) {
  tll_ptr call_ret_t49;
  call_ret_t49 = pred_i9(x_v10716);
  return call_ret_t49;
}

tll_ptr addn_i10(tll_ptr x_v10717, tll_ptr y_v10718) {
  tll_ptr addn_ret_t52;
  instr_addn(&addn_ret_t52, x_v10717, y_v10718);
  return addn_ret_t52;
}

tll_ptr lam_fun_t54(tll_ptr y_v10721, tll_env env) {
  tll_ptr call_ret_t53;
  call_ret_t53 = addn_i10(env[0], y_v10721);
  return call_ret_t53;
}

tll_ptr lam_fun_t56(tll_ptr x_v10719, tll_env env) {
  tll_ptr lam_clo_t55;
  instr_clo(&lam_clo_t55, &lam_fun_t54, 1, x_v10719);
  return lam_clo_t55;
}

tll_ptr subn_i11(tll_ptr x_v10722, tll_ptr y_v10723) {
  tll_ptr add_ret_t60; tll_ptr call_ret_t58; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t61;
  if (y_v10723) {
    call_ret_t59 = pred_i9(x_v10722);
    add_ret_t60 = y_v10723 - 1;
    call_ret_t58 = subn_i11(call_ret_t59, add_ret_t60);
    ifte_ret_t61 = call_ret_t58;
  }
  else {
    ifte_ret_t61 = x_v10722;
  }
  return ifte_ret_t61;
}

tll_ptr lam_fun_t63(tll_ptr y_v10726, tll_env env) {
  tll_ptr call_ret_t62;
  call_ret_t62 = subn_i11(env[0], y_v10726);
  return call_ret_t62;
}

tll_ptr lam_fun_t65(tll_ptr x_v10724, tll_env env) {
  tll_ptr lam_clo_t64;
  instr_clo(&lam_clo_t64, &lam_fun_t63, 1, x_v10724);
  return lam_clo_t64;
}

tll_ptr muln_i12(tll_ptr x_v10727, tll_ptr y_v10728) {
  tll_ptr muln_ret_t67;
  instr_muln(&muln_ret_t67, x_v10727, y_v10728);
  return muln_ret_t67;
}

tll_ptr lam_fun_t69(tll_ptr y_v10731, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = muln_i12(env[0], y_v10731);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr x_v10729, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, x_v10729);
  return lam_clo_t70;
}

tll_ptr divn_i13(tll_ptr x_v10732, tll_ptr y_v10733) {
  tll_ptr divn_ret_t73;
  instr_divn(&divn_ret_t73, x_v10732, y_v10733);
  return divn_ret_t73;
}

tll_ptr lam_fun_t75(tll_ptr y_v10736, tll_env env) {
  tll_ptr call_ret_t74;
  call_ret_t74 = divn_i13(env[0], y_v10736);
  return call_ret_t74;
}

tll_ptr lam_fun_t77(tll_ptr x_v10734, tll_env env) {
  tll_ptr lam_clo_t76;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 1, x_v10734);
  return lam_clo_t76;
}

tll_ptr modn_i14(tll_ptr x_v10737, tll_ptr y_v10738) {
  tll_ptr modn_ret_t79;
  instr_modn(&modn_ret_t79, x_v10737, y_v10738);
  return modn_ret_t79;
}

tll_ptr lam_fun_t81(tll_ptr y_v10741, tll_env env) {
  tll_ptr call_ret_t80;
  call_ret_t80 = modn_i14(env[0], y_v10741);
  return call_ret_t80;
}

tll_ptr lam_fun_t83(tll_ptr x_v10739, tll_env env) {
  tll_ptr lam_clo_t82;
  instr_clo(&lam_clo_t82, &lam_fun_t81, 1, x_v10739);
  return lam_clo_t82;
}

tll_ptr cats_i15(tll_ptr s1_v10742, tll_ptr s2_v10743) {
  tll_ptr String_t87; tll_ptr c_v10744; tll_ptr call_ret_t86;
  tll_ptr s1_v10745; tll_ptr switch_ret_t85;
  switch(((tll_node)s1_v10742)->tag) {
    case 2:
      switch_ret_t85 = s2_v10743;
      break;
    case 3:
      c_v10744 = ((tll_node)s1_v10742)->data[0];
      s1_v10745 = ((tll_node)s1_v10742)->data[1];
      call_ret_t86 = cats_i15(s1_v10745, s2_v10743);
      instr_struct(&String_t87, 3, 2, c_v10744, call_ret_t86);
      switch_ret_t85 = String_t87;
      break;
  }
  return switch_ret_t85;
}

tll_ptr lam_fun_t89(tll_ptr s2_v10748, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = cats_i15(env[0], s2_v10748);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr s1_v10746, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, s1_v10746);
  return lam_clo_t90;
}

tll_ptr strlen_i16(tll_ptr s_v10749) {
  tll_ptr __v10750; tll_ptr add_ret_t95; tll_ptr call_ret_t94;
  tll_ptr s_v10751; tll_ptr switch_ret_t93;
  switch(((tll_node)s_v10749)->tag) {
    case 2:
      switch_ret_t93 = (tll_ptr)0;
      break;
    case 3:
      __v10750 = ((tll_node)s_v10749)->data[0];
      s_v10751 = ((tll_node)s_v10749)->data[1];
      call_ret_t94 = strlen_i16(s_v10751);
      add_ret_t95 = call_ret_t94 + 1;
      switch_ret_t93 = add_ret_t95;
      break;
  }
  return switch_ret_t93;
}

tll_ptr lam_fun_t97(tll_ptr s_v10752, tll_env env) {
  tll_ptr call_ret_t96;
  call_ret_t96 = strlen_i16(s_v10752);
  return call_ret_t96;
}

tll_ptr lenUU_i43(tll_ptr A_v10753, tll_ptr xs_v10754) {
  tll_ptr add_ret_t104; tll_ptr call_ret_t102; tll_ptr consUU_t105;
  tll_ptr n_v10757; tll_ptr nilUU_t100; tll_ptr pair_struct_t101;
  tll_ptr pair_struct_t106; tll_ptr switch_ret_t103; tll_ptr switch_ret_t99;
  tll_ptr x_v10755; tll_ptr xs_v10756; tll_ptr xs_v10758;
  switch(((tll_node)xs_v10754)->tag) {
    case 12:
      instr_struct(&nilUU_t100, 12, 0);
      instr_struct(&pair_struct_t101, 0, 2, (tll_ptr)0, nilUU_t100);
      switch_ret_t99 = pair_struct_t101;
      break;
    case 13:
      x_v10755 = ((tll_node)xs_v10754)->data[0];
      xs_v10756 = ((tll_node)xs_v10754)->data[1];
      call_ret_t102 = lenUU_i43(0, xs_v10756);
      switch(((tll_node)call_ret_t102)->tag) {
        case 0:
          n_v10757 = ((tll_node)call_ret_t102)->data[0];
          xs_v10758 = ((tll_node)call_ret_t102)->data[1];
          instr_free_struct(call_ret_t102);
          add_ret_t104 = n_v10757 + 1;
          instr_struct(&consUU_t105, 13, 2, x_v10755, xs_v10758);
          instr_struct(&pair_struct_t106, 0, 2, add_ret_t104, consUU_t105);
          switch_ret_t103 = pair_struct_t106;
          break;
      }
      switch_ret_t99 = switch_ret_t103;
      break;
  }
  return switch_ret_t99;
}

tll_ptr lam_fun_t108(tll_ptr xs_v10761, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = lenUU_i43(env[0], xs_v10761);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr A_v10759, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, A_v10759);
  return lam_clo_t109;
}

tll_ptr lenUL_i42(tll_ptr A_v10762, tll_ptr xs_v10763) {
  tll_ptr add_ret_t117; tll_ptr call_ret_t115; tll_ptr consUL_t118;
  tll_ptr n_v10766; tll_ptr nilUL_t113; tll_ptr pair_struct_t114;
  tll_ptr pair_struct_t119; tll_ptr switch_ret_t112; tll_ptr switch_ret_t116;
  tll_ptr x_v10764; tll_ptr xs_v10765; tll_ptr xs_v10767;
  switch(((tll_node)xs_v10763)->tag) {
    case 10:
      instr_free_struct(xs_v10763);
      instr_struct(&nilUL_t113, 10, 0);
      instr_struct(&pair_struct_t114, 0, 2, (tll_ptr)0, nilUL_t113);
      switch_ret_t112 = pair_struct_t114;
      break;
    case 11:
      x_v10764 = ((tll_node)xs_v10763)->data[0];
      xs_v10765 = ((tll_node)xs_v10763)->data[1];
      instr_free_struct(xs_v10763);
      call_ret_t115 = lenUL_i42(0, xs_v10765);
      switch(((tll_node)call_ret_t115)->tag) {
        case 0:
          n_v10766 = ((tll_node)call_ret_t115)->data[0];
          xs_v10767 = ((tll_node)call_ret_t115)->data[1];
          instr_free_struct(call_ret_t115);
          add_ret_t117 = n_v10766 + 1;
          instr_struct(&consUL_t118, 11, 2, x_v10764, xs_v10767);
          instr_struct(&pair_struct_t119, 0, 2, add_ret_t117, consUL_t118);
          switch_ret_t116 = pair_struct_t119;
          break;
      }
      switch_ret_t112 = switch_ret_t116;
      break;
  }
  return switch_ret_t112;
}

tll_ptr lam_fun_t121(tll_ptr xs_v10770, tll_env env) {
  tll_ptr call_ret_t120;
  call_ret_t120 = lenUL_i42(env[0], xs_v10770);
  return call_ret_t120;
}

tll_ptr lam_fun_t123(tll_ptr A_v10768, tll_env env) {
  tll_ptr lam_clo_t122;
  instr_clo(&lam_clo_t122, &lam_fun_t121, 1, A_v10768);
  return lam_clo_t122;
}

tll_ptr lenLL_i40(tll_ptr A_v10771, tll_ptr xs_v10772) {
  tll_ptr add_ret_t130; tll_ptr call_ret_t128; tll_ptr consLL_t131;
  tll_ptr n_v10775; tll_ptr nilLL_t126; tll_ptr pair_struct_t127;
  tll_ptr pair_struct_t132; tll_ptr switch_ret_t125; tll_ptr switch_ret_t129;
  tll_ptr x_v10773; tll_ptr xs_v10774; tll_ptr xs_v10776;
  switch(((tll_node)xs_v10772)->tag) {
    case 6:
      instr_free_struct(xs_v10772);
      instr_struct(&nilLL_t126, 6, 0);
      instr_struct(&pair_struct_t127, 0, 2, (tll_ptr)0, nilLL_t126);
      switch_ret_t125 = pair_struct_t127;
      break;
    case 7:
      x_v10773 = ((tll_node)xs_v10772)->data[0];
      xs_v10774 = ((tll_node)xs_v10772)->data[1];
      instr_free_struct(xs_v10772);
      call_ret_t128 = lenLL_i40(0, xs_v10774);
      switch(((tll_node)call_ret_t128)->tag) {
        case 0:
          n_v10775 = ((tll_node)call_ret_t128)->data[0];
          xs_v10776 = ((tll_node)call_ret_t128)->data[1];
          instr_free_struct(call_ret_t128);
          add_ret_t130 = n_v10775 + 1;
          instr_struct(&consLL_t131, 7, 2, x_v10773, xs_v10776);
          instr_struct(&pair_struct_t132, 0, 2, add_ret_t130, consLL_t131);
          switch_ret_t129 = pair_struct_t132;
          break;
      }
      switch_ret_t125 = switch_ret_t129;
      break;
  }
  return switch_ret_t125;
}

tll_ptr lam_fun_t134(tll_ptr xs_v10779, tll_env env) {
  tll_ptr call_ret_t133;
  call_ret_t133 = lenLL_i40(env[0], xs_v10779);
  return call_ret_t133;
}

tll_ptr lam_fun_t136(tll_ptr A_v10777, tll_env env) {
  tll_ptr lam_clo_t135;
  instr_clo(&lam_clo_t135, &lam_fun_t134, 1, A_v10777);
  return lam_clo_t135;
}

tll_ptr appendUU_i47(tll_ptr A_v10780, tll_ptr xs_v10781, tll_ptr ys_v10782) {
  tll_ptr call_ret_t139; tll_ptr consUU_t140; tll_ptr switch_ret_t138;
  tll_ptr x_v10783; tll_ptr xs_v10784;
  switch(((tll_node)xs_v10781)->tag) {
    case 12:
      switch_ret_t138 = ys_v10782;
      break;
    case 13:
      x_v10783 = ((tll_node)xs_v10781)->data[0];
      xs_v10784 = ((tll_node)xs_v10781)->data[1];
      call_ret_t139 = appendUU_i47(0, xs_v10784, ys_v10782);
      instr_struct(&consUU_t140, 13, 2, x_v10783, call_ret_t139);
      switch_ret_t138 = consUU_t140;
      break;
  }
  return switch_ret_t138;
}

tll_ptr lam_fun_t142(tll_ptr ys_v10790, tll_env env) {
  tll_ptr call_ret_t141;
  call_ret_t141 = appendUU_i47(env[1], env[0], ys_v10790);
  return call_ret_t141;
}

tll_ptr lam_fun_t144(tll_ptr xs_v10788, tll_env env) {
  tll_ptr lam_clo_t143;
  instr_clo(&lam_clo_t143, &lam_fun_t142, 2, xs_v10788, env[0]);
  return lam_clo_t143;
}

tll_ptr lam_fun_t146(tll_ptr A_v10785, tll_env env) {
  tll_ptr lam_clo_t145;
  instr_clo(&lam_clo_t145, &lam_fun_t144, 1, A_v10785);
  return lam_clo_t145;
}

tll_ptr appendUL_i46(tll_ptr A_v10791, tll_ptr xs_v10792, tll_ptr ys_v10793) {
  tll_ptr call_ret_t149; tll_ptr consUL_t150; tll_ptr switch_ret_t148;
  tll_ptr x_v10794; tll_ptr xs_v10795;
  switch(((tll_node)xs_v10792)->tag) {
    case 10:
      instr_free_struct(xs_v10792);
      switch_ret_t148 = ys_v10793;
      break;
    case 11:
      x_v10794 = ((tll_node)xs_v10792)->data[0];
      xs_v10795 = ((tll_node)xs_v10792)->data[1];
      instr_free_struct(xs_v10792);
      call_ret_t149 = appendUL_i46(0, xs_v10795, ys_v10793);
      instr_struct(&consUL_t150, 11, 2, x_v10794, call_ret_t149);
      switch_ret_t148 = consUL_t150;
      break;
  }
  return switch_ret_t148;
}

tll_ptr lam_fun_t152(tll_ptr ys_v10801, tll_env env) {
  tll_ptr call_ret_t151;
  call_ret_t151 = appendUL_i46(env[1], env[0], ys_v10801);
  return call_ret_t151;
}

tll_ptr lam_fun_t154(tll_ptr xs_v10799, tll_env env) {
  tll_ptr lam_clo_t153;
  instr_clo(&lam_clo_t153, &lam_fun_t152, 2, xs_v10799, env[0]);
  return lam_clo_t153;
}

tll_ptr lam_fun_t156(tll_ptr A_v10796, tll_env env) {
  tll_ptr lam_clo_t155;
  instr_clo(&lam_clo_t155, &lam_fun_t154, 1, A_v10796);
  return lam_clo_t155;
}

tll_ptr appendLL_i44(tll_ptr A_v10802, tll_ptr xs_v10803, tll_ptr ys_v10804) {
  tll_ptr call_ret_t159; tll_ptr consLL_t160; tll_ptr switch_ret_t158;
  tll_ptr x_v10805; tll_ptr xs_v10806;
  switch(((tll_node)xs_v10803)->tag) {
    case 6:
      instr_free_struct(xs_v10803);
      switch_ret_t158 = ys_v10804;
      break;
    case 7:
      x_v10805 = ((tll_node)xs_v10803)->data[0];
      xs_v10806 = ((tll_node)xs_v10803)->data[1];
      instr_free_struct(xs_v10803);
      call_ret_t159 = appendLL_i44(0, xs_v10806, ys_v10804);
      instr_struct(&consLL_t160, 7, 2, x_v10805, call_ret_t159);
      switch_ret_t158 = consLL_t160;
      break;
  }
  return switch_ret_t158;
}

tll_ptr lam_fun_t162(tll_ptr ys_v10812, tll_env env) {
  tll_ptr call_ret_t161;
  call_ret_t161 = appendLL_i44(env[1], env[0], ys_v10812);
  return call_ret_t161;
}

tll_ptr lam_fun_t164(tll_ptr xs_v10810, tll_env env) {
  tll_ptr lam_clo_t163;
  instr_clo(&lam_clo_t163, &lam_fun_t162, 2, xs_v10810, env[0]);
  return lam_clo_t163;
}

tll_ptr lam_fun_t166(tll_ptr A_v10807, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, A_v10807);
  return lam_clo_t165;
}

tll_ptr lam_fun_t173(tll_ptr __v10814, tll_env env) {
  tll_ptr __v10823; tll_ptr ch_v10821; tll_ptr ch_v10822; tll_ptr ch_v10825;
  tll_ptr ch_v10826; tll_ptr prim_ch_t168; tll_ptr recv_msg_t170;
  tll_ptr s_v10824; tll_ptr send_ch_t169; tll_ptr send_ch_t172;
  tll_ptr switch_ret_t171;
  instr_open(&prim_ch_t168, &proc_stdin);
  ch_v10821 = prim_ch_t168;
  instr_send(&send_ch_t169, ch_v10821, (tll_ptr)1);
  ch_v10822 = send_ch_t169;
  instr_recv(&recv_msg_t170, ch_v10822);
  __v10823 = recv_msg_t170;
  switch(((tll_node)__v10823)->tag) {
    case 0:
      s_v10824 = ((tll_node)__v10823)->data[0];
      ch_v10825 = ((tll_node)__v10823)->data[1];
      instr_free_struct(__v10823);
      instr_send(&send_ch_t172, ch_v10825, (tll_ptr)0);
      ch_v10826 = send_ch_t172;
      switch_ret_t171 = s_v10824;
      break;
  }
  return switch_ret_t171;
}

tll_ptr readline_i25(tll_ptr __v10813) {
  tll_ptr lam_clo_t174;
  instr_clo(&lam_clo_t174, &lam_fun_t173, 0);
  return lam_clo_t174;
}

tll_ptr lam_fun_t176(tll_ptr __v10827, tll_env env) {
  tll_ptr call_ret_t175;
  call_ret_t175 = readline_i25(__v10827);
  return call_ret_t175;
}

tll_ptr lam_fun_t182(tll_ptr __v10829, tll_env env) {
  tll_ptr ch_v10834; tll_ptr ch_v10835; tll_ptr ch_v10836; tll_ptr ch_v10837;
  tll_ptr prim_ch_t178; tll_ptr send_ch_t179; tll_ptr send_ch_t180;
  tll_ptr send_ch_t181;
  instr_open(&prim_ch_t178, &proc_stdout);
  ch_v10834 = prim_ch_t178;
  instr_send(&send_ch_t179, ch_v10834, (tll_ptr)1);
  ch_v10835 = send_ch_t179;
  instr_send(&send_ch_t180, ch_v10835, env[0]);
  ch_v10836 = send_ch_t180;
  instr_send(&send_ch_t181, ch_v10836, (tll_ptr)0);
  ch_v10837 = send_ch_t181;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v10828) {
  tll_ptr lam_clo_t183;
  instr_clo(&lam_clo_t183, &lam_fun_t182, 1, s_v10828);
  return lam_clo_t183;
}

tll_ptr lam_fun_t185(tll_ptr s_v10838, tll_env env) {
  tll_ptr call_ret_t184;
  call_ret_t184 = print_i26(s_v10838);
  return call_ret_t184;
}

tll_ptr lam_fun_t191(tll_ptr __v10840, tll_env env) {
  tll_ptr ch_v10845; tll_ptr ch_v10846; tll_ptr ch_v10847; tll_ptr ch_v10848;
  tll_ptr prim_ch_t187; tll_ptr send_ch_t188; tll_ptr send_ch_t189;
  tll_ptr send_ch_t190;
  instr_open(&prim_ch_t187, &proc_stderr);
  ch_v10845 = prim_ch_t187;
  instr_send(&send_ch_t188, ch_v10845, (tll_ptr)1);
  ch_v10846 = send_ch_t188;
  instr_send(&send_ch_t189, ch_v10846, env[0]);
  ch_v10847 = send_ch_t189;
  instr_send(&send_ch_t190, ch_v10847, (tll_ptr)0);
  ch_v10848 = send_ch_t190;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v10839) {
  tll_ptr lam_clo_t192;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 1, s_v10839);
  return lam_clo_t192;
}

tll_ptr lam_fun_t194(tll_ptr s_v10849, tll_env env) {
  tll_ptr call_ret_t193;
  call_ret_t193 = prerr_i27(s_v10849);
  return call_ret_t193;
}

tll_ptr get_at_i29(tll_ptr A_v10850, tll_ptr n_v10851, tll_ptr xs_v10852, tll_ptr a_v10853) {
  tll_ptr __v10854; tll_ptr __v10857; tll_ptr add_ret_t239;
  tll_ptr call_ret_t238; tll_ptr ifte_ret_t241; tll_ptr switch_ret_t237;
  tll_ptr switch_ret_t240; tll_ptr x_v10856; tll_ptr xs_v10855;
  if (n_v10851) {
    switch(((tll_node)xs_v10852)->tag) {
      case 12:
        switch_ret_t237 = a_v10853;
        break;
      case 13:
        __v10854 = ((tll_node)xs_v10852)->data[0];
        xs_v10855 = ((tll_node)xs_v10852)->data[1];
        add_ret_t239 = n_v10851 - 1;
        call_ret_t238 = get_at_i29(0, add_ret_t239, xs_v10855, a_v10853);
        switch_ret_t237 = call_ret_t238;
        break;
    }
    ifte_ret_t241 = switch_ret_t237;
  }
  else {
    switch(((tll_node)xs_v10852)->tag) {
      case 12:
        switch_ret_t240 = a_v10853;
        break;
      case 13:
        x_v10856 = ((tll_node)xs_v10852)->data[0];
        __v10857 = ((tll_node)xs_v10852)->data[1];
        switch_ret_t240 = x_v10856;
        break;
    }
    ifte_ret_t241 = switch_ret_t240;
  }
  return ifte_ret_t241;
}

tll_ptr lam_fun_t243(tll_ptr a_v10867, tll_env env) {
  tll_ptr call_ret_t242;
  call_ret_t242 = get_at_i29(env[2], env[1], env[0], a_v10867);
  return call_ret_t242;
}

tll_ptr lam_fun_t245(tll_ptr xs_v10865, tll_env env) {
  tll_ptr lam_clo_t244;
  instr_clo(&lam_clo_t244, &lam_fun_t243, 3, xs_v10865, env[0], env[1]);
  return lam_clo_t244;
}

tll_ptr lam_fun_t247(tll_ptr n_v10862, tll_env env) {
  tll_ptr lam_clo_t246;
  instr_clo(&lam_clo_t246, &lam_fun_t245, 2, n_v10862, env[0]);
  return lam_clo_t246;
}

tll_ptr lam_fun_t249(tll_ptr A_v10858, tll_env env) {
  tll_ptr lam_clo_t248;
  instr_clo(&lam_clo_t248, &lam_fun_t247, 1, A_v10858);
  return lam_clo_t248;
}

tll_ptr string_of_digit_i30(tll_ptr n_v10868) {
  tll_ptr EmptyString_t252; tll_ptr call_ret_t251;
  instr_struct(&EmptyString_t252, 2, 0);
  call_ret_t251 = get_at_i29(0, n_v10868, digits_i28, EmptyString_t252);
  return call_ret_t251;
}

tll_ptr lam_fun_t254(tll_ptr n_v10869, tll_env env) {
  tll_ptr call_ret_t253;
  call_ret_t253 = string_of_digit_i30(n_v10869);
  return call_ret_t253;
}

tll_ptr string_of_nat_i31(tll_ptr n_v10870) {
  tll_ptr call_ret_t256; tll_ptr call_ret_t257; tll_ptr call_ret_t258;
  tll_ptr call_ret_t259; tll_ptr call_ret_t260; tll_ptr call_ret_t261;
  tll_ptr ifte_ret_t262; tll_ptr n_v10872; tll_ptr s_v10871;
  call_ret_t257 = modn_i14(n_v10870, (tll_ptr)10);
  call_ret_t256 = string_of_digit_i30(call_ret_t257);
  s_v10871 = call_ret_t256;
  call_ret_t258 = divn_i13(n_v10870, (tll_ptr)10);
  n_v10872 = call_ret_t258;
  call_ret_t259 = ltn_i6((tll_ptr)0, n_v10872);
  if (call_ret_t259) {
    call_ret_t261 = string_of_nat_i31(n_v10872);
    call_ret_t260 = cats_i15(call_ret_t261, s_v10871);
    ifte_ret_t262 = call_ret_t260;
  }
  else {
    ifte_ret_t262 = s_v10871;
  }
  return ifte_ret_t262;
}

tll_ptr lam_fun_t264(tll_ptr n_v10873, tll_env env) {
  tll_ptr call_ret_t263;
  call_ret_t263 = string_of_nat_i31(n_v10873);
  return call_ret_t263;
}

tll_ptr pow_i32(tll_ptr n_v10874, tll_ptr m_v10875) {
  tll_ptr add_ret_t268; tll_ptr call_ret_t266; tll_ptr call_ret_t267;
  tll_ptr ifte_ret_t269;
  if (m_v10875) {
    add_ret_t268 = m_v10875 - 1;
    call_ret_t267 = pow_i32(n_v10874, add_ret_t268);
    call_ret_t266 = muln_i12(n_v10874, call_ret_t267);
    ifte_ret_t269 = call_ret_t266;
  }
  else {
    ifte_ret_t269 = (tll_ptr)1;
  }
  return ifte_ret_t269;
}

tll_ptr lam_fun_t271(tll_ptr m_v10878, tll_env env) {
  tll_ptr call_ret_t270;
  call_ret_t270 = pow_i32(env[0], m_v10878);
  return call_ret_t270;
}

tll_ptr lam_fun_t273(tll_ptr n_v10876, tll_env env) {
  tll_ptr lam_clo_t272;
  instr_clo(&lam_clo_t272, &lam_fun_t271, 1, n_v10876);
  return lam_clo_t272;
}

tll_ptr lam_fun_t293(tll_ptr __v10883, tll_env env) {
  tll_ptr B_v10899; tll_ptr Char_t289; tll_ptr EmptyString_t290;
  tll_ptr String_t291; tll_ptr __v10898; tll_ptr app_ret_t292;
  tll_ptr b_v10896; tll_ptr call_ret_t275; tll_ptr call_ret_t276;
  tll_ptr call_ret_t284; tll_ptr call_ret_t285; tll_ptr call_ret_t286;
  tll_ptr call_ret_t287; tll_ptr call_ret_t288; tll_ptr ch_v10894;
  tll_ptr ch_v10897; tll_ptr ch_v10900; tll_ptr ch_v10902;
  tll_ptr pair_struct_t278; tll_ptr pair_struct_t282; tll_ptr pf_v10901;
  tll_ptr recv_msg_t280; tll_ptr s_v10903; tll_ptr send_ch_t277;
  tll_ptr switch_ret_t279; tll_ptr switch_ret_t281; tll_ptr switch_ret_t283;
  tll_ptr x_v10895;
  call_ret_t276 = pow_i32(env[1], env[3]);
  call_ret_t275 = modn_i14(call_ret_t276, env[2]);
  x_v10895 = call_ret_t275;
  instr_send(&send_ch_t277, env[0], x_v10895);
  ch_v10894 = send_ch_t277;
  instr_struct(&pair_struct_t278, 0, 2, 0, ch_v10894);
  switch(((tll_node)pair_struct_t278)->tag) {
    case 0:
      b_v10896 = ((tll_node)pair_struct_t278)->data[0];
      ch_v10897 = ((tll_node)pair_struct_t278)->data[1];
      instr_free_struct(pair_struct_t278);
      instr_recv(&recv_msg_t280, ch_v10897);
      __v10898 = recv_msg_t280;
      switch(((tll_node)__v10898)->tag) {
        case 0:
          B_v10899 = ((tll_node)__v10898)->data[0];
          ch_v10900 = ((tll_node)__v10898)->data[1];
          instr_free_struct(__v10898);
          instr_struct(&pair_struct_t282, 0, 2, 0, ch_v10900);
          switch(((tll_node)pair_struct_t282)->tag) {
            case 0:
              pf_v10901 = ((tll_node)pair_struct_t282)->data[0];
              ch_v10902 = ((tll_node)pair_struct_t282)->data[1];
              instr_free_struct(pair_struct_t282);
              call_ret_t285 = pow_i32(B_v10899, env[3]);
              call_ret_t284 = modn_i14(call_ret_t285, env[2]);
              s_v10903 = call_ret_t284;
              call_ret_t288 = string_of_nat_i31(s_v10903);
              instr_struct(&Char_t289, 1, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t290, 2, 0);
              instr_struct(&String_t291, 3, 2, Char_t289, EmptyString_t290);
              call_ret_t287 = cats_i15(call_ret_t288, String_t291);
              call_ret_t286 = print_i26(call_ret_t287);
              instr_app(&app_ret_t292, call_ret_t286, 0);
              instr_free_clo(call_ret_t286);
              switch_ret_t283 = app_ret_t292;
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

tll_ptr alice_i36(tll_ptr a_v10879, tll_ptr p_v10880, tll_ptr g_v10881, tll_ptr ch_v10882) {
  tll_ptr lam_clo_t294;
  instr_clo(&lam_clo_t294, &lam_fun_t293, 4,
            ch_v10882, g_v10881, p_v10880, a_v10879);
  return lam_clo_t294;
}

tll_ptr lam_fun_t296(tll_ptr ch_v10913, tll_env env) {
  tll_ptr call_ret_t295;
  call_ret_t295 = alice_i36(env[2], env[1], env[0], ch_v10913);
  return call_ret_t295;
}

tll_ptr lam_fun_t298(tll_ptr g_v10911, tll_env env) {
  tll_ptr lam_clo_t297;
  instr_clo(&lam_clo_t297, &lam_fun_t296, 3, g_v10911, env[0], env[1]);
  return lam_clo_t297;
}

tll_ptr lam_fun_t300(tll_ptr p_v10908, tll_env env) {
  tll_ptr lam_clo_t299;
  instr_clo(&lam_clo_t299, &lam_fun_t298, 2, p_v10908, env[0]);
  return lam_clo_t299;
}

tll_ptr lam_fun_t302(tll_ptr a_v10904, tll_env env) {
  tll_ptr lam_clo_t301;
  instr_clo(&lam_clo_t301, &lam_fun_t300, 1, a_v10904);
  return lam_clo_t301;
}

tll_ptr lam_fun_t323(tll_ptr __v10918, tll_env env) {
  tll_ptr A_v10933; tll_ptr Char_t319; tll_ptr EmptyString_t320;
  tll_ptr String_t321; tll_ptr __v10932; tll_ptr __v10940; tll_ptr a_v10930;
  tll_ptr app_ret_t322; tll_ptr call_ret_t310; tll_ptr call_ret_t311;
  tll_ptr call_ret_t313; tll_ptr call_ret_t314; tll_ptr call_ret_t316;
  tll_ptr call_ret_t317; tll_ptr call_ret_t318; tll_ptr ch_v10931;
  tll_ptr ch_v10934; tll_ptr ch_v10936; tll_ptr ch_v10937;
  tll_ptr close_tmp_t315; tll_ptr pair_struct_t304; tll_ptr pair_struct_t308;
  tll_ptr pf_v10935; tll_ptr recv_msg_t306; tll_ptr s_v10939;
  tll_ptr send_ch_t312; tll_ptr switch_ret_t305; tll_ptr switch_ret_t307;
  tll_ptr switch_ret_t309; tll_ptr x_v10938;
  instr_struct(&pair_struct_t304, 0, 2, 0, env[0]);
  switch(((tll_node)pair_struct_t304)->tag) {
    case 0:
      a_v10930 = ((tll_node)pair_struct_t304)->data[0];
      ch_v10931 = ((tll_node)pair_struct_t304)->data[1];
      instr_free_struct(pair_struct_t304);
      instr_recv(&recv_msg_t306, ch_v10931);
      __v10932 = recv_msg_t306;
      switch(((tll_node)__v10932)->tag) {
        case 0:
          A_v10933 = ((tll_node)__v10932)->data[0];
          ch_v10934 = ((tll_node)__v10932)->data[1];
          instr_free_struct(__v10932);
          instr_struct(&pair_struct_t308, 0, 2, 0, ch_v10934);
          switch(((tll_node)pair_struct_t308)->tag) {
            case 0:
              pf_v10935 = ((tll_node)pair_struct_t308)->data[0];
              ch_v10936 = ((tll_node)pair_struct_t308)->data[1];
              instr_free_struct(pair_struct_t308);
              call_ret_t311 = pow_i32(env[1], env[3]);
              call_ret_t310 = modn_i14(call_ret_t311, env[2]);
              x_v10938 = call_ret_t310;
              instr_send(&send_ch_t312, ch_v10936, x_v10938);
              ch_v10937 = send_ch_t312;
              call_ret_t314 = pow_i32(A_v10933, env[3]);
              call_ret_t313 = modn_i14(call_ret_t314, env[2]);
              s_v10939 = call_ret_t313;
              instr_close(&close_tmp_t315, ch_v10937);
              __v10940 = close_tmp_t315;
              call_ret_t318 = string_of_nat_i31(s_v10939);
              instr_struct(&Char_t319, 1, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t320, 2, 0);
              instr_struct(&String_t321, 3, 2, Char_t319, EmptyString_t320);
              call_ret_t317 = cats_i15(call_ret_t318, String_t321);
              call_ret_t316 = print_i26(call_ret_t317);
              instr_app(&app_ret_t322, call_ret_t316, 0);
              instr_free_clo(call_ret_t316);
              switch_ret_t309 = app_ret_t322;
              break;
          }
          switch_ret_t307 = switch_ret_t309;
          break;
      }
      switch_ret_t305 = switch_ret_t307;
      break;
  }
  return switch_ret_t305;
}

tll_ptr bob_i37(tll_ptr b_v10914, tll_ptr p_v10915, tll_ptr g_v10916, tll_ptr ch_v10917) {
  tll_ptr lam_clo_t324;
  instr_clo(&lam_clo_t324, &lam_fun_t323, 4,
            ch_v10917, g_v10916, p_v10915, b_v10914);
  return lam_clo_t324;
}

tll_ptr lam_fun_t326(tll_ptr ch_v10950, tll_env env) {
  tll_ptr call_ret_t325;
  call_ret_t325 = bob_i37(env[2], env[1], env[0], ch_v10950);
  return call_ret_t325;
}

tll_ptr lam_fun_t328(tll_ptr g_v10948, tll_env env) {
  tll_ptr lam_clo_t327;
  instr_clo(&lam_clo_t327, &lam_fun_t326, 3, g_v10948, env[0], env[1]);
  return lam_clo_t327;
}

tll_ptr lam_fun_t330(tll_ptr p_v10945, tll_env env) {
  tll_ptr lam_clo_t329;
  instr_clo(&lam_clo_t329, &lam_fun_t328, 2, p_v10945, env[0]);
  return lam_clo_t329;
}

tll_ptr lam_fun_t332(tll_ptr b_v10941, tll_env env) {
  tll_ptr lam_clo_t331;
  instr_clo(&lam_clo_t331, &lam_fun_t330, 1, b_v10941);
  return lam_clo_t331;
}

tll_ptr fork_fun_t336(tll_env env) {
  tll_ptr app_ret_t335; tll_ptr call_ret_t334; tll_ptr fork_ret_t338;
  call_ret_t334 = alice_i36((tll_ptr)4, (tll_ptr)23, (tll_ptr)5, env[0]);
  instr_app(&app_ret_t335, call_ret_t334, 0);
  instr_free_clo(call_ret_t334);
  fork_ret_t338 = app_ret_t335;
  instr_free_thread(env);
  return fork_ret_t338;
}

tll_ptr fork_fun_t343(tll_env env) {
  tll_ptr __v10968; tll_ptr app_ret_t342; tll_ptr c0_v10970;
  tll_ptr c_v10969; tll_ptr call_ret_t341; tll_ptr fork_ret_t345;
  tll_ptr recv_msg_t339; tll_ptr switch_ret_t340;
  instr_recv(&recv_msg_t339, env[0]);
  __v10968 = recv_msg_t339;
  switch(((tll_node)__v10968)->tag) {
    case 0:
      c_v10969 = ((tll_node)__v10968)->data[0];
      c0_v10970 = ((tll_node)__v10968)->data[1];
      instr_free_struct(__v10968);
      call_ret_t341 = bob_i37((tll_ptr)3, (tll_ptr)23, (tll_ptr)5, c_v10969);
      instr_app(&app_ret_t342, call_ret_t341, 0);
      instr_free_clo(call_ret_t341);
      switch_ret_t340 = app_ret_t342;
      break;
  }
  fork_ret_t345 = switch_ret_t340;
  instr_free_thread(env);
  return fork_ret_t345;
}

tll_ptr lam_fun_t348(tll_ptr __v10952, tll_env env) {
  tll_ptr c0_v10963; tll_ptr c0_v10971; tll_ptr c_v10961;
  tll_ptr close_tmp_t347; tll_ptr fork_ch_t337; tll_ptr fork_ch_t344;
  tll_ptr send_ch_t346;
  instr_fork(&fork_ch_t337, &fork_fun_t336, 0);
  c_v10961 = fork_ch_t337;
  instr_fork(&fork_ch_t344, &fork_fun_t343, 0);
  c0_v10963 = fork_ch_t344;
  instr_send(&send_ch_t346, c0_v10963, c_v10961);
  c0_v10971 = send_ch_t346;
  instr_close(&close_tmp_t347, c0_v10971);
  return close_tmp_t347;
}

tll_ptr key_exchange_i38(tll_ptr __v10951) {
  tll_ptr lam_clo_t349;
  instr_clo(&lam_clo_t349, &lam_fun_t348, 0);
  return lam_clo_t349;
}

tll_ptr lam_fun_t351(tll_ptr __v10972, tll_env env) {
  tll_ptr call_ret_t350;
  call_ret_t350 = key_exchange_i38(__v10972);
  return call_ret_t350;
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
  tll_ptr String_t222; tll_ptr String_t225; tll_ptr __v10973;
  tll_ptr app_ret_t354; tll_ptr call_ret_t353; tll_ptr consUU_t227;
  tll_ptr consUU_t228; tll_ptr consUU_t229; tll_ptr consUU_t230;
  tll_ptr consUU_t231; tll_ptr consUU_t232; tll_ptr consUU_t233;
  tll_ptr consUU_t234; tll_ptr consUU_t235; tll_ptr consUU_t236;
  tll_ptr lam_clo_t111; tll_ptr lam_clo_t12; tll_ptr lam_clo_t124;
  tll_ptr lam_clo_t137; tll_ptr lam_clo_t147; tll_ptr lam_clo_t157;
  tll_ptr lam_clo_t16; tll_ptr lam_clo_t167; tll_ptr lam_clo_t177;
  tll_ptr lam_clo_t186; tll_ptr lam_clo_t195; tll_ptr lam_clo_t22;
  tll_ptr lam_clo_t250; tll_ptr lam_clo_t255; tll_ptr lam_clo_t265;
  tll_ptr lam_clo_t274; tll_ptr lam_clo_t28; tll_ptr lam_clo_t303;
  tll_ptr lam_clo_t333; tll_ptr lam_clo_t34; tll_ptr lam_clo_t352;
  tll_ptr lam_clo_t40; tll_ptr lam_clo_t46; tll_ptr lam_clo_t51;
  tll_ptr lam_clo_t57; tll_ptr lam_clo_t6; tll_ptr lam_clo_t66;
  tll_ptr lam_clo_t72; tll_ptr lam_clo_t78; tll_ptr lam_clo_t84;
  tll_ptr lam_clo_t92; tll_ptr lam_clo_t98; tll_ptr nilUU_t226;
  tll_ptr sleep_tmp_t355;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i48 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i49 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i50 = lam_clo_t16;
  instr_clo(&lam_clo_t22, &lam_fun_t21, 0);
  ltenclo_i51 = lam_clo_t22;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  gtenclo_i52 = lam_clo_t28;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 0);
  ltnclo_i53 = lam_clo_t34;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 0);
  gtnclo_i54 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  eqnclo_i55 = lam_clo_t46;
  instr_clo(&lam_clo_t51, &lam_fun_t50, 0);
  predclo_i56 = lam_clo_t51;
  instr_clo(&lam_clo_t57, &lam_fun_t56, 0);
  addnclo_i57 = lam_clo_t57;
  instr_clo(&lam_clo_t66, &lam_fun_t65, 0);
  subnclo_i58 = lam_clo_t66;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  mulnclo_i59 = lam_clo_t72;
  instr_clo(&lam_clo_t78, &lam_fun_t77, 0);
  divnclo_i60 = lam_clo_t78;
  instr_clo(&lam_clo_t84, &lam_fun_t83, 0);
  modnclo_i61 = lam_clo_t84;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  catsclo_i62 = lam_clo_t92;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  strlenclo_i63 = lam_clo_t98;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 0);
  lenUUclo_i64 = lam_clo_t111;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 0);
  lenULclo_i65 = lam_clo_t124;
  instr_clo(&lam_clo_t137, &lam_fun_t136, 0);
  lenLLclo_i66 = lam_clo_t137;
  instr_clo(&lam_clo_t147, &lam_fun_t146, 0);
  appendUUclo_i67 = lam_clo_t147;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 0);
  appendULclo_i68 = lam_clo_t157;
  instr_clo(&lam_clo_t167, &lam_fun_t166, 0);
  appendLLclo_i69 = lam_clo_t167;
  instr_clo(&lam_clo_t177, &lam_fun_t176, 0);
  readlineclo_i70 = lam_clo_t177;
  instr_clo(&lam_clo_t186, &lam_fun_t185, 0);
  printclo_i71 = lam_clo_t186;
  instr_clo(&lam_clo_t195, &lam_fun_t194, 0);
  prerrclo_i72 = lam_clo_t195;
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
  get_atclo_i73 = lam_clo_t250;
  instr_clo(&lam_clo_t255, &lam_fun_t254, 0);
  string_of_digitclo_i74 = lam_clo_t255;
  instr_clo(&lam_clo_t265, &lam_fun_t264, 0);
  string_of_natclo_i75 = lam_clo_t265;
  instr_clo(&lam_clo_t274, &lam_fun_t273, 0);
  powclo_i76 = lam_clo_t274;
  instr_clo(&lam_clo_t303, &lam_fun_t302, 0);
  aliceclo_i77 = lam_clo_t303;
  instr_clo(&lam_clo_t333, &lam_fun_t332, 0);
  bobclo_i78 = lam_clo_t333;
  instr_clo(&lam_clo_t352, &lam_fun_t351, 0);
  key_exchangeclo_i79 = lam_clo_t352;
  call_ret_t353 = key_exchange_i38(0);
  instr_app(&app_ret_t354, call_ret_t353, 0);
  instr_free_clo(call_ret_t353);
  __v10973 = app_ret_t354;
  instr_sleep(&sleep_tmp_t355, (tll_ptr)1);
  return 0;
}

