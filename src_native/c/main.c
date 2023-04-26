#include "runtime.h"
#include <unistd.h> // notice this! you need it!

tll_ptr andb_i1(tll_ptr b1_v10560, tll_ptr b2_v10561);
tll_ptr orb_i2(tll_ptr b1_v10565, tll_ptr b2_v10566);
tll_ptr notb_i3(tll_ptr b_v10570);
tll_ptr lten_i4(tll_ptr x_v10572, tll_ptr y_v10573);
tll_ptr gten_i5(tll_ptr x_v10577, tll_ptr y_v10578);
tll_ptr ltn_i6(tll_ptr x_v10582, tll_ptr y_v10583);
tll_ptr gtn_i7(tll_ptr x_v10587, tll_ptr y_v10588);
tll_ptr eqn_i8(tll_ptr x_v10592, tll_ptr y_v10593);
tll_ptr pred_i9(tll_ptr x_v10597);
tll_ptr addn_i10(tll_ptr x_v10599, tll_ptr y_v10600);
tll_ptr subn_i11(tll_ptr x_v10604, tll_ptr y_v10605);
tll_ptr muln_i12(tll_ptr x_v10609, tll_ptr y_v10610);
tll_ptr divn_i13(tll_ptr x_v10614, tll_ptr y_v10615);
tll_ptr modn_i14(tll_ptr x_v10619, tll_ptr y_v10620);
tll_ptr cats_i15(tll_ptr s1_v10624, tll_ptr s2_v10625);
tll_ptr strlen_i16(tll_ptr s_v10631);
tll_ptr lenUU_i43(tll_ptr A_v10635, tll_ptr xs_v10636);
tll_ptr lenUL_i42(tll_ptr A_v10644, tll_ptr xs_v10645);
tll_ptr lenLL_i40(tll_ptr A_v10653, tll_ptr xs_v10654);
tll_ptr appendUU_i47(tll_ptr A_v10662, tll_ptr xs_v10663, tll_ptr ys_v10664);
tll_ptr appendUL_i46(tll_ptr A_v10673, tll_ptr xs_v10674, tll_ptr ys_v10675);
tll_ptr appendLL_i44(tll_ptr A_v10684, tll_ptr xs_v10685, tll_ptr ys_v10686);
tll_ptr readline_i25(tll_ptr __v10695);
tll_ptr print_i26(tll_ptr s_v10710);
tll_ptr prerr_i27(tll_ptr s_v10721);
tll_ptr get_at_i29(tll_ptr A_v10732, tll_ptr n_v10733, tll_ptr xs_v10734,
                   tll_ptr a_v10735);
tll_ptr string_of_digit_i30(tll_ptr n_v10750);
tll_ptr string_of_nat_i31(tll_ptr n_v10752);
tll_ptr pow_i32(tll_ptr n_v10754, tll_ptr m_v10755);
tll_ptr alice_i36(tll_ptr a_v10759, tll_ptr p_v10760, tll_ptr g_v10761,
                  tll_ptr ch_v10762);
tll_ptr bob_i37(tll_ptr b_v10790, tll_ptr p_v10791, tll_ptr g_v10792,
                tll_ptr ch_v10793);
tll_ptr key_exchange_i38(tll_ptr __v10823);

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

tll_ptr andb_i1(tll_ptr b1_v10560, tll_ptr b2_v10561) {
  tll_ptr ifte_ret_t1;
  if (b1_v10560) {
    ifte_ret_t1 = b2_v10561;
  } else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v10564, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v10564);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v10562, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v10562);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v10565, tll_ptr b2_v10566) {
  tll_ptr ifte_ret_t7;
  if (b1_v10565) {
    ifte_ret_t7 = (tll_ptr)1;
  } else {
    ifte_ret_t7 = b2_v10566;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v10569, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v10569);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v10567, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v10567);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v10570) {
  tll_ptr ifte_ret_t13;
  if (b_v10570) {
    ifte_ret_t13 = (tll_ptr)0;
  } else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v10571, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v10571);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v10572, tll_ptr y_v10573) {
  tll_ptr add_ret_t18;
  tll_ptr add_ret_t19;
  tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20;
  tll_ptr ifte_ret_t21;
  if (x_v10572) {
    if (y_v10573) {
      add_ret_t18 = x_v10572 - 1;
      add_ret_t19 = y_v10573 - 1;
      call_ret_t17 = lten_i4(add_ret_t18, add_ret_t19);
      ifte_ret_t20 = call_ret_t17;
    } else {
      ifte_ret_t20 = (tll_ptr)0;
    }
    ifte_ret_t21 = ifte_ret_t20;
  } else {
    ifte_ret_t21 = (tll_ptr)1;
  }
  return ifte_ret_t21;
}

tll_ptr lam_fun_t23(tll_ptr y_v10576, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v10576);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v10574, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v10574);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v10577, tll_ptr y_v10578) {
  tll_ptr add_ret_t28;
  tll_ptr add_ret_t29;
  tll_ptr call_ret_t27;
  tll_ptr ifte_ret_t30;
  tll_ptr ifte_ret_t31;
  tll_ptr ifte_ret_t32;
  if (x_v10577) {
    if (y_v10578) {
      add_ret_t28 = x_v10577 - 1;
      add_ret_t29 = y_v10578 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    } else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  } else {
    if (y_v10578) {
      ifte_ret_t31 = (tll_ptr)0;
    } else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v10581, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v10581);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v10579, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v10579);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v10582, tll_ptr y_v10583) {
  tll_ptr add_ret_t39;
  tll_ptr add_ret_t40;
  tll_ptr call_ret_t38;
  tll_ptr ifte_ret_t41;
  tll_ptr ifte_ret_t42;
  tll_ptr ifte_ret_t43;
  if (x_v10582) {
    if (y_v10583) {
      add_ret_t39 = x_v10582 - 1;
      add_ret_t40 = y_v10583 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    } else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  } else {
    if (y_v10583) {
      ifte_ret_t42 = (tll_ptr)1;
    } else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v10586, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v10586);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v10584, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v10584);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v10587, tll_ptr y_v10588) {
  tll_ptr add_ret_t50;
  tll_ptr add_ret_t51;
  tll_ptr call_ret_t49;
  tll_ptr ifte_ret_t52;
  tll_ptr ifte_ret_t53;
  if (x_v10587) {
    if (y_v10588) {
      add_ret_t50 = x_v10587 - 1;
      add_ret_t51 = y_v10588 - 1;
      call_ret_t49 = gtn_i7(add_ret_t50, add_ret_t51);
      ifte_ret_t52 = call_ret_t49;
    } else {
      ifte_ret_t52 = (tll_ptr)1;
    }
    ifte_ret_t53 = ifte_ret_t52;
  } else {
    ifte_ret_t53 = (tll_ptr)0;
  }
  return ifte_ret_t53;
}

tll_ptr lam_fun_t55(tll_ptr y_v10591, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v10591);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v10589, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v10589);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v10592, tll_ptr y_v10593) {
  tll_ptr add_ret_t60;
  tll_ptr add_ret_t61;
  tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t62;
  tll_ptr ifte_ret_t63;
  tll_ptr ifte_ret_t64;
  if (x_v10592) {
    if (y_v10593) {
      add_ret_t60 = x_v10592 - 1;
      add_ret_t61 = y_v10593 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    } else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  } else {
    if (y_v10593) {
      ifte_ret_t63 = (tll_ptr)0;
    } else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v10596, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v10596);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v10594, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v10594);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v10597) {
  tll_ptr add_ret_t70;
  tll_ptr ifte_ret_t71;
  if (x_v10597) {
    add_ret_t70 = x_v10597 - 1;
    ifte_ret_t71 = add_ret_t70;
  } else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v10598, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v10598);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v10599, tll_ptr y_v10600) {
  tll_ptr add_ret_t76;
  tll_ptr add_ret_t77;
  tll_ptr call_ret_t75;
  tll_ptr ifte_ret_t78;
  if (x_v10599) {
    add_ret_t76 = x_v10599 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v10600);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  } else {
    ifte_ret_t78 = y_v10600;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v10603, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v10603);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v10601, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v10601);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v10604, tll_ptr y_v10605) {
  tll_ptr add_ret_t86;
  tll_ptr call_ret_t84;
  tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v10605) {
    call_ret_t85 = pred_i9(x_v10604);
    add_ret_t86 = y_v10605 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  } else {
    ifte_ret_t87 = x_v10604;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v10608, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v10608);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v10606, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v10606);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v10609, tll_ptr y_v10610) {
  tll_ptr add_ret_t95;
  tll_ptr call_ret_t93;
  tll_ptr call_ret_t94;
  tll_ptr ifte_ret_t96;
  if (x_v10609) {
    add_ret_t95 = x_v10609 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v10610);
    call_ret_t93 = addn_i10(y_v10610, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  } else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v10613, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v10613);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v10611, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v10611);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v10614, tll_ptr y_v10615) {
  tll_ptr add_ret_t105;
  tll_ptr call_ret_t102;
  tll_ptr call_ret_t103;
  tll_ptr call_ret_t104;
  tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v10614, y_v10615);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  } else {
    call_ret_t104 = subn_i11(x_v10614, y_v10615);
    call_ret_t103 = divn_i13(call_ret_t104, y_v10615);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v10618, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v10618);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v10616, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v10616);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v10619, tll_ptr y_v10620) {
  tll_ptr call_ret_t112;
  tll_ptr call_ret_t113;
  tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v10619, y_v10620);
  call_ret_t113 = muln_i12(call_ret_t114, y_v10620);
  call_ret_t112 = subn_i11(x_v10619, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v10623, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v10623);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v10621, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v10621);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v10624, tll_ptr s2_v10625) {
  tll_ptr String_t122;
  tll_ptr c_v10626;
  tll_ptr call_ret_t121;
  tll_ptr s1_v10627;
  tll_ptr switch_ret_t120;
  switch (((tll_node)s1_v10624)->tag) {
  case 2:
    switch_ret_t120 = s2_v10625;
    break;
  case 3:
    c_v10626 = ((tll_node)s1_v10624)->data[0];
    s1_v10627 = ((tll_node)s1_v10624)->data[1];
    call_ret_t121 = cats_i15(s1_v10627, s2_v10625);
    instr_struct(&String_t122, 3, 2, c_v10626, call_ret_t121);
    switch_ret_t120 = String_t122;
    break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v10630, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v10630);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v10628, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v10628);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v10631) {
  tll_ptr __v10632;
  tll_ptr add_ret_t130;
  tll_ptr call_ret_t129;
  tll_ptr s_v10633;
  tll_ptr switch_ret_t128;
  switch (((tll_node)s_v10631)->tag) {
  case 2:
    switch_ret_t128 = (tll_ptr)0;
    break;
  case 3:
    __v10632 = ((tll_node)s_v10631)->data[0];
    s_v10633 = ((tll_node)s_v10631)->data[1];
    call_ret_t129 = strlen_i16(s_v10633);
    add_ret_t130 = call_ret_t129 + 1;
    switch_ret_t128 = add_ret_t130;
    break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v10634, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v10634);
  return call_ret_t131;
}

tll_ptr lenUU_i43(tll_ptr A_v10635, tll_ptr xs_v10636) {
  tll_ptr add_ret_t139;
  tll_ptr call_ret_t137;
  tll_ptr consUU_t140;
  tll_ptr n_v10639;
  tll_ptr nilUU_t135;
  tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141;
  tll_ptr switch_ret_t134;
  tll_ptr switch_ret_t138;
  tll_ptr x_v10637;
  tll_ptr xs_v10638;
  tll_ptr xs_v10640;
  switch (((tll_node)xs_v10636)->tag) {
  case 12:
    instr_struct(&nilUU_t135, 12, 0);
    instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
    switch_ret_t134 = pair_struct_t136;
    break;
  case 13:
    x_v10637 = ((tll_node)xs_v10636)->data[0];
    xs_v10638 = ((tll_node)xs_v10636)->data[1];
    call_ret_t137 = lenUU_i43(0, xs_v10638);
    switch (((tll_node)call_ret_t137)->tag) {
    case 0:
      n_v10639 = ((tll_node)call_ret_t137)->data[0];
      xs_v10640 = ((tll_node)call_ret_t137)->data[1];
      instr_free_struct(call_ret_t137);
      add_ret_t139 = n_v10639 + 1;
      instr_struct(&consUU_t140, 13, 2, x_v10637, xs_v10640);
      instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
      switch_ret_t138 = pair_struct_t141;
      break;
    }
    switch_ret_t134 = switch_ret_t138;
    break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v10643, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i43(env[0], xs_v10643);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v10641, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v10641);
  return lam_clo_t144;
}

tll_ptr lenUL_i42(tll_ptr A_v10644, tll_ptr xs_v10645) {
  tll_ptr add_ret_t152;
  tll_ptr call_ret_t150;
  tll_ptr consUL_t153;
  tll_ptr n_v10648;
  tll_ptr nilUL_t148;
  tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154;
  tll_ptr switch_ret_t147;
  tll_ptr switch_ret_t151;
  tll_ptr x_v10646;
  tll_ptr xs_v10647;
  tll_ptr xs_v10649;
  switch (((tll_node)xs_v10645)->tag) {
  case 10:
    instr_free_struct(xs_v10645);
    instr_struct(&nilUL_t148, 10, 0);
    instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
    switch_ret_t147 = pair_struct_t149;
    break;
  case 11:
    x_v10646 = ((tll_node)xs_v10645)->data[0];
    xs_v10647 = ((tll_node)xs_v10645)->data[1];
    instr_free_struct(xs_v10645);
    call_ret_t150 = lenUL_i42(0, xs_v10647);
    switch (((tll_node)call_ret_t150)->tag) {
    case 0:
      n_v10648 = ((tll_node)call_ret_t150)->data[0];
      xs_v10649 = ((tll_node)call_ret_t150)->data[1];
      instr_free_struct(call_ret_t150);
      add_ret_t152 = n_v10648 + 1;
      instr_struct(&consUL_t153, 11, 2, x_v10646, xs_v10649);
      instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
      switch_ret_t151 = pair_struct_t154;
      break;
    }
    switch_ret_t147 = switch_ret_t151;
    break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v10652, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i42(env[0], xs_v10652);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v10650, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v10650);
  return lam_clo_t157;
}

tll_ptr lenLL_i40(tll_ptr A_v10653, tll_ptr xs_v10654) {
  tll_ptr add_ret_t165;
  tll_ptr call_ret_t163;
  tll_ptr consLL_t166;
  tll_ptr n_v10657;
  tll_ptr nilLL_t161;
  tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167;
  tll_ptr switch_ret_t160;
  tll_ptr switch_ret_t164;
  tll_ptr x_v10655;
  tll_ptr xs_v10656;
  tll_ptr xs_v10658;
  switch (((tll_node)xs_v10654)->tag) {
  case 6:
    instr_free_struct(xs_v10654);
    instr_struct(&nilLL_t161, 6, 0);
    instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
    switch_ret_t160 = pair_struct_t162;
    break;
  case 7:
    x_v10655 = ((tll_node)xs_v10654)->data[0];
    xs_v10656 = ((tll_node)xs_v10654)->data[1];
    instr_free_struct(xs_v10654);
    call_ret_t163 = lenLL_i40(0, xs_v10656);
    switch (((tll_node)call_ret_t163)->tag) {
    case 0:
      n_v10657 = ((tll_node)call_ret_t163)->data[0];
      xs_v10658 = ((tll_node)call_ret_t163)->data[1];
      instr_free_struct(call_ret_t163);
      add_ret_t165 = n_v10657 + 1;
      instr_struct(&consLL_t166, 7, 2, x_v10655, xs_v10658);
      instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
      switch_ret_t164 = pair_struct_t167;
      break;
    }
    switch_ret_t160 = switch_ret_t164;
    break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v10661, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i40(env[0], xs_v10661);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v10659, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v10659);
  return lam_clo_t170;
}

tll_ptr appendUU_i47(tll_ptr A_v10662, tll_ptr xs_v10663, tll_ptr ys_v10664) {
  tll_ptr call_ret_t174;
  tll_ptr consUU_t175;
  tll_ptr switch_ret_t173;
  tll_ptr x_v10665;
  tll_ptr xs_v10666;
  switch (((tll_node)xs_v10663)->tag) {
  case 12:
    switch_ret_t173 = ys_v10664;
    break;
  case 13:
    x_v10665 = ((tll_node)xs_v10663)->data[0];
    xs_v10666 = ((tll_node)xs_v10663)->data[1];
    call_ret_t174 = appendUU_i47(0, xs_v10666, ys_v10664);
    instr_struct(&consUU_t175, 13, 2, x_v10665, call_ret_t174);
    switch_ret_t173 = consUU_t175;
    break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v10672, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i47(env[1], env[0], ys_v10672);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v10670, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v10670, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v10667, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v10667);
  return lam_clo_t180;
}

tll_ptr appendUL_i46(tll_ptr A_v10673, tll_ptr xs_v10674, tll_ptr ys_v10675) {
  tll_ptr call_ret_t184;
  tll_ptr consUL_t185;
  tll_ptr switch_ret_t183;
  tll_ptr x_v10676;
  tll_ptr xs_v10677;
  switch (((tll_node)xs_v10674)->tag) {
  case 10:
    instr_free_struct(xs_v10674);
    switch_ret_t183 = ys_v10675;
    break;
  case 11:
    x_v10676 = ((tll_node)xs_v10674)->data[0];
    xs_v10677 = ((tll_node)xs_v10674)->data[1];
    instr_free_struct(xs_v10674);
    call_ret_t184 = appendUL_i46(0, xs_v10677, ys_v10675);
    instr_struct(&consUL_t185, 11, 2, x_v10676, call_ret_t184);
    switch_ret_t183 = consUL_t185;
    break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v10683, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i46(env[1], env[0], ys_v10683);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v10681, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v10681, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v10678, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v10678);
  return lam_clo_t190;
}

tll_ptr appendLL_i44(tll_ptr A_v10684, tll_ptr xs_v10685, tll_ptr ys_v10686) {
  tll_ptr call_ret_t194;
  tll_ptr consLL_t195;
  tll_ptr switch_ret_t193;
  tll_ptr x_v10687;
  tll_ptr xs_v10688;
  switch (((tll_node)xs_v10685)->tag) {
  case 6:
    instr_free_struct(xs_v10685);
    switch_ret_t193 = ys_v10686;
    break;
  case 7:
    x_v10687 = ((tll_node)xs_v10685)->data[0];
    xs_v10688 = ((tll_node)xs_v10685)->data[1];
    instr_free_struct(xs_v10685);
    call_ret_t194 = appendLL_i44(0, xs_v10688, ys_v10686);
    instr_struct(&consLL_t195, 7, 2, x_v10687, call_ret_t194);
    switch_ret_t193 = consLL_t195;
    break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v10694, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i44(env[1], env[0], ys_v10694);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v10692, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v10692, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v10689, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v10689);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v10696, tll_env env) {
  tll_ptr __v10705;
  tll_ptr ch_v10703;
  tll_ptr ch_v10704;
  tll_ptr ch_v10707;
  tll_ptr ch_v10708;
  tll_ptr prim_ch_t203;
  tll_ptr recv_msg_t205;
  tll_ptr s_v10706;
  tll_ptr send_ch_t204;
  tll_ptr send_ch_t207;
  tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v10703 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v10703, (tll_ptr)1);
  ch_v10704 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v10704);
  __v10705 = recv_msg_t205;
  switch (((tll_node)__v10705)->tag) {
  case 0:
    s_v10706 = ((tll_node)__v10705)->data[0];
    ch_v10707 = ((tll_node)__v10705)->data[1];
    instr_free_struct(__v10705);
    instr_send(&send_ch_t207, ch_v10707, (tll_ptr)0);
    ch_v10708 = send_ch_t207;
    switch_ret_t206 = s_v10706;
    break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v10695) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v10709, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v10709);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v10711, tll_env env) {
  tll_ptr ch_v10716;
  tll_ptr ch_v10717;
  tll_ptr ch_v10718;
  tll_ptr ch_v10719;
  tll_ptr prim_ch_t213;
  tll_ptr send_ch_t214;
  tll_ptr send_ch_t215;
  tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v10716 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v10716, (tll_ptr)1);
  ch_v10717 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v10717, env[0]);
  ch_v10718 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v10718, (tll_ptr)0);
  ch_v10719 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v10710) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v10710);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v10720, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v10720);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v10722, tll_env env) {
  tll_ptr ch_v10727;
  tll_ptr ch_v10728;
  tll_ptr ch_v10729;
  tll_ptr ch_v10730;
  tll_ptr prim_ch_t222;
  tll_ptr send_ch_t223;
  tll_ptr send_ch_t224;
  tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v10727 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v10727, (tll_ptr)1);
  ch_v10728 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v10728, env[0]);
  ch_v10729 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v10729, (tll_ptr)0);
  ch_v10730 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v10721) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v10721);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v10731, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v10731);
  return call_ret_t228;
}

tll_ptr get_at_i29(tll_ptr A_v10732, tll_ptr n_v10733, tll_ptr xs_v10734,
                   tll_ptr a_v10735) {
  tll_ptr __v10736;
  tll_ptr __v10739;
  tll_ptr add_ret_t274;
  tll_ptr call_ret_t273;
  tll_ptr ifte_ret_t276;
  tll_ptr switch_ret_t272;
  tll_ptr switch_ret_t275;
  tll_ptr x_v10738;
  tll_ptr xs_v10737;
  if (n_v10733) {
    switch (((tll_node)xs_v10734)->tag) {
    case 12:
      switch_ret_t272 = a_v10735;
      break;
    case 13:
      __v10736 = ((tll_node)xs_v10734)->data[0];
      xs_v10737 = ((tll_node)xs_v10734)->data[1];
      add_ret_t274 = n_v10733 - 1;
      call_ret_t273 = get_at_i29(0, add_ret_t274, xs_v10737, a_v10735);
      switch_ret_t272 = call_ret_t273;
      break;
    }
    ifte_ret_t276 = switch_ret_t272;
  } else {
    switch (((tll_node)xs_v10734)->tag) {
    case 12:
      switch_ret_t275 = a_v10735;
      break;
    case 13:
      x_v10738 = ((tll_node)xs_v10734)->data[0];
      __v10739 = ((tll_node)xs_v10734)->data[1];
      switch_ret_t275 = x_v10738;
      break;
    }
    ifte_ret_t276 = switch_ret_t275;
  }
  return ifte_ret_t276;
}

tll_ptr lam_fun_t278(tll_ptr a_v10749, tll_env env) {
  tll_ptr call_ret_t277;
  call_ret_t277 = get_at_i29(env[2], env[1], env[0], a_v10749);
  return call_ret_t277;
}

tll_ptr lam_fun_t280(tll_ptr xs_v10747, tll_env env) {
  tll_ptr lam_clo_t279;
  instr_clo(&lam_clo_t279, &lam_fun_t278, 3, xs_v10747, env[0], env[1]);
  return lam_clo_t279;
}

tll_ptr lam_fun_t282(tll_ptr n_v10744, tll_env env) {
  tll_ptr lam_clo_t281;
  instr_clo(&lam_clo_t281, &lam_fun_t280, 2, n_v10744, env[0]);
  return lam_clo_t281;
}

tll_ptr lam_fun_t284(tll_ptr A_v10740, tll_env env) {
  tll_ptr lam_clo_t283;
  instr_clo(&lam_clo_t283, &lam_fun_t282, 1, A_v10740);
  return lam_clo_t283;
}

tll_ptr string_of_digit_i30(tll_ptr n_v10750) {
  tll_ptr EmptyString_t287;
  tll_ptr call_ret_t286;
  instr_struct(&EmptyString_t287, 2, 0);
  call_ret_t286 = get_at_i29(0, n_v10750, digits_i28, EmptyString_t287);
  return call_ret_t286;
}

tll_ptr lam_fun_t289(tll_ptr n_v10751, tll_env env) {
  tll_ptr call_ret_t288;
  call_ret_t288 = string_of_digit_i30(n_v10751);
  return call_ret_t288;
}

tll_ptr string_of_nat_i31(tll_ptr n_v10752) {
  tll_ptr call_ret_t291;
  tll_ptr call_ret_t292;
  tll_ptr call_ret_t293;
  tll_ptr call_ret_t294;
  tll_ptr call_ret_t295;
  tll_ptr call_ret_t296;
  tll_ptr call_ret_t297;
  tll_ptr call_ret_t298;
  tll_ptr call_ret_t299;
  tll_ptr ifte_ret_t300;
  call_ret_t292 = divn_i13(n_v10752, (tll_ptr)10);
  call_ret_t291 = ltn_i6((tll_ptr)0, call_ret_t292);
  if (call_ret_t291) {
    call_ret_t295 = divn_i13(n_v10752, (tll_ptr)10);
    call_ret_t294 = string_of_nat_i31(call_ret_t295);
    call_ret_t297 = modn_i14(n_v10752, (tll_ptr)10);
    call_ret_t296 = string_of_digit_i30(call_ret_t297);
    call_ret_t293 = cats_i15(call_ret_t294, call_ret_t296);
    ifte_ret_t300 = call_ret_t293;
  } else {
    call_ret_t299 = modn_i14(n_v10752, (tll_ptr)10);
    call_ret_t298 = string_of_digit_i30(call_ret_t299);
    ifte_ret_t300 = call_ret_t298;
  }
  return ifte_ret_t300;
}

tll_ptr lam_fun_t302(tll_ptr n_v10753, tll_env env) {
  tll_ptr call_ret_t301;
  call_ret_t301 = string_of_nat_i31(n_v10753);
  return call_ret_t301;
}

tll_ptr pow_i32(tll_ptr n_v10754, tll_ptr m_v10755) {
  tll_ptr add_ret_t306;
  tll_ptr call_ret_t304;
  tll_ptr call_ret_t305;
  tll_ptr ifte_ret_t307;
  if (m_v10755) {
    add_ret_t306 = m_v10755 - 1;
    call_ret_t305 = pow_i32(n_v10754, add_ret_t306);
    call_ret_t304 = muln_i12(n_v10754, call_ret_t305);
    ifte_ret_t307 = call_ret_t304;
  } else {
    ifte_ret_t307 = (tll_ptr)1;
  }
  return ifte_ret_t307;
}

tll_ptr lam_fun_t309(tll_ptr m_v10758, tll_env env) {
  tll_ptr call_ret_t308;
  call_ret_t308 = pow_i32(env[0], m_v10758);
  return call_ret_t308;
}

tll_ptr lam_fun_t311(tll_ptr n_v10756, tll_env env) {
  tll_ptr lam_clo_t310;
  instr_clo(&lam_clo_t310, &lam_fun_t309, 1, n_v10756);
  return lam_clo_t310;
}

tll_ptr lam_fun_t331(tll_ptr __v10763, tll_env env) {
  tll_ptr B_v10776;
  tll_ptr Char_t327;
  tll_ptr EmptyString_t328;
  tll_ptr String_t329;
  tll_ptr __v10775;
  tll_ptr app_ret_t330;
  tll_ptr b_v10773;
  tll_ptr call_ret_t314;
  tll_ptr call_ret_t315;
  tll_ptr call_ret_t322;
  tll_ptr call_ret_t323;
  tll_ptr call_ret_t324;
  tll_ptr call_ret_t325;
  tll_ptr call_ret_t326;
  tll_ptr ch_v10772;
  tll_ptr ch_v10774;
  tll_ptr ch_v10777;
  tll_ptr ch_v10779;
  tll_ptr pair_struct_t316;
  tll_ptr pair_struct_t320;
  tll_ptr pf_v10778;
  tll_ptr recv_msg_t318;
  tll_ptr send_ch_t313;
  tll_ptr switch_ret_t317;
  tll_ptr switch_ret_t319;
  tll_ptr switch_ret_t321;
  call_ret_t315 = pow_i32(env[1], env[3]);
  call_ret_t314 = modn_i14(call_ret_t315, env[2]);
  instr_send(&send_ch_t313, env[0], call_ret_t314);
  ch_v10772 = send_ch_t313;
  instr_struct(&pair_struct_t316, 0, 2, 0, ch_v10772);
  switch (((tll_node)pair_struct_t316)->tag) {
  case 0:
    b_v10773 = ((tll_node)pair_struct_t316)->data[0];
    ch_v10774 = ((tll_node)pair_struct_t316)->data[1];
    instr_free_struct(pair_struct_t316);
    instr_recv(&recv_msg_t318, ch_v10774);
    __v10775 = recv_msg_t318;
    switch (((tll_node)__v10775)->tag) {
    case 0:
      B_v10776 = ((tll_node)__v10775)->data[0];
      ch_v10777 = ((tll_node)__v10775)->data[1];
      instr_free_struct(__v10775);
      instr_struct(&pair_struct_t320, 0, 2, 0, ch_v10777);
      switch (((tll_node)pair_struct_t320)->tag) {
      case 0:
        pf_v10778 = ((tll_node)pair_struct_t320)->data[0];
        ch_v10779 = ((tll_node)pair_struct_t320)->data[1];
        instr_free_struct(pair_struct_t320);
        call_ret_t326 = pow_i32(B_v10776, env[3]);
        call_ret_t325 = modn_i14(call_ret_t326, env[2]);
        call_ret_t324 = string_of_nat_i31(call_ret_t325);
        instr_struct(&Char_t327, 1, 1, (tll_ptr)10);
        instr_struct(&EmptyString_t328, 2, 0);
        instr_struct(&String_t329, 3, 2, Char_t327, EmptyString_t328);
        call_ret_t323 = cats_i15(call_ret_t324, String_t329);
        call_ret_t322 = print_i26(call_ret_t323);
        instr_app(&app_ret_t330, call_ret_t322, 0);
        instr_free_clo(call_ret_t322);
        switch_ret_t321 = app_ret_t330;
        break;
      }
      switch_ret_t319 = switch_ret_t321;
      break;
    }
    switch_ret_t317 = switch_ret_t319;
    break;
  }
  return switch_ret_t317;
}

tll_ptr alice_i36(tll_ptr a_v10759, tll_ptr p_v10760, tll_ptr g_v10761,
                  tll_ptr ch_v10762) {
  tll_ptr lam_clo_t332;
  instr_clo(&lam_clo_t332, &lam_fun_t331, 4, ch_v10762, g_v10761, p_v10760,
            a_v10759);
  return lam_clo_t332;
}

tll_ptr lam_fun_t334(tll_ptr ch_v10789, tll_env env) {
  tll_ptr call_ret_t333;
  call_ret_t333 = alice_i36(env[2], env[1], env[0], ch_v10789);
  return call_ret_t333;
}

tll_ptr lam_fun_t336(tll_ptr g_v10787, tll_env env) {
  tll_ptr lam_clo_t335;
  instr_clo(&lam_clo_t335, &lam_fun_t334, 3, g_v10787, env[0], env[1]);
  return lam_clo_t335;
}

tll_ptr lam_fun_t338(tll_ptr p_v10784, tll_env env) {
  tll_ptr lam_clo_t337;
  instr_clo(&lam_clo_t337, &lam_fun_t336, 2, p_v10784, env[0]);
  return lam_clo_t337;
}

tll_ptr lam_fun_t340(tll_ptr a_v10780, tll_env env) {
  tll_ptr lam_clo_t339;
  instr_clo(&lam_clo_t339, &lam_fun_t338, 1, a_v10780);
  return lam_clo_t339;
}

tll_ptr lam_fun_t361(tll_ptr __v10794, tll_env env) {
  tll_ptr A_v10807;
  tll_ptr Char_t357;
  tll_ptr EmptyString_t358;
  tll_ptr String_t359;
  tll_ptr __v10806;
  tll_ptr __v10812;
  tll_ptr a_v10804;
  tll_ptr app_ret_t360;
  tll_ptr call_ret_t349;
  tll_ptr call_ret_t350;
  tll_ptr call_ret_t352;
  tll_ptr call_ret_t353;
  tll_ptr call_ret_t354;
  tll_ptr call_ret_t355;
  tll_ptr call_ret_t356;
  tll_ptr ch_v10805;
  tll_ptr ch_v10808;
  tll_ptr ch_v10810;
  tll_ptr ch_v10811;
  tll_ptr close_tmp_t351;
  tll_ptr pair_struct_t342;
  tll_ptr pair_struct_t346;
  tll_ptr pf_v10809;
  tll_ptr recv_msg_t344;
  tll_ptr send_ch_t348;
  tll_ptr switch_ret_t343;
  tll_ptr switch_ret_t345;
  tll_ptr switch_ret_t347;
  instr_struct(&pair_struct_t342, 0, 2, 0, env[0]);
  switch (((tll_node)pair_struct_t342)->tag) {
  case 0:
    a_v10804 = ((tll_node)pair_struct_t342)->data[0];
    ch_v10805 = ((tll_node)pair_struct_t342)->data[1];
    instr_free_struct(pair_struct_t342);
    instr_recv(&recv_msg_t344, ch_v10805);
    __v10806 = recv_msg_t344;
    switch (((tll_node)__v10806)->tag) {
    case 0:
      A_v10807 = ((tll_node)__v10806)->data[0];
      ch_v10808 = ((tll_node)__v10806)->data[1];
      instr_free_struct(__v10806);
      instr_struct(&pair_struct_t346, 0, 2, 0, ch_v10808);
      switch (((tll_node)pair_struct_t346)->tag) {
      case 0:
        pf_v10809 = ((tll_node)pair_struct_t346)->data[0];
        ch_v10810 = ((tll_node)pair_struct_t346)->data[1];
        instr_free_struct(pair_struct_t346);
        call_ret_t350 = pow_i32(env[1], env[3]);
        call_ret_t349 = modn_i14(call_ret_t350, env[2]);
        instr_send(&send_ch_t348, ch_v10810, call_ret_t349);
        ch_v10811 = send_ch_t348;
        instr_close(&close_tmp_t351, ch_v10811);
        __v10812 = close_tmp_t351;
        call_ret_t356 = pow_i32(A_v10807, env[3]);
        call_ret_t355 = modn_i14(call_ret_t356, env[2]);
        call_ret_t354 = string_of_nat_i31(call_ret_t355);
        instr_struct(&Char_t357, 1, 1, (tll_ptr)10);
        instr_struct(&EmptyString_t358, 2, 0);
        instr_struct(&String_t359, 3, 2, Char_t357, EmptyString_t358);
        call_ret_t353 = cats_i15(call_ret_t354, String_t359);
        call_ret_t352 = print_i26(call_ret_t353);
        instr_app(&app_ret_t360, call_ret_t352, 0);
        instr_free_clo(call_ret_t352);
        switch_ret_t347 = app_ret_t360;
        break;
      }
      switch_ret_t345 = switch_ret_t347;
      break;
    }
    switch_ret_t343 = switch_ret_t345;
    break;
  }
  return switch_ret_t343;
}

tll_ptr bob_i37(tll_ptr b_v10790, tll_ptr p_v10791, tll_ptr g_v10792,
                tll_ptr ch_v10793) {
  tll_ptr lam_clo_t362;
  instr_clo(&lam_clo_t362, &lam_fun_t361, 4, ch_v10793, g_v10792, p_v10791,
            b_v10790);
  return lam_clo_t362;
}

tll_ptr lam_fun_t364(tll_ptr ch_v10822, tll_env env) {
  tll_ptr call_ret_t363;
  call_ret_t363 = bob_i37(env[2], env[1], env[0], ch_v10822);
  return call_ret_t363;
}

tll_ptr lam_fun_t366(tll_ptr g_v10820, tll_env env) {
  tll_ptr lam_clo_t365;
  instr_clo(&lam_clo_t365, &lam_fun_t364, 3, g_v10820, env[0], env[1]);
  return lam_clo_t365;
}

tll_ptr lam_fun_t368(tll_ptr p_v10817, tll_env env) {
  tll_ptr lam_clo_t367;
  instr_clo(&lam_clo_t367, &lam_fun_t366, 2, p_v10817, env[0]);
  return lam_clo_t367;
}

tll_ptr lam_fun_t370(tll_ptr b_v10813, tll_env env) {
  tll_ptr lam_clo_t369;
  instr_clo(&lam_clo_t369, &lam_fun_t368, 1, b_v10813);
  return lam_clo_t369;
}

tll_ptr fork_fun_t374(tll_env env) {
  tll_ptr app_ret_t373;
  tll_ptr call_ret_t372;
  tll_ptr fork_ret_t376;
  call_ret_t372 = alice_i36((tll_ptr)4, (tll_ptr)23, (tll_ptr)5, env[0]);
  instr_app(&app_ret_t373, call_ret_t372, 0);
  instr_free_clo(call_ret_t372);
  fork_ret_t376 = app_ret_t373;
  instr_free_thread(env);
  return fork_ret_t376;
}

tll_ptr fork_fun_t381(tll_env env) {
  tll_ptr __v10840;
  tll_ptr app_ret_t380;
  tll_ptr c0_v10842;
  tll_ptr c_v10841;
  tll_ptr call_ret_t379;
  tll_ptr fork_ret_t383;
  tll_ptr recv_msg_t377;
  tll_ptr switch_ret_t378;
  instr_recv(&recv_msg_t377, env[0]);
  __v10840 = recv_msg_t377;
  switch (((tll_node)__v10840)->tag) {
  case 0:
    c_v10841 = ((tll_node)__v10840)->data[0];
    c0_v10842 = ((tll_node)__v10840)->data[1];
    instr_free_struct(__v10840);
    call_ret_t379 = bob_i37((tll_ptr)3, (tll_ptr)23, (tll_ptr)5, c_v10841);
    instr_app(&app_ret_t380, call_ret_t379, 0);
    instr_free_clo(call_ret_t379);
    switch_ret_t378 = app_ret_t380;
    break;
  }
  fork_ret_t383 = switch_ret_t378;
  instr_free_thread(env);
  return fork_ret_t383;
}

tll_ptr lam_fun_t386(tll_ptr __v10824, tll_env env) {
  tll_ptr c0_v10835;
  tll_ptr c0_v10843;
  tll_ptr c_v10833;
  tll_ptr close_tmp_t385;
  tll_ptr fork_ch_t375;
  tll_ptr fork_ch_t382;
  tll_ptr send_ch_t384;
  instr_fork(&fork_ch_t375, &fork_fun_t374, 0);
  c_v10833 = fork_ch_t375;
  instr_fork(&fork_ch_t382, &fork_fun_t381, 0);
  c0_v10835 = fork_ch_t382;
  instr_send(&send_ch_t384, c0_v10835, c_v10833);
  c0_v10843 = send_ch_t384;
  instr_close(&close_tmp_t385, c0_v10843);
  return close_tmp_t385;
}

tll_ptr key_exchange_i38(tll_ptr __v10823) {
  tll_ptr lam_clo_t387;
  instr_clo(&lam_clo_t387, &lam_fun_t386, 0);
  return lam_clo_t387;
}

tll_ptr lam_fun_t389(tll_ptr __v10844, tll_env env) {
  tll_ptr call_ret_t388;
  call_ret_t388 = key_exchange_i38(__v10844);
  return call_ret_t388;
}

int main() {
  instr_init();
  tll_ptr Char_t231;
  tll_ptr Char_t234;
  tll_ptr Char_t237;
  tll_ptr Char_t240;
  tll_ptr Char_t243;
  tll_ptr Char_t246;
  tll_ptr Char_t249;
  tll_ptr Char_t252;
  tll_ptr Char_t255;
  tll_ptr Char_t258;
  tll_ptr EmptyString_t232;
  tll_ptr EmptyString_t235;
  tll_ptr EmptyString_t238;
  tll_ptr EmptyString_t241;
  tll_ptr EmptyString_t244;
  tll_ptr EmptyString_t247;
  tll_ptr EmptyString_t250;
  tll_ptr EmptyString_t253;
  tll_ptr EmptyString_t256;
  tll_ptr EmptyString_t259;
  tll_ptr String_t233;
  tll_ptr String_t236;
  tll_ptr String_t239;
  tll_ptr String_t242;
  tll_ptr String_t245;
  tll_ptr String_t248;
  tll_ptr String_t251;
  tll_ptr String_t254;
  tll_ptr String_t257;
  tll_ptr String_t260;
  tll_ptr app_ret_t392;
  tll_ptr call_ret_t391;
  tll_ptr consUU_t262;
  tll_ptr consUU_t263;
  tll_ptr consUU_t264;
  tll_ptr consUU_t265;
  tll_ptr consUU_t266;
  tll_ptr consUU_t267;
  tll_ptr consUU_t268;
  tll_ptr consUU_t269;
  tll_ptr consUU_t270;
  tll_ptr consUU_t271;
  tll_ptr lam_clo_t101;
  tll_ptr lam_clo_t111;
  tll_ptr lam_clo_t119;
  tll_ptr lam_clo_t12;
  tll_ptr lam_clo_t127;
  tll_ptr lam_clo_t133;
  tll_ptr lam_clo_t146;
  tll_ptr lam_clo_t159;
  tll_ptr lam_clo_t16;
  tll_ptr lam_clo_t172;
  tll_ptr lam_clo_t182;
  tll_ptr lam_clo_t192;
  tll_ptr lam_clo_t202;
  tll_ptr lam_clo_t212;
  tll_ptr lam_clo_t221;
  tll_ptr lam_clo_t230;
  tll_ptr lam_clo_t26;
  tll_ptr lam_clo_t285;
  tll_ptr lam_clo_t290;
  tll_ptr lam_clo_t303;
  tll_ptr lam_clo_t312;
  tll_ptr lam_clo_t341;
  tll_ptr lam_clo_t37;
  tll_ptr lam_clo_t371;
  tll_ptr lam_clo_t390;
  tll_ptr lam_clo_t48;
  tll_ptr lam_clo_t58;
  tll_ptr lam_clo_t6;
  tll_ptr lam_clo_t69;
  tll_ptr lam_clo_t74;
  tll_ptr lam_clo_t83;
  tll_ptr lam_clo_t92;
  tll_ptr nilUU_t261;
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
  instr_clo(&lam_clo_t303, &lam_fun_t302, 0);
  string_of_natclo_i75 = lam_clo_t303;
  instr_clo(&lam_clo_t312, &lam_fun_t311, 0);
  powclo_i76 = lam_clo_t312;
  instr_clo(&lam_clo_t341, &lam_fun_t340, 0);
  aliceclo_i77 = lam_clo_t341;
  instr_clo(&lam_clo_t371, &lam_fun_t370, 0);
  bobclo_i78 = lam_clo_t371;
  instr_clo(&lam_clo_t390, &lam_fun_t389, 0);
  key_exchangeclo_i79 = lam_clo_t390;
  call_ret_t391 = key_exchange_i38(0);
  instr_app(&app_ret_t392, call_ret_t391, 0);
  instr_free_clo(call_ret_t391);
  sleep(2);
  return 0;
}
