#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v5649, tll_ptr b2_v5650);
tll_ptr orb_i2(tll_ptr b1_v5654, tll_ptr b2_v5655);
tll_ptr notb_i3(tll_ptr b_v5659);
tll_ptr lten_i4(tll_ptr x_v5661, tll_ptr y_v5662);
tll_ptr gten_i5(tll_ptr x_v5666, tll_ptr y_v5667);
tll_ptr ltn_i6(tll_ptr x_v5671, tll_ptr y_v5672);
tll_ptr gtn_i7(tll_ptr x_v5676, tll_ptr y_v5677);
tll_ptr eqn_i8(tll_ptr x_v5681, tll_ptr y_v5682);
tll_ptr pred_i9(tll_ptr x_v5686);
tll_ptr addn_i10(tll_ptr x_v5688, tll_ptr y_v5689);
tll_ptr subn_i11(tll_ptr x_v5693, tll_ptr y_v5694);
tll_ptr muln_i12(tll_ptr x_v5698, tll_ptr y_v5699);
tll_ptr divn_i13(tll_ptr x_v5703, tll_ptr y_v5704);
tll_ptr modn_i14(tll_ptr x_v5708, tll_ptr y_v5709);
tll_ptr cats_i15(tll_ptr s1_v5713, tll_ptr s2_v5714);
tll_ptr strlen_i16(tll_ptr s_v5720);
tll_ptr lenUU_i38(tll_ptr A_v5724, tll_ptr xs_v5725);
tll_ptr lenUL_i37(tll_ptr A_v5733, tll_ptr xs_v5734);
tll_ptr lenLL_i35(tll_ptr A_v5742, tll_ptr xs_v5743);
tll_ptr appendUU_i42(tll_ptr A_v5751, tll_ptr xs_v5752, tll_ptr ys_v5753);
tll_ptr appendUL_i41(tll_ptr A_v5762, tll_ptr xs_v5763, tll_ptr ys_v5764);
tll_ptr appendLL_i39(tll_ptr A_v5773, tll_ptr xs_v5774, tll_ptr ys_v5775);
tll_ptr readline_i25(tll_ptr __v5784);
tll_ptr print_i26(tll_ptr s_v5799);
tll_ptr prerr_i27(tll_ptr s_v5810);
tll_ptr id_i28(tll_ptr n_v5821, tll_ptr acc_v5822);
tll_ptr idM_i29(tll_ptr n_v5826, tll_ptr acc_v5827);
tll_ptr get_at_i31(tll_ptr A_v5832, tll_ptr n_v5833, tll_ptr xs_v5834, tll_ptr a_v5835);
tll_ptr string_of_digit_i32(tll_ptr n_v5850);
tll_ptr string_of_nat_i33(tll_ptr n_v5852);

tll_ptr addnclo_i52;
tll_ptr andbclo_i43;
tll_ptr appendLLclo_i64;
tll_ptr appendULclo_i63;
tll_ptr appendUUclo_i62;
tll_ptr catsclo_i57;
tll_ptr digits_i30;
tll_ptr divnclo_i55;
tll_ptr eqnclo_i50;
tll_ptr get_atclo_i70;
tll_ptr gtenclo_i47;
tll_ptr gtnclo_i49;
tll_ptr idMclo_i69;
tll_ptr idclo_i68;
tll_ptr lenLLclo_i61;
tll_ptr lenULclo_i60;
tll_ptr lenUUclo_i59;
tll_ptr ltenclo_i46;
tll_ptr ltnclo_i48;
tll_ptr modnclo_i56;
tll_ptr mulnclo_i54;
tll_ptr notbclo_i45;
tll_ptr orbclo_i44;
tll_ptr predclo_i51;
tll_ptr prerrclo_i67;
tll_ptr printclo_i66;
tll_ptr readlineclo_i65;
tll_ptr string_of_digitclo_i71;
tll_ptr string_of_natclo_i72;
tll_ptr strlenclo_i58;
tll_ptr subnclo_i53;

tll_ptr andb_i1(tll_ptr b1_v5649, tll_ptr b2_v5650) {
  tll_ptr ifte_ret_t1;
  if (b1_v5649) {
    ifte_ret_t1 = b2_v5650;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v5653, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v5653);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v5651, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v5651);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v5654, tll_ptr b2_v5655) {
  tll_ptr ifte_ret_t7;
  if (b1_v5654) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v5655;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v5658, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v5658);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v5656, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v5656);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v5659) {
  tll_ptr ifte_ret_t13;
  if (b_v5659) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v5660, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v5660);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v5661, tll_ptr y_v5662) {
  tll_ptr add_ret_t18; tll_ptr add_ret_t19; tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  if (x_v5661) {
    if (y_v5662) {
      add_ret_t18 = x_v5661 - 1;
      add_ret_t19 = y_v5662 - 1;
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

tll_ptr lam_fun_t23(tll_ptr y_v5665, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v5665);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v5663, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v5663);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v5666, tll_ptr y_v5667) {
  tll_ptr add_ret_t28; tll_ptr add_ret_t29; tll_ptr call_ret_t27;
  tll_ptr ifte_ret_t30; tll_ptr ifte_ret_t31; tll_ptr ifte_ret_t32;
  if (x_v5666) {
    if (y_v5667) {
      add_ret_t28 = x_v5666 - 1;
      add_ret_t29 = y_v5667 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v5667) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v5670, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v5670);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v5668, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v5668);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v5671, tll_ptr y_v5672) {
  tll_ptr add_ret_t39; tll_ptr add_ret_t40; tll_ptr call_ret_t38;
  tll_ptr ifte_ret_t41; tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t43;
  if (x_v5671) {
    if (y_v5672) {
      add_ret_t39 = x_v5671 - 1;
      add_ret_t40 = y_v5672 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v5672) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v5675, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v5675);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v5673, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v5673);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v5676, tll_ptr y_v5677) {
  tll_ptr add_ret_t50; tll_ptr add_ret_t51; tll_ptr call_ret_t49;
  tll_ptr ifte_ret_t52; tll_ptr ifte_ret_t53;
  if (x_v5676) {
    if (y_v5677) {
      add_ret_t50 = x_v5676 - 1;
      add_ret_t51 = y_v5677 - 1;
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

tll_ptr lam_fun_t55(tll_ptr y_v5680, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v5680);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v5678, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v5678);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v5681, tll_ptr y_v5682) {
  tll_ptr add_ret_t60; tll_ptr add_ret_t61; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t62; tll_ptr ifte_ret_t63; tll_ptr ifte_ret_t64;
  if (x_v5681) {
    if (y_v5682) {
      add_ret_t60 = x_v5681 - 1;
      add_ret_t61 = y_v5682 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v5682) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v5685, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v5685);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v5683, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v5683);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v5686) {
  tll_ptr add_ret_t70; tll_ptr ifte_ret_t71;
  if (x_v5686) {
    add_ret_t70 = x_v5686 - 1;
    ifte_ret_t71 = add_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v5687, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v5687);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v5688, tll_ptr y_v5689) {
  tll_ptr add_ret_t76; tll_ptr add_ret_t77; tll_ptr call_ret_t75;
  tll_ptr ifte_ret_t78;
  if (x_v5688) {
    add_ret_t76 = x_v5688 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v5689);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v5689;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v5692, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v5692);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v5690, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v5690);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v5693, tll_ptr y_v5694) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v5694) {
    call_ret_t85 = pred_i9(x_v5693);
    add_ret_t86 = y_v5694 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v5693;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v5697, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v5697);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v5695, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v5695);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v5698, tll_ptr y_v5699) {
  tll_ptr add_ret_t95; tll_ptr call_ret_t93; tll_ptr call_ret_t94;
  tll_ptr ifte_ret_t96;
  if (x_v5698) {
    add_ret_t95 = x_v5698 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v5699);
    call_ret_t93 = addn_i10(y_v5699, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v5702, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v5702);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v5700, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v5700);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v5703, tll_ptr y_v5704) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v5703, y_v5704);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v5703, y_v5704);
    call_ret_t103 = divn_i13(call_ret_t104, y_v5704);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v5707, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v5707);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v5705, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v5705);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v5708, tll_ptr y_v5709) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v5708, y_v5709);
  call_ret_t113 = muln_i12(call_ret_t114, y_v5709);
  call_ret_t112 = subn_i11(x_v5708, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v5712, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v5712);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v5710, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v5710);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v5713, tll_ptr s2_v5714) {
  tll_ptr String_t122; tll_ptr c_v5715; tll_ptr call_ret_t121;
  tll_ptr s1_v5716; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v5713)->tag) {
    case 2:
      switch_ret_t120 = s2_v5714;
      break;
    case 3:
      c_v5715 = ((tll_node)s1_v5713)->data[0];
      s1_v5716 = ((tll_node)s1_v5713)->data[1];
      call_ret_t121 = cats_i15(s1_v5716, s2_v5714);
      instr_struct(&String_t122, 3, 2, c_v5715, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v5719, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v5719);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v5717, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v5717);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v5720) {
  tll_ptr __v5721; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v5722; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v5720)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v5721 = ((tll_node)s_v5720)->data[0];
      s_v5722 = ((tll_node)s_v5720)->data[1];
      call_ret_t129 = strlen_i16(s_v5722);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v5723, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v5723);
  return call_ret_t131;
}

tll_ptr lenUU_i38(tll_ptr A_v5724, tll_ptr xs_v5725) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v5728; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v5726; tll_ptr xs_v5727; tll_ptr xs_v5729;
  switch(((tll_node)xs_v5725)->tag) {
    case 12:
      instr_struct(&nilUU_t135, 12, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 13:
      x_v5726 = ((tll_node)xs_v5725)->data[0];
      xs_v5727 = ((tll_node)xs_v5725)->data[1];
      call_ret_t137 = lenUU_i38(0, xs_v5727);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v5728 = ((tll_node)call_ret_t137)->data[0];
          xs_v5729 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v5728 + 1;
          instr_struct(&consUU_t140, 13, 2, x_v5726, xs_v5729);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v5732, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i38(env[0], xs_v5732);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v5730, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v5730);
  return lam_clo_t144;
}

tll_ptr lenUL_i37(tll_ptr A_v5733, tll_ptr xs_v5734) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v5737; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v5735; tll_ptr xs_v5736; tll_ptr xs_v5738;
  switch(((tll_node)xs_v5734)->tag) {
    case 10:
      instr_free_struct(xs_v5734);
      instr_struct(&nilUL_t148, 10, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 11:
      x_v5735 = ((tll_node)xs_v5734)->data[0];
      xs_v5736 = ((tll_node)xs_v5734)->data[1];
      instr_free_struct(xs_v5734);
      call_ret_t150 = lenUL_i37(0, xs_v5736);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v5737 = ((tll_node)call_ret_t150)->data[0];
          xs_v5738 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v5737 + 1;
          instr_struct(&consUL_t153, 11, 2, x_v5735, xs_v5738);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v5741, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i37(env[0], xs_v5741);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v5739, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v5739);
  return lam_clo_t157;
}

tll_ptr lenLL_i35(tll_ptr A_v5742, tll_ptr xs_v5743) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v5746; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v5744; tll_ptr xs_v5745; tll_ptr xs_v5747;
  switch(((tll_node)xs_v5743)->tag) {
    case 6:
      instr_free_struct(xs_v5743);
      instr_struct(&nilLL_t161, 6, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 7:
      x_v5744 = ((tll_node)xs_v5743)->data[0];
      xs_v5745 = ((tll_node)xs_v5743)->data[1];
      instr_free_struct(xs_v5743);
      call_ret_t163 = lenLL_i35(0, xs_v5745);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v5746 = ((tll_node)call_ret_t163)->data[0];
          xs_v5747 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v5746 + 1;
          instr_struct(&consLL_t166, 7, 2, x_v5744, xs_v5747);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v5750, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i35(env[0], xs_v5750);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v5748, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v5748);
  return lam_clo_t170;
}

tll_ptr appendUU_i42(tll_ptr A_v5751, tll_ptr xs_v5752, tll_ptr ys_v5753) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v5754; tll_ptr xs_v5755;
  switch(((tll_node)xs_v5752)->tag) {
    case 12:
      switch_ret_t173 = ys_v5753;
      break;
    case 13:
      x_v5754 = ((tll_node)xs_v5752)->data[0];
      xs_v5755 = ((tll_node)xs_v5752)->data[1];
      call_ret_t174 = appendUU_i42(0, xs_v5755, ys_v5753);
      instr_struct(&consUU_t175, 13, 2, x_v5754, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v5761, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i42(env[1], env[0], ys_v5761);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v5759, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v5759, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v5756, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v5756);
  return lam_clo_t180;
}

tll_ptr appendUL_i41(tll_ptr A_v5762, tll_ptr xs_v5763, tll_ptr ys_v5764) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v5765; tll_ptr xs_v5766;
  switch(((tll_node)xs_v5763)->tag) {
    case 10:
      instr_free_struct(xs_v5763);
      switch_ret_t183 = ys_v5764;
      break;
    case 11:
      x_v5765 = ((tll_node)xs_v5763)->data[0];
      xs_v5766 = ((tll_node)xs_v5763)->data[1];
      instr_free_struct(xs_v5763);
      call_ret_t184 = appendUL_i41(0, xs_v5766, ys_v5764);
      instr_struct(&consUL_t185, 11, 2, x_v5765, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v5772, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i41(env[1], env[0], ys_v5772);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v5770, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v5770, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v5767, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v5767);
  return lam_clo_t190;
}

tll_ptr appendLL_i39(tll_ptr A_v5773, tll_ptr xs_v5774, tll_ptr ys_v5775) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v5776; tll_ptr xs_v5777;
  switch(((tll_node)xs_v5774)->tag) {
    case 6:
      instr_free_struct(xs_v5774);
      switch_ret_t193 = ys_v5775;
      break;
    case 7:
      x_v5776 = ((tll_node)xs_v5774)->data[0];
      xs_v5777 = ((tll_node)xs_v5774)->data[1];
      instr_free_struct(xs_v5774);
      call_ret_t194 = appendLL_i39(0, xs_v5777, ys_v5775);
      instr_struct(&consLL_t195, 7, 2, x_v5776, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v5783, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i39(env[1], env[0], ys_v5783);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v5781, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v5781, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v5778, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v5778);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v5785, tll_env env) {
  tll_ptr __v5794; tll_ptr ch_v5792; tll_ptr ch_v5793; tll_ptr ch_v5796;
  tll_ptr ch_v5797; tll_ptr prim_ch_t203; tll_ptr recv_msg_t205;
  tll_ptr s_v5795; tll_ptr send_ch_t204; tll_ptr send_ch_t207;
  tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v5792 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v5792, (tll_ptr)1);
  ch_v5793 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v5793);
  __v5794 = recv_msg_t205;
  switch(((tll_node)__v5794)->tag) {
    case 0:
      s_v5795 = ((tll_node)__v5794)->data[0];
      ch_v5796 = ((tll_node)__v5794)->data[1];
      instr_free_struct(__v5794);
      instr_send(&send_ch_t207, ch_v5796, (tll_ptr)0);
      ch_v5797 = send_ch_t207;
      switch_ret_t206 = s_v5795;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v5784) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v5798, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v5798);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v5800, tll_env env) {
  tll_ptr ch_v5805; tll_ptr ch_v5806; tll_ptr ch_v5807; tll_ptr ch_v5808;
  tll_ptr prim_ch_t213; tll_ptr send_ch_t214; tll_ptr send_ch_t215;
  tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v5805 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v5805, (tll_ptr)1);
  ch_v5806 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v5806, env[0]);
  ch_v5807 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v5807, (tll_ptr)0);
  ch_v5808 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v5799) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v5799);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v5809, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v5809);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v5811, tll_env env) {
  tll_ptr ch_v5816; tll_ptr ch_v5817; tll_ptr ch_v5818; tll_ptr ch_v5819;
  tll_ptr prim_ch_t222; tll_ptr send_ch_t223; tll_ptr send_ch_t224;
  tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v5816 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v5816, (tll_ptr)1);
  ch_v5817 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v5817, env[0]);
  ch_v5818 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v5818, (tll_ptr)0);
  ch_v5819 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v5810) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v5810);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v5820, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v5820);
  return call_ret_t228;
}

tll_ptr id_i28(tll_ptr n_v5821, tll_ptr acc_v5822) {
  tll_ptr add_ret_t232; tll_ptr add_ret_t233; tll_ptr call_ret_t231;
  tll_ptr ifte_ret_t234;
  if (n_v5821) {
    add_ret_t232 = n_v5821 - 1;
    add_ret_t233 = acc_v5822 + 1;
    call_ret_t231 = id_i28(add_ret_t232, add_ret_t233);
    ifte_ret_t234 = call_ret_t231;
  }
  else {
    ifte_ret_t234 = acc_v5822;
  }
  return ifte_ret_t234;
}

tll_ptr lam_fun_t236(tll_ptr acc_v5825, tll_env env) {
  tll_ptr call_ret_t235;
  call_ret_t235 = id_i28(env[0], acc_v5825);
  return call_ret_t235;
}

tll_ptr lam_fun_t238(tll_ptr n_v5823, tll_env env) {
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, n_v5823);
  return lam_clo_t237;
}

tll_ptr lam_fun_t243(tll_ptr __v5828, tll_env env) {
  
  
  return env[0];
}

tll_ptr idM_i29(tll_ptr n_v5826, tll_ptr acc_v5827) {
  tll_ptr add_ret_t241; tll_ptr add_ret_t242; tll_ptr call_ret_t240;
  tll_ptr ifte_ret_t245; tll_ptr lam_clo_t244;
  if (n_v5826) {
    add_ret_t241 = n_v5826 - 1;
    add_ret_t242 = acc_v5827 + 1;
    call_ret_t240 = idM_i29(add_ret_t241, add_ret_t242);
    ifte_ret_t245 = call_ret_t240;
  }
  else {
    instr_clo(&lam_clo_t244, &lam_fun_t243, 1, acc_v5827);
    ifte_ret_t245 = lam_clo_t244;
  }
  return ifte_ret_t245;
}

tll_ptr lam_fun_t247(tll_ptr acc_v5831, tll_env env) {
  tll_ptr call_ret_t246;
  call_ret_t246 = idM_i29(env[0], acc_v5831);
  return call_ret_t246;
}

tll_ptr lam_fun_t249(tll_ptr n_v5829, tll_env env) {
  tll_ptr lam_clo_t248;
  instr_clo(&lam_clo_t248, &lam_fun_t247, 1, n_v5829);
  return lam_clo_t248;
}

tll_ptr get_at_i31(tll_ptr A_v5832, tll_ptr n_v5833, tll_ptr xs_v5834, tll_ptr a_v5835) {
  tll_ptr __v5836; tll_ptr __v5839; tll_ptr add_ret_t294;
  tll_ptr call_ret_t293; tll_ptr ifte_ret_t296; tll_ptr switch_ret_t292;
  tll_ptr switch_ret_t295; tll_ptr x_v5838; tll_ptr xs_v5837;
  if (n_v5833) {
    switch(((tll_node)xs_v5834)->tag) {
      case 12:
        switch_ret_t292 = a_v5835;
        break;
      case 13:
        __v5836 = ((tll_node)xs_v5834)->data[0];
        xs_v5837 = ((tll_node)xs_v5834)->data[1];
        add_ret_t294 = n_v5833 - 1;
        call_ret_t293 = get_at_i31(0, add_ret_t294, xs_v5837, a_v5835);
        switch_ret_t292 = call_ret_t293;
        break;
    }
    ifte_ret_t296 = switch_ret_t292;
  }
  else {
    switch(((tll_node)xs_v5834)->tag) {
      case 12:
        switch_ret_t295 = a_v5835;
        break;
      case 13:
        x_v5838 = ((tll_node)xs_v5834)->data[0];
        __v5839 = ((tll_node)xs_v5834)->data[1];
        switch_ret_t295 = x_v5838;
        break;
    }
    ifte_ret_t296 = switch_ret_t295;
  }
  return ifte_ret_t296;
}

tll_ptr lam_fun_t298(tll_ptr a_v5849, tll_env env) {
  tll_ptr call_ret_t297;
  call_ret_t297 = get_at_i31(env[2], env[1], env[0], a_v5849);
  return call_ret_t297;
}

tll_ptr lam_fun_t300(tll_ptr xs_v5847, tll_env env) {
  tll_ptr lam_clo_t299;
  instr_clo(&lam_clo_t299, &lam_fun_t298, 3, xs_v5847, env[0], env[1]);
  return lam_clo_t299;
}

tll_ptr lam_fun_t302(tll_ptr n_v5844, tll_env env) {
  tll_ptr lam_clo_t301;
  instr_clo(&lam_clo_t301, &lam_fun_t300, 2, n_v5844, env[0]);
  return lam_clo_t301;
}

tll_ptr lam_fun_t304(tll_ptr A_v5840, tll_env env) {
  tll_ptr lam_clo_t303;
  instr_clo(&lam_clo_t303, &lam_fun_t302, 1, A_v5840);
  return lam_clo_t303;
}

tll_ptr string_of_digit_i32(tll_ptr n_v5850) {
  tll_ptr EmptyString_t307; tll_ptr call_ret_t306;
  instr_struct(&EmptyString_t307, 2, 0);
  call_ret_t306 = get_at_i31(0, n_v5850, digits_i30, EmptyString_t307);
  return call_ret_t306;
}

tll_ptr lam_fun_t309(tll_ptr n_v5851, tll_env env) {
  tll_ptr call_ret_t308;
  call_ret_t308 = string_of_digit_i32(n_v5851);
  return call_ret_t308;
}

tll_ptr string_of_nat_i33(tll_ptr n_v5852) {
  tll_ptr call_ret_t311; tll_ptr call_ret_t312; tll_ptr call_ret_t313;
  tll_ptr call_ret_t314; tll_ptr call_ret_t315; tll_ptr call_ret_t316;
  tll_ptr ifte_ret_t317; tll_ptr n_v5854; tll_ptr s_v5853;
  call_ret_t312 = modn_i14(n_v5852, (tll_ptr)10);
  call_ret_t311 = string_of_digit_i32(call_ret_t312);
  s_v5853 = call_ret_t311;
  call_ret_t313 = divn_i13(n_v5852, (tll_ptr)10);
  n_v5854 = call_ret_t313;
  call_ret_t314 = ltn_i6((tll_ptr)0, n_v5854);
  if (call_ret_t314) {
    call_ret_t316 = string_of_nat_i33(n_v5854);
    call_ret_t315 = cats_i15(call_ret_t316, s_v5853);
    ifte_ret_t317 = call_ret_t315;
  }
  else {
    ifte_ret_t317 = s_v5853;
  }
  return ifte_ret_t317;
}

tll_ptr lam_fun_t319(tll_ptr n_v5855, tll_env env) {
  tll_ptr call_ret_t318;
  call_ret_t318 = string_of_nat_i33(n_v5855);
  return call_ret_t318;
}

int main() {
  instr_init();
  tll_ptr Char_t251; tll_ptr Char_t254; tll_ptr Char_t257; tll_ptr Char_t260;
  tll_ptr Char_t263; tll_ptr Char_t266; tll_ptr Char_t269; tll_ptr Char_t272;
  tll_ptr Char_t275; tll_ptr Char_t278; tll_ptr EmptyString_t252;
  tll_ptr EmptyString_t255; tll_ptr EmptyString_t258;
  tll_ptr EmptyString_t261; tll_ptr EmptyString_t264;
  tll_ptr EmptyString_t267; tll_ptr EmptyString_t270;
  tll_ptr EmptyString_t273; tll_ptr EmptyString_t276;
  tll_ptr EmptyString_t279; tll_ptr String_t253; tll_ptr String_t256;
  tll_ptr String_t259; tll_ptr String_t262; tll_ptr String_t265;
  tll_ptr String_t268; tll_ptr String_t271; tll_ptr String_t274;
  tll_ptr String_t277; tll_ptr String_t280; tll_ptr app_ret_t322;
  tll_ptr call_ret_t321; tll_ptr consUU_t282; tll_ptr consUU_t283;
  tll_ptr consUU_t284; tll_ptr consUU_t285; tll_ptr consUU_t286;
  tll_ptr consUU_t287; tll_ptr consUU_t288; tll_ptr consUU_t289;
  tll_ptr consUU_t290; tll_ptr consUU_t291; tll_ptr lam_clo_t101;
  tll_ptr lam_clo_t111; tll_ptr lam_clo_t119; tll_ptr lam_clo_t12;
  tll_ptr lam_clo_t127; tll_ptr lam_clo_t133; tll_ptr lam_clo_t146;
  tll_ptr lam_clo_t159; tll_ptr lam_clo_t16; tll_ptr lam_clo_t172;
  tll_ptr lam_clo_t182; tll_ptr lam_clo_t192; tll_ptr lam_clo_t202;
  tll_ptr lam_clo_t212; tll_ptr lam_clo_t221; tll_ptr lam_clo_t230;
  tll_ptr lam_clo_t239; tll_ptr lam_clo_t250; tll_ptr lam_clo_t26;
  tll_ptr lam_clo_t305; tll_ptr lam_clo_t310; tll_ptr lam_clo_t320;
  tll_ptr lam_clo_t37; tll_ptr lam_clo_t48; tll_ptr lam_clo_t58;
  tll_ptr lam_clo_t6; tll_ptr lam_clo_t69; tll_ptr lam_clo_t74;
  tll_ptr lam_clo_t83; tll_ptr lam_clo_t92; tll_ptr nilUU_t281;
  tll_ptr x_v5856;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i43 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i44 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i45 = lam_clo_t16;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 0);
  ltenclo_i46 = lam_clo_t26;
  instr_clo(&lam_clo_t37, &lam_fun_t36, 0);
  gtenclo_i47 = lam_clo_t37;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  ltnclo_i48 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  gtnclo_i49 = lam_clo_t58;
  instr_clo(&lam_clo_t69, &lam_fun_t68, 0);
  eqnclo_i50 = lam_clo_t69;
  instr_clo(&lam_clo_t74, &lam_fun_t73, 0);
  predclo_i51 = lam_clo_t74;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i52 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i53 = lam_clo_t92;
  instr_clo(&lam_clo_t101, &lam_fun_t100, 0);
  mulnclo_i54 = lam_clo_t101;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 0);
  divnclo_i55 = lam_clo_t111;
  instr_clo(&lam_clo_t119, &lam_fun_t118, 0);
  modnclo_i56 = lam_clo_t119;
  instr_clo(&lam_clo_t127, &lam_fun_t126, 0);
  catsclo_i57 = lam_clo_t127;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 0);
  strlenclo_i58 = lam_clo_t133;
  instr_clo(&lam_clo_t146, &lam_fun_t145, 0);
  lenUUclo_i59 = lam_clo_t146;
  instr_clo(&lam_clo_t159, &lam_fun_t158, 0);
  lenULclo_i60 = lam_clo_t159;
  instr_clo(&lam_clo_t172, &lam_fun_t171, 0);
  lenLLclo_i61 = lam_clo_t172;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 0);
  appendUUclo_i62 = lam_clo_t182;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 0);
  appendULclo_i63 = lam_clo_t192;
  instr_clo(&lam_clo_t202, &lam_fun_t201, 0);
  appendLLclo_i64 = lam_clo_t202;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  readlineclo_i65 = lam_clo_t212;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 0);
  printclo_i66 = lam_clo_t221;
  instr_clo(&lam_clo_t230, &lam_fun_t229, 0);
  prerrclo_i67 = lam_clo_t230;
  instr_clo(&lam_clo_t239, &lam_fun_t238, 0);
  idclo_i68 = lam_clo_t239;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 0);
  idMclo_i69 = lam_clo_t250;
  instr_struct(&Char_t251, 1, 1, (tll_ptr)48);
  instr_struct(&EmptyString_t252, 2, 0);
  instr_struct(&String_t253, 3, 2, Char_t251, EmptyString_t252);
  instr_struct(&Char_t254, 1, 1, (tll_ptr)49);
  instr_struct(&EmptyString_t255, 2, 0);
  instr_struct(&String_t256, 3, 2, Char_t254, EmptyString_t255);
  instr_struct(&Char_t257, 1, 1, (tll_ptr)50);
  instr_struct(&EmptyString_t258, 2, 0);
  instr_struct(&String_t259, 3, 2, Char_t257, EmptyString_t258);
  instr_struct(&Char_t260, 1, 1, (tll_ptr)51);
  instr_struct(&EmptyString_t261, 2, 0);
  instr_struct(&String_t262, 3, 2, Char_t260, EmptyString_t261);
  instr_struct(&Char_t263, 1, 1, (tll_ptr)52);
  instr_struct(&EmptyString_t264, 2, 0);
  instr_struct(&String_t265, 3, 2, Char_t263, EmptyString_t264);
  instr_struct(&Char_t266, 1, 1, (tll_ptr)53);
  instr_struct(&EmptyString_t267, 2, 0);
  instr_struct(&String_t268, 3, 2, Char_t266, EmptyString_t267);
  instr_struct(&Char_t269, 1, 1, (tll_ptr)54);
  instr_struct(&EmptyString_t270, 2, 0);
  instr_struct(&String_t271, 3, 2, Char_t269, EmptyString_t270);
  instr_struct(&Char_t272, 1, 1, (tll_ptr)55);
  instr_struct(&EmptyString_t273, 2, 0);
  instr_struct(&String_t274, 3, 2, Char_t272, EmptyString_t273);
  instr_struct(&Char_t275, 1, 1, (tll_ptr)56);
  instr_struct(&EmptyString_t276, 2, 0);
  instr_struct(&String_t277, 3, 2, Char_t275, EmptyString_t276);
  instr_struct(&Char_t278, 1, 1, (tll_ptr)57);
  instr_struct(&EmptyString_t279, 2, 0);
  instr_struct(&String_t280, 3, 2, Char_t278, EmptyString_t279);
  instr_struct(&nilUU_t281, 12, 0);
  instr_struct(&consUU_t282, 13, 2, String_t280, nilUU_t281);
  instr_struct(&consUU_t283, 13, 2, String_t277, consUU_t282);
  instr_struct(&consUU_t284, 13, 2, String_t274, consUU_t283);
  instr_struct(&consUU_t285, 13, 2, String_t271, consUU_t284);
  instr_struct(&consUU_t286, 13, 2, String_t268, consUU_t285);
  instr_struct(&consUU_t287, 13, 2, String_t265, consUU_t286);
  instr_struct(&consUU_t288, 13, 2, String_t262, consUU_t287);
  instr_struct(&consUU_t289, 13, 2, String_t259, consUU_t288);
  instr_struct(&consUU_t290, 13, 2, String_t256, consUU_t289);
  instr_struct(&consUU_t291, 13, 2, String_t253, consUU_t290);
  digits_i30 = consUU_t291;
  instr_clo(&lam_clo_t305, &lam_fun_t304, 0);
  get_atclo_i70 = lam_clo_t305;
  instr_clo(&lam_clo_t310, &lam_fun_t309, 0);
  string_of_digitclo_i71 = lam_clo_t310;
  instr_clo(&lam_clo_t320, &lam_fun_t319, 0);
  string_of_natclo_i72 = lam_clo_t320;
  call_ret_t321 = idM_i29((tll_ptr)8000000, (tll_ptr)0);
  instr_app(&app_ret_t322, call_ret_t321, 0);
  instr_free_clo(call_ret_t321);
  x_v5856 = app_ret_t322;
  return 0;
}

