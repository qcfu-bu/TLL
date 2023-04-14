#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v4567, tll_ptr b2_v4568);
tll_ptr orb_i2(tll_ptr b1_v4572, tll_ptr b2_v4573);
tll_ptr notb_i3(tll_ptr b_v4577);
tll_ptr lten_i4(tll_ptr x_v4579, tll_ptr y_v4580);
tll_ptr gten_i5(tll_ptr x_v4584, tll_ptr y_v4585);
tll_ptr ltn_i6(tll_ptr x_v4589, tll_ptr y_v4590);
tll_ptr gtn_i7(tll_ptr x_v4594, tll_ptr y_v4595);
tll_ptr eqn_i8(tll_ptr x_v4599, tll_ptr y_v4600);
tll_ptr pred_i9(tll_ptr x_v4604);
tll_ptr addn_i10(tll_ptr x_v4606, tll_ptr y_v4607);
tll_ptr subn_i11(tll_ptr x_v4611, tll_ptr y_v4612);
tll_ptr muln_i12(tll_ptr x_v4616, tll_ptr y_v4617);
tll_ptr divn_i13(tll_ptr x_v4621, tll_ptr y_v4622);
tll_ptr modn_i14(tll_ptr x_v4626, tll_ptr y_v4627);
tll_ptr cats_i15(tll_ptr s1_v4631, tll_ptr s2_v4632);
tll_ptr strlen_i16(tll_ptr s_v4638);
tll_ptr lenUU_i33(tll_ptr A_v4642, tll_ptr xs_v4643);
tll_ptr lenUL_i32(tll_ptr A_v4651, tll_ptr xs_v4652);
tll_ptr lenLL_i30(tll_ptr A_v4660, tll_ptr xs_v4661);
tll_ptr appendUU_i37(tll_ptr A_v4669, tll_ptr xs_v4670, tll_ptr ys_v4671);
tll_ptr appendUL_i36(tll_ptr A_v4680, tll_ptr xs_v4681, tll_ptr ys_v4682);
tll_ptr appendLL_i34(tll_ptr A_v4691, tll_ptr xs_v4692, tll_ptr ys_v4693);
tll_ptr readline_i25(tll_ptr __v4702);
tll_ptr print_i26(tll_ptr s_v4717);
tll_ptr prerr_i27(tll_ptr s_v4728);

tll_ptr addnclo_i47;
tll_ptr andbclo_i38;
tll_ptr appendLLclo_i59;
tll_ptr appendULclo_i58;
tll_ptr appendUUclo_i57;
tll_ptr catsclo_i52;
tll_ptr divnclo_i50;
tll_ptr eqnclo_i45;
tll_ptr gtenclo_i42;
tll_ptr gtnclo_i44;
tll_ptr lenLLclo_i56;
tll_ptr lenULclo_i55;
tll_ptr lenUUclo_i54;
tll_ptr ltenclo_i41;
tll_ptr ltnclo_i43;
tll_ptr modnclo_i51;
tll_ptr mulnclo_i49;
tll_ptr notbclo_i40;
tll_ptr orbclo_i39;
tll_ptr predclo_i46;
tll_ptr prerrclo_i62;
tll_ptr printclo_i61;
tll_ptr readlineclo_i60;
tll_ptr strlenclo_i53;
tll_ptr subnclo_i48;

tll_ptr andb_i1(tll_ptr b1_v4567, tll_ptr b2_v4568) {
  tll_ptr ifte_ret_t1;
  if (b1_v4567) {
    ifte_ret_t1 = b2_v4568;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v4571, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v4571);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v4569, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v4569);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v4572, tll_ptr b2_v4573) {
  tll_ptr ifte_ret_t7;
  if (b1_v4572) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v4573;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v4576, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v4576);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v4574, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v4574);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v4577) {
  tll_ptr ifte_ret_t13;
  if (b_v4577) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v4578, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v4578);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v4579, tll_ptr y_v4580) {
  tll_ptr add_ret_t18; tll_ptr add_ret_t19; tll_ptr call_ret_t17;
  tll_ptr ifte_ret_t20; tll_ptr ifte_ret_t21;
  if (x_v4579) {
    if (y_v4580) {
      add_ret_t18 = x_v4579 - 1;
      add_ret_t19 = y_v4580 - 1;
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

tll_ptr lam_fun_t23(tll_ptr y_v4583, tll_env env) {
  tll_ptr call_ret_t22;
  call_ret_t22 = lten_i4(env[0], y_v4583);
  return call_ret_t22;
}

tll_ptr lam_fun_t25(tll_ptr x_v4581, tll_env env) {
  tll_ptr lam_clo_t24;
  instr_clo(&lam_clo_t24, &lam_fun_t23, 1, x_v4581);
  return lam_clo_t24;
}

tll_ptr gten_i5(tll_ptr x_v4584, tll_ptr y_v4585) {
  tll_ptr add_ret_t28; tll_ptr add_ret_t29; tll_ptr call_ret_t27;
  tll_ptr ifte_ret_t30; tll_ptr ifte_ret_t31; tll_ptr ifte_ret_t32;
  if (x_v4584) {
    if (y_v4585) {
      add_ret_t28 = x_v4584 - 1;
      add_ret_t29 = y_v4585 - 1;
      call_ret_t27 = gten_i5(add_ret_t28, add_ret_t29);
      ifte_ret_t30 = call_ret_t27;
    }
    else {
      ifte_ret_t30 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t30;
  }
  else {
    if (y_v4585) {
      ifte_ret_t31 = (tll_ptr)0;
    }
    else {
      ifte_ret_t31 = (tll_ptr)1;
    }
    ifte_ret_t32 = ifte_ret_t31;
  }
  return ifte_ret_t32;
}

tll_ptr lam_fun_t34(tll_ptr y_v4588, tll_env env) {
  tll_ptr call_ret_t33;
  call_ret_t33 = gten_i5(env[0], y_v4588);
  return call_ret_t33;
}

tll_ptr lam_fun_t36(tll_ptr x_v4586, tll_env env) {
  tll_ptr lam_clo_t35;
  instr_clo(&lam_clo_t35, &lam_fun_t34, 1, x_v4586);
  return lam_clo_t35;
}

tll_ptr ltn_i6(tll_ptr x_v4589, tll_ptr y_v4590) {
  tll_ptr add_ret_t39; tll_ptr add_ret_t40; tll_ptr call_ret_t38;
  tll_ptr ifte_ret_t41; tll_ptr ifte_ret_t42; tll_ptr ifte_ret_t43;
  if (x_v4589) {
    if (y_v4590) {
      add_ret_t39 = x_v4589 - 1;
      add_ret_t40 = y_v4590 - 1;
      call_ret_t38 = ltn_i6(add_ret_t39, add_ret_t40);
      ifte_ret_t41 = call_ret_t38;
    }
    else {
      ifte_ret_t41 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t41;
  }
  else {
    if (y_v4590) {
      ifte_ret_t42 = (tll_ptr)1;
    }
    else {
      ifte_ret_t42 = (tll_ptr)0;
    }
    ifte_ret_t43 = ifte_ret_t42;
  }
  return ifte_ret_t43;
}

tll_ptr lam_fun_t45(tll_ptr y_v4593, tll_env env) {
  tll_ptr call_ret_t44;
  call_ret_t44 = ltn_i6(env[0], y_v4593);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v4591, tll_env env) {
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v4591);
  return lam_clo_t46;
}

tll_ptr gtn_i7(tll_ptr x_v4594, tll_ptr y_v4595) {
  tll_ptr add_ret_t50; tll_ptr add_ret_t51; tll_ptr call_ret_t49;
  tll_ptr ifte_ret_t52; tll_ptr ifte_ret_t53;
  if (x_v4594) {
    if (y_v4595) {
      add_ret_t50 = x_v4594 - 1;
      add_ret_t51 = y_v4595 - 1;
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

tll_ptr lam_fun_t55(tll_ptr y_v4598, tll_env env) {
  tll_ptr call_ret_t54;
  call_ret_t54 = gtn_i7(env[0], y_v4598);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v4596, tll_env env) {
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v4596);
  return lam_clo_t56;
}

tll_ptr eqn_i8(tll_ptr x_v4599, tll_ptr y_v4600) {
  tll_ptr add_ret_t60; tll_ptr add_ret_t61; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t62; tll_ptr ifte_ret_t63; tll_ptr ifte_ret_t64;
  if (x_v4599) {
    if (y_v4600) {
      add_ret_t60 = x_v4599 - 1;
      add_ret_t61 = y_v4600 - 1;
      call_ret_t59 = eqn_i8(add_ret_t60, add_ret_t61);
      ifte_ret_t62 = call_ret_t59;
    }
    else {
      ifte_ret_t62 = (tll_ptr)0;
    }
    ifte_ret_t64 = ifte_ret_t62;
  }
  else {
    if (y_v4600) {
      ifte_ret_t63 = (tll_ptr)0;
    }
    else {
      ifte_ret_t63 = (tll_ptr)1;
    }
    ifte_ret_t64 = ifte_ret_t63;
  }
  return ifte_ret_t64;
}

tll_ptr lam_fun_t66(tll_ptr y_v4603, tll_env env) {
  tll_ptr call_ret_t65;
  call_ret_t65 = eqn_i8(env[0], y_v4603);
  return call_ret_t65;
}

tll_ptr lam_fun_t68(tll_ptr x_v4601, tll_env env) {
  tll_ptr lam_clo_t67;
  instr_clo(&lam_clo_t67, &lam_fun_t66, 1, x_v4601);
  return lam_clo_t67;
}

tll_ptr pred_i9(tll_ptr x_v4604) {
  tll_ptr add_ret_t70; tll_ptr ifte_ret_t71;
  if (x_v4604) {
    add_ret_t70 = x_v4604 - 1;
    ifte_ret_t71 = add_ret_t70;
  }
  else {
    ifte_ret_t71 = (tll_ptr)0;
  }
  return ifte_ret_t71;
}

tll_ptr lam_fun_t73(tll_ptr x_v4605, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = pred_i9(x_v4605);
  return call_ret_t72;
}

tll_ptr addn_i10(tll_ptr x_v4606, tll_ptr y_v4607) {
  tll_ptr add_ret_t76; tll_ptr add_ret_t77; tll_ptr call_ret_t75;
  tll_ptr ifte_ret_t78;
  if (x_v4606) {
    add_ret_t76 = x_v4606 - 1;
    call_ret_t75 = addn_i10(add_ret_t76, y_v4607);
    add_ret_t77 = call_ret_t75 + 1;
    ifte_ret_t78 = add_ret_t77;
  }
  else {
    ifte_ret_t78 = y_v4607;
  }
  return ifte_ret_t78;
}

tll_ptr lam_fun_t80(tll_ptr y_v4610, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = addn_i10(env[0], y_v4610);
  return call_ret_t79;
}

tll_ptr lam_fun_t82(tll_ptr x_v4608, tll_env env) {
  tll_ptr lam_clo_t81;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 1, x_v4608);
  return lam_clo_t81;
}

tll_ptr subn_i11(tll_ptr x_v4611, tll_ptr y_v4612) {
  tll_ptr add_ret_t86; tll_ptr call_ret_t84; tll_ptr call_ret_t85;
  tll_ptr ifte_ret_t87;
  if (y_v4612) {
    call_ret_t85 = pred_i9(x_v4611);
    add_ret_t86 = y_v4612 - 1;
    call_ret_t84 = subn_i11(call_ret_t85, add_ret_t86);
    ifte_ret_t87 = call_ret_t84;
  }
  else {
    ifte_ret_t87 = x_v4611;
  }
  return ifte_ret_t87;
}

tll_ptr lam_fun_t89(tll_ptr y_v4615, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = subn_i11(env[0], y_v4615);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr x_v4613, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, x_v4613);
  return lam_clo_t90;
}

tll_ptr muln_i12(tll_ptr x_v4616, tll_ptr y_v4617) {
  tll_ptr add_ret_t95; tll_ptr call_ret_t93; tll_ptr call_ret_t94;
  tll_ptr ifte_ret_t96;
  if (x_v4616) {
    add_ret_t95 = x_v4616 - 1;
    call_ret_t94 = muln_i12(add_ret_t95, y_v4617);
    call_ret_t93 = addn_i10(y_v4617, call_ret_t94);
    ifte_ret_t96 = call_ret_t93;
  }
  else {
    ifte_ret_t96 = (tll_ptr)0;
  }
  return ifte_ret_t96;
}

tll_ptr lam_fun_t98(tll_ptr y_v4620, tll_env env) {
  tll_ptr call_ret_t97;
  call_ret_t97 = muln_i12(env[0], y_v4620);
  return call_ret_t97;
}

tll_ptr lam_fun_t100(tll_ptr x_v4618, tll_env env) {
  tll_ptr lam_clo_t99;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 1, x_v4618);
  return lam_clo_t99;
}

tll_ptr divn_i13(tll_ptr x_v4621, tll_ptr y_v4622) {
  tll_ptr add_ret_t105; tll_ptr call_ret_t102; tll_ptr call_ret_t103;
  tll_ptr call_ret_t104; tll_ptr ifte_ret_t106;
  call_ret_t102 = ltn_i6(x_v4621, y_v4622);
  if (call_ret_t102) {
    ifte_ret_t106 = (tll_ptr)0;
  }
  else {
    call_ret_t104 = subn_i11(x_v4621, y_v4622);
    call_ret_t103 = divn_i13(call_ret_t104, y_v4622);
    add_ret_t105 = call_ret_t103 + 1;
    ifte_ret_t106 = add_ret_t105;
  }
  return ifte_ret_t106;
}

tll_ptr lam_fun_t108(tll_ptr y_v4625, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = divn_i13(env[0], y_v4625);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr x_v4623, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, x_v4623);
  return lam_clo_t109;
}

tll_ptr modn_i14(tll_ptr x_v4626, tll_ptr y_v4627) {
  tll_ptr call_ret_t112; tll_ptr call_ret_t113; tll_ptr call_ret_t114;
  call_ret_t114 = divn_i13(x_v4626, y_v4627);
  call_ret_t113 = muln_i12(call_ret_t114, y_v4627);
  call_ret_t112 = subn_i11(x_v4626, call_ret_t113);
  return call_ret_t112;
}

tll_ptr lam_fun_t116(tll_ptr y_v4630, tll_env env) {
  tll_ptr call_ret_t115;
  call_ret_t115 = modn_i14(env[0], y_v4630);
  return call_ret_t115;
}

tll_ptr lam_fun_t118(tll_ptr x_v4628, tll_env env) {
  tll_ptr lam_clo_t117;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 1, x_v4628);
  return lam_clo_t117;
}

tll_ptr cats_i15(tll_ptr s1_v4631, tll_ptr s2_v4632) {
  tll_ptr String_t122; tll_ptr c_v4633; tll_ptr call_ret_t121;
  tll_ptr s1_v4634; tll_ptr switch_ret_t120;
  switch(((tll_node)s1_v4631)->tag) {
    case 2:
      switch_ret_t120 = s2_v4632;
      break;
    case 3:
      c_v4633 = ((tll_node)s1_v4631)->data[0];
      s1_v4634 = ((tll_node)s1_v4631)->data[1];
      call_ret_t121 = cats_i15(s1_v4634, s2_v4632);
      instr_struct(&String_t122, 3, 2, c_v4633, call_ret_t121);
      switch_ret_t120 = String_t122;
      break;
  }
  return switch_ret_t120;
}

tll_ptr lam_fun_t124(tll_ptr s2_v4637, tll_env env) {
  tll_ptr call_ret_t123;
  call_ret_t123 = cats_i15(env[0], s2_v4637);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr s1_v4635, tll_env env) {
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, s1_v4635);
  return lam_clo_t125;
}

tll_ptr strlen_i16(tll_ptr s_v4638) {
  tll_ptr __v4639; tll_ptr add_ret_t130; tll_ptr call_ret_t129;
  tll_ptr s_v4640; tll_ptr switch_ret_t128;
  switch(((tll_node)s_v4638)->tag) {
    case 2:
      switch_ret_t128 = (tll_ptr)0;
      break;
    case 3:
      __v4639 = ((tll_node)s_v4638)->data[0];
      s_v4640 = ((tll_node)s_v4638)->data[1];
      call_ret_t129 = strlen_i16(s_v4640);
      add_ret_t130 = call_ret_t129 + 1;
      switch_ret_t128 = add_ret_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr s_v4641, tll_env env) {
  tll_ptr call_ret_t131;
  call_ret_t131 = strlen_i16(s_v4641);
  return call_ret_t131;
}

tll_ptr lenUU_i33(tll_ptr A_v4642, tll_ptr xs_v4643) {
  tll_ptr add_ret_t139; tll_ptr call_ret_t137; tll_ptr consUU_t140;
  tll_ptr n_v4646; tll_ptr nilUU_t135; tll_ptr pair_struct_t136;
  tll_ptr pair_struct_t141; tll_ptr switch_ret_t134; tll_ptr switch_ret_t138;
  tll_ptr x_v4644; tll_ptr xs_v4645; tll_ptr xs_v4647;
  switch(((tll_node)xs_v4643)->tag) {
    case 12:
      instr_struct(&nilUU_t135, 12, 0);
      instr_struct(&pair_struct_t136, 0, 2, (tll_ptr)0, nilUU_t135);
      switch_ret_t134 = pair_struct_t136;
      break;
    case 13:
      x_v4644 = ((tll_node)xs_v4643)->data[0];
      xs_v4645 = ((tll_node)xs_v4643)->data[1];
      call_ret_t137 = lenUU_i33(0, xs_v4645);
      switch(((tll_node)call_ret_t137)->tag) {
        case 0:
          n_v4646 = ((tll_node)call_ret_t137)->data[0];
          xs_v4647 = ((tll_node)call_ret_t137)->data[1];
          instr_free_struct(call_ret_t137);
          add_ret_t139 = n_v4646 + 1;
          instr_struct(&consUU_t140, 13, 2, x_v4644, xs_v4647);
          instr_struct(&pair_struct_t141, 0, 2, add_ret_t139, consUU_t140);
          switch_ret_t138 = pair_struct_t141;
          break;
      }
      switch_ret_t134 = switch_ret_t138;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t143(tll_ptr xs_v4650, tll_env env) {
  tll_ptr call_ret_t142;
  call_ret_t142 = lenUU_i33(env[0], xs_v4650);
  return call_ret_t142;
}

tll_ptr lam_fun_t145(tll_ptr A_v4648, tll_env env) {
  tll_ptr lam_clo_t144;
  instr_clo(&lam_clo_t144, &lam_fun_t143, 1, A_v4648);
  return lam_clo_t144;
}

tll_ptr lenUL_i32(tll_ptr A_v4651, tll_ptr xs_v4652) {
  tll_ptr add_ret_t152; tll_ptr call_ret_t150; tll_ptr consUL_t153;
  tll_ptr n_v4655; tll_ptr nilUL_t148; tll_ptr pair_struct_t149;
  tll_ptr pair_struct_t154; tll_ptr switch_ret_t147; tll_ptr switch_ret_t151;
  tll_ptr x_v4653; tll_ptr xs_v4654; tll_ptr xs_v4656;
  switch(((tll_node)xs_v4652)->tag) {
    case 10:
      instr_free_struct(xs_v4652);
      instr_struct(&nilUL_t148, 10, 0);
      instr_struct(&pair_struct_t149, 0, 2, (tll_ptr)0, nilUL_t148);
      switch_ret_t147 = pair_struct_t149;
      break;
    case 11:
      x_v4653 = ((tll_node)xs_v4652)->data[0];
      xs_v4654 = ((tll_node)xs_v4652)->data[1];
      instr_free_struct(xs_v4652);
      call_ret_t150 = lenUL_i32(0, xs_v4654);
      switch(((tll_node)call_ret_t150)->tag) {
        case 0:
          n_v4655 = ((tll_node)call_ret_t150)->data[0];
          xs_v4656 = ((tll_node)call_ret_t150)->data[1];
          instr_free_struct(call_ret_t150);
          add_ret_t152 = n_v4655 + 1;
          instr_struct(&consUL_t153, 11, 2, x_v4653, xs_v4656);
          instr_struct(&pair_struct_t154, 0, 2, add_ret_t152, consUL_t153);
          switch_ret_t151 = pair_struct_t154;
          break;
      }
      switch_ret_t147 = switch_ret_t151;
      break;
  }
  return switch_ret_t147;
}

tll_ptr lam_fun_t156(tll_ptr xs_v4659, tll_env env) {
  tll_ptr call_ret_t155;
  call_ret_t155 = lenUL_i32(env[0], xs_v4659);
  return call_ret_t155;
}

tll_ptr lam_fun_t158(tll_ptr A_v4657, tll_env env) {
  tll_ptr lam_clo_t157;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 1, A_v4657);
  return lam_clo_t157;
}

tll_ptr lenLL_i30(tll_ptr A_v4660, tll_ptr xs_v4661) {
  tll_ptr add_ret_t165; tll_ptr call_ret_t163; tll_ptr consLL_t166;
  tll_ptr n_v4664; tll_ptr nilLL_t161; tll_ptr pair_struct_t162;
  tll_ptr pair_struct_t167; tll_ptr switch_ret_t160; tll_ptr switch_ret_t164;
  tll_ptr x_v4662; tll_ptr xs_v4663; tll_ptr xs_v4665;
  switch(((tll_node)xs_v4661)->tag) {
    case 6:
      instr_free_struct(xs_v4661);
      instr_struct(&nilLL_t161, 6, 0);
      instr_struct(&pair_struct_t162, 0, 2, (tll_ptr)0, nilLL_t161);
      switch_ret_t160 = pair_struct_t162;
      break;
    case 7:
      x_v4662 = ((tll_node)xs_v4661)->data[0];
      xs_v4663 = ((tll_node)xs_v4661)->data[1];
      instr_free_struct(xs_v4661);
      call_ret_t163 = lenLL_i30(0, xs_v4663);
      switch(((tll_node)call_ret_t163)->tag) {
        case 0:
          n_v4664 = ((tll_node)call_ret_t163)->data[0];
          xs_v4665 = ((tll_node)call_ret_t163)->data[1];
          instr_free_struct(call_ret_t163);
          add_ret_t165 = n_v4664 + 1;
          instr_struct(&consLL_t166, 7, 2, x_v4662, xs_v4665);
          instr_struct(&pair_struct_t167, 0, 2, add_ret_t165, consLL_t166);
          switch_ret_t164 = pair_struct_t167;
          break;
      }
      switch_ret_t160 = switch_ret_t164;
      break;
  }
  return switch_ret_t160;
}

tll_ptr lam_fun_t169(tll_ptr xs_v4668, tll_env env) {
  tll_ptr call_ret_t168;
  call_ret_t168 = lenLL_i30(env[0], xs_v4668);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v4666, tll_env env) {
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v4666);
  return lam_clo_t170;
}

tll_ptr appendUU_i37(tll_ptr A_v4669, tll_ptr xs_v4670, tll_ptr ys_v4671) {
  tll_ptr call_ret_t174; tll_ptr consUU_t175; tll_ptr switch_ret_t173;
  tll_ptr x_v4672; tll_ptr xs_v4673;
  switch(((tll_node)xs_v4670)->tag) {
    case 12:
      switch_ret_t173 = ys_v4671;
      break;
    case 13:
      x_v4672 = ((tll_node)xs_v4670)->data[0];
      xs_v4673 = ((tll_node)xs_v4670)->data[1];
      call_ret_t174 = appendUU_i37(0, xs_v4673, ys_v4671);
      instr_struct(&consUU_t175, 13, 2, x_v4672, call_ret_t174);
      switch_ret_t173 = consUU_t175;
      break;
  }
  return switch_ret_t173;
}

tll_ptr lam_fun_t177(tll_ptr ys_v4679, tll_env env) {
  tll_ptr call_ret_t176;
  call_ret_t176 = appendUU_i37(env[1], env[0], ys_v4679);
  return call_ret_t176;
}

tll_ptr lam_fun_t179(tll_ptr xs_v4677, tll_env env) {
  tll_ptr lam_clo_t178;
  instr_clo(&lam_clo_t178, &lam_fun_t177, 2, xs_v4677, env[0]);
  return lam_clo_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v4674, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v4674);
  return lam_clo_t180;
}

tll_ptr appendUL_i36(tll_ptr A_v4680, tll_ptr xs_v4681, tll_ptr ys_v4682) {
  tll_ptr call_ret_t184; tll_ptr consUL_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v4683; tll_ptr xs_v4684;
  switch(((tll_node)xs_v4681)->tag) {
    case 10:
      instr_free_struct(xs_v4681);
      switch_ret_t183 = ys_v4682;
      break;
    case 11:
      x_v4683 = ((tll_node)xs_v4681)->data[0];
      xs_v4684 = ((tll_node)xs_v4681)->data[1];
      instr_free_struct(xs_v4681);
      call_ret_t184 = appendUL_i36(0, xs_v4684, ys_v4682);
      instr_struct(&consUL_t185, 11, 2, x_v4683, call_ret_t184);
      switch_ret_t183 = consUL_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v4690, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUL_i36(env[1], env[0], ys_v4690);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v4688, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v4688, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v4685, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v4685);
  return lam_clo_t190;
}

tll_ptr appendLL_i34(tll_ptr A_v4691, tll_ptr xs_v4692, tll_ptr ys_v4693) {
  tll_ptr call_ret_t194; tll_ptr consLL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v4694; tll_ptr xs_v4695;
  switch(((tll_node)xs_v4692)->tag) {
    case 6:
      instr_free_struct(xs_v4692);
      switch_ret_t193 = ys_v4693;
      break;
    case 7:
      x_v4694 = ((tll_node)xs_v4692)->data[0];
      xs_v4695 = ((tll_node)xs_v4692)->data[1];
      instr_free_struct(xs_v4692);
      call_ret_t194 = appendLL_i34(0, xs_v4695, ys_v4693);
      instr_struct(&consLL_t195, 7, 2, x_v4694, call_ret_t194);
      switch_ret_t193 = consLL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v4701, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendLL_i34(env[1], env[0], ys_v4701);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v4699, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v4699, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v4696, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v4696);
  return lam_clo_t200;
}

tll_ptr lam_fun_t208(tll_ptr __v4703, tll_env env) {
  tll_ptr __v4712; tll_ptr ch_v4710; tll_ptr ch_v4711; tll_ptr ch_v4714;
  tll_ptr ch_v4715; tll_ptr prim_ch_t203; tll_ptr recv_msg_t205;
  tll_ptr s_v4713; tll_ptr send_ch_t204; tll_ptr send_ch_t207;
  tll_ptr switch_ret_t206;
  instr_open(&prim_ch_t203, &proc_stdin);
  ch_v4710 = prim_ch_t203;
  instr_send(&send_ch_t204, ch_v4710, (tll_ptr)1);
  ch_v4711 = send_ch_t204;
  instr_recv(&recv_msg_t205, ch_v4711);
  __v4712 = recv_msg_t205;
  switch(((tll_node)__v4712)->tag) {
    case 0:
      s_v4713 = ((tll_node)__v4712)->data[0];
      ch_v4714 = ((tll_node)__v4712)->data[1];
      instr_free_struct(__v4712);
      instr_send(&send_ch_t207, ch_v4714, (tll_ptr)0);
      ch_v4715 = send_ch_t207;
      switch_ret_t206 = s_v4713;
      break;
  }
  return switch_ret_t206;
}

tll_ptr readline_i25(tll_ptr __v4702) {
  tll_ptr lam_clo_t209;
  instr_clo(&lam_clo_t209, &lam_fun_t208, 0);
  return lam_clo_t209;
}

tll_ptr lam_fun_t211(tll_ptr __v4716, tll_env env) {
  tll_ptr call_ret_t210;
  call_ret_t210 = readline_i25(__v4716);
  return call_ret_t210;
}

tll_ptr lam_fun_t217(tll_ptr __v4718, tll_env env) {
  tll_ptr ch_v4723; tll_ptr ch_v4724; tll_ptr ch_v4725; tll_ptr ch_v4726;
  tll_ptr prim_ch_t213; tll_ptr send_ch_t214; tll_ptr send_ch_t215;
  tll_ptr send_ch_t216;
  instr_open(&prim_ch_t213, &proc_stdout);
  ch_v4723 = prim_ch_t213;
  instr_send(&send_ch_t214, ch_v4723, (tll_ptr)1);
  ch_v4724 = send_ch_t214;
  instr_send(&send_ch_t215, ch_v4724, env[0]);
  ch_v4725 = send_ch_t215;
  instr_send(&send_ch_t216, ch_v4725, (tll_ptr)0);
  ch_v4726 = send_ch_t216;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v4717) {
  tll_ptr lam_clo_t218;
  instr_clo(&lam_clo_t218, &lam_fun_t217, 1, s_v4717);
  return lam_clo_t218;
}

tll_ptr lam_fun_t220(tll_ptr s_v4727, tll_env env) {
  tll_ptr call_ret_t219;
  call_ret_t219 = print_i26(s_v4727);
  return call_ret_t219;
}

tll_ptr lam_fun_t226(tll_ptr __v4729, tll_env env) {
  tll_ptr ch_v4734; tll_ptr ch_v4735; tll_ptr ch_v4736; tll_ptr ch_v4737;
  tll_ptr prim_ch_t222; tll_ptr send_ch_t223; tll_ptr send_ch_t224;
  tll_ptr send_ch_t225;
  instr_open(&prim_ch_t222, &proc_stderr);
  ch_v4734 = prim_ch_t222;
  instr_send(&send_ch_t223, ch_v4734, (tll_ptr)1);
  ch_v4735 = send_ch_t223;
  instr_send(&send_ch_t224, ch_v4735, env[0]);
  ch_v4736 = send_ch_t224;
  instr_send(&send_ch_t225, ch_v4736, (tll_ptr)0);
  ch_v4737 = send_ch_t225;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v4728) {
  tll_ptr lam_clo_t227;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 1, s_v4728);
  return lam_clo_t227;
}

tll_ptr lam_fun_t229(tll_ptr s_v4738, tll_env env) {
  tll_ptr call_ret_t228;
  call_ret_t228 = prerr_i27(s_v4738);
  return call_ret_t228;
}

int main() {
  instr_init();
  tll_ptr lam_clo_t101; tll_ptr lam_clo_t111; tll_ptr lam_clo_t119;
  tll_ptr lam_clo_t12; tll_ptr lam_clo_t127; tll_ptr lam_clo_t133;
  tll_ptr lam_clo_t146; tll_ptr lam_clo_t159; tll_ptr lam_clo_t16;
  tll_ptr lam_clo_t172; tll_ptr lam_clo_t182; tll_ptr lam_clo_t192;
  tll_ptr lam_clo_t202; tll_ptr lam_clo_t212; tll_ptr lam_clo_t221;
  tll_ptr lam_clo_t230; tll_ptr lam_clo_t26; tll_ptr lam_clo_t37;
  tll_ptr lam_clo_t48; tll_ptr lam_clo_t58; tll_ptr lam_clo_t6;
  tll_ptr lam_clo_t69; tll_ptr lam_clo_t74; tll_ptr lam_clo_t83;
  tll_ptr lam_clo_t92;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i38 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i39 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i40 = lam_clo_t16;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 0);
  ltenclo_i41 = lam_clo_t26;
  instr_clo(&lam_clo_t37, &lam_fun_t36, 0);
  gtenclo_i42 = lam_clo_t37;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  ltnclo_i43 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  gtnclo_i44 = lam_clo_t58;
  instr_clo(&lam_clo_t69, &lam_fun_t68, 0);
  eqnclo_i45 = lam_clo_t69;
  instr_clo(&lam_clo_t74, &lam_fun_t73, 0);
  predclo_i46 = lam_clo_t74;
  instr_clo(&lam_clo_t83, &lam_fun_t82, 0);
  addnclo_i47 = lam_clo_t83;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  subnclo_i48 = lam_clo_t92;
  instr_clo(&lam_clo_t101, &lam_fun_t100, 0);
  mulnclo_i49 = lam_clo_t101;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 0);
  divnclo_i50 = lam_clo_t111;
  instr_clo(&lam_clo_t119, &lam_fun_t118, 0);
  modnclo_i51 = lam_clo_t119;
  instr_clo(&lam_clo_t127, &lam_fun_t126, 0);
  catsclo_i52 = lam_clo_t127;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 0);
  strlenclo_i53 = lam_clo_t133;
  instr_clo(&lam_clo_t146, &lam_fun_t145, 0);
  lenUUclo_i54 = lam_clo_t146;
  instr_clo(&lam_clo_t159, &lam_fun_t158, 0);
  lenULclo_i55 = lam_clo_t159;
  instr_clo(&lam_clo_t172, &lam_fun_t171, 0);
  lenLLclo_i56 = lam_clo_t172;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 0);
  appendUUclo_i57 = lam_clo_t182;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 0);
  appendULclo_i58 = lam_clo_t192;
  instr_clo(&lam_clo_t202, &lam_fun_t201, 0);
  appendLLclo_i59 = lam_clo_t202;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  readlineclo_i60 = lam_clo_t212;
  instr_clo(&lam_clo_t221, &lam_fun_t220, 0);
  printclo_i61 = lam_clo_t221;
  instr_clo(&lam_clo_t230, &lam_fun_t229, 0);
  prerrclo_i62 = lam_clo_t230;
  return 0;
}

