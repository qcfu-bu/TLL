#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v4040, tll_ptr b2_v4041);
tll_ptr orb_i2(tll_ptr b1_v4045, tll_ptr b2_v4046);
tll_ptr notb_i3(tll_ptr b_v4050);
tll_ptr lten_i4(tll_ptr x_v4052, tll_ptr y_v4053);
tll_ptr gten_i5(tll_ptr x_v4059, tll_ptr y_v4060);
tll_ptr ltn_i6(tll_ptr x_v4067, tll_ptr y_v4068);
tll_ptr gtn_i7(tll_ptr x_v4075, tll_ptr y_v4076);
tll_ptr eqn_i8(tll_ptr x_v4082, tll_ptr y_v4083);
tll_ptr pred_i9(tll_ptr x_v4090);
tll_ptr addn_i10(tll_ptr x_v4093, tll_ptr y_v4094);
tll_ptr subn_i11(tll_ptr x_v4099, tll_ptr y_v4100);
tll_ptr muln_i12(tll_ptr x_v4105, tll_ptr y_v4106);
tll_ptr divn_i13(tll_ptr x_v4111, tll_ptr y_v4112);
tll_ptr modn_i14(tll_ptr x_v4116, tll_ptr y_v4117);
tll_ptr cats_i15(tll_ptr s1_v4121, tll_ptr s2_v4122);
tll_ptr strlen_i16(tll_ptr s_v4128);
tll_ptr lenUU_i39(tll_ptr A_v4132, tll_ptr xs_v4133);
tll_ptr lenUL_i38(tll_ptr A_v4141, tll_ptr xs_v4142);
tll_ptr lenLL_i36(tll_ptr A_v4150, tll_ptr xs_v4151);
tll_ptr appendUU_i43(tll_ptr A_v4159, tll_ptr xs_v4160, tll_ptr ys_v4161);
tll_ptr appendUL_i42(tll_ptr A_v4170, tll_ptr xs_v4171, tll_ptr ys_v4172);
tll_ptr appendLL_i40(tll_ptr A_v4181, tll_ptr xs_v4182, tll_ptr ys_v4183);
tll_ptr readline_i25(tll_ptr __v4192);
tll_ptr print_i26(tll_ptr s_v4216);
tll_ptr prerr_i27(tll_ptr s_v4229);
tll_ptr ref_handler_i30(tll_ptr A_v4242, tll_ptr m_v4243, tll_ptr c0_v4244);
tll_ptr mk_ref_i31(tll_ptr A_v4293, tll_ptr m_v4294);
tll_ptr set_ref_i32(tll_ptr A_v4301, tll_ptr m_v4302, tll_ptr r_v4303);
tll_ptr get_ref_i33(tll_ptr A_v4313, tll_ptr r_v4314);
tll_ptr free_ref_i34(tll_ptr A_v4321, tll_ptr r_v4322);

tll_ptr addnclo_i53;
tll_ptr andbclo_i44;
tll_ptr appendLLclo_i65;
tll_ptr appendULclo_i64;
tll_ptr appendUUclo_i63;
tll_ptr catsclo_i58;
tll_ptr divnclo_i56;
tll_ptr eqnclo_i51;
tll_ptr free_refclo_i73;
tll_ptr get_refclo_i72;
tll_ptr gtenclo_i48;
tll_ptr gtnclo_i50;
tll_ptr lenLLclo_i62;
tll_ptr lenULclo_i61;
tll_ptr lenUUclo_i60;
tll_ptr ltenclo_i47;
tll_ptr ltnclo_i49;
tll_ptr mk_refclo_i70;
tll_ptr modnclo_i57;
tll_ptr mulnclo_i55;
tll_ptr notbclo_i46;
tll_ptr orbclo_i45;
tll_ptr predclo_i52;
tll_ptr prerrclo_i68;
tll_ptr printclo_i67;
tll_ptr readlineclo_i66;
tll_ptr ref_handlerclo_i69;
tll_ptr set_refclo_i71;
tll_ptr strlenclo_i59;
tll_ptr subnclo_i54;

tll_ptr andb_i1(tll_ptr b1_v4040, tll_ptr b2_v4041)
{
  tll_ptr false_t2; tll_ptr switch_ret_t1;
  switch(((tll_node)b1_v4040)->tag) {
    case 2:
      switch_ret_t1 = b2_v4041;
      break;
    case 3:
      instr_struct(&false_t2, 3, 0);
      switch_ret_t1 = false_t2;
      break;
  }
  return switch_ret_t1;
}

tll_ptr lam_fun_t4(tll_ptr b2_v4044, tll_env env)
{
  tll_ptr call_ret_t3;
  call_ret_t3 = andb_i1(env[0], b2_v4044);
  return call_ret_t3;
}

tll_ptr lam_fun_t6(tll_ptr b1_v4042, tll_env env)
{
  tll_ptr lam_clo_t5;
  instr_clo(&lam_clo_t5, &lam_fun_t4, 1, b1_v4042);
  return lam_clo_t5;
}

tll_ptr orb_i2(tll_ptr b1_v4045, tll_ptr b2_v4046)
{
  tll_ptr switch_ret_t8; tll_ptr true_t9;
  switch(((tll_node)b1_v4045)->tag) {
    case 2:
      instr_struct(&true_t9, 2, 0);
      switch_ret_t8 = true_t9;
      break;
    case 3:
      switch_ret_t8 = b2_v4046;
      break;
  }
  return switch_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b2_v4049, tll_env env)
{
  tll_ptr call_ret_t10;
  call_ret_t10 = orb_i2(env[0], b2_v4049);
  return call_ret_t10;
}

tll_ptr lam_fun_t13(tll_ptr b1_v4047, tll_env env)
{
  tll_ptr lam_clo_t12;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 1, b1_v4047);
  return lam_clo_t12;
}

tll_ptr notb_i3(tll_ptr b_v4050)
{
  tll_ptr false_t16; tll_ptr switch_ret_t15; tll_ptr true_t17;
  switch(((tll_node)b_v4050)->tag) {
    case 2:
      instr_struct(&false_t16, 3, 0);
      switch_ret_t15 = false_t16;
      break;
    case 3:
      instr_struct(&true_t17, 2, 0);
      switch_ret_t15 = true_t17;
      break;
  }
  return switch_ret_t15;
}

tll_ptr lam_fun_t19(tll_ptr b_v4051, tll_env env)
{
  tll_ptr call_ret_t18;
  call_ret_t18 = notb_i3(b_v4051);
  return call_ret_t18;
}

tll_ptr lten_i4(tll_ptr x_v4052, tll_ptr y_v4053)
{
  tll_ptr call_ret_t25; tll_ptr false_t24; tll_ptr switch_ret_t21;
  tll_ptr switch_ret_t23; tll_ptr true_t22; tll_ptr x_v4054; tll_ptr y_v4055;
  switch(((tll_node)x_v4052)->tag) {
    case 4:
      instr_struct(&true_t22, 2, 0);
      switch_ret_t21 = true_t22;
      break;
    case 5:
      x_v4054 = ((tll_node)x_v4052)->data[0];
      switch(((tll_node)y_v4053)->tag) {
        case 4:
          instr_struct(&false_t24, 3, 0);
          switch_ret_t23 = false_t24;
          break;
        case 5:
          y_v4055 = ((tll_node)y_v4053)->data[0];
          call_ret_t25 = lten_i4(x_v4054, y_v4055);
          switch_ret_t23 = call_ret_t25;
          break;
      }
      switch_ret_t21 = switch_ret_t23;
      break;
  }
  return switch_ret_t21;
}

tll_ptr lam_fun_t27(tll_ptr y_v4058, tll_env env)
{
  tll_ptr call_ret_t26;
  call_ret_t26 = lten_i4(env[0], y_v4058);
  return call_ret_t26;
}

tll_ptr lam_fun_t29(tll_ptr x_v4056, tll_env env)
{
  tll_ptr lam_clo_t28;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 1, x_v4056);
  return lam_clo_t28;
}

tll_ptr gten_i5(tll_ptr x_v4059, tll_ptr y_v4060)
{
  tll_ptr __v4061; tll_ptr call_ret_t37; tll_ptr false_t34;
  tll_ptr switch_ret_t31; tll_ptr switch_ret_t32; tll_ptr switch_ret_t35;
  tll_ptr true_t33; tll_ptr true_t36; tll_ptr x_v4062; tll_ptr y_v4063;
  switch(((tll_node)x_v4059)->tag) {
    case 4:
      switch(((tll_node)y_v4060)->tag) {
        case 4:
          instr_struct(&true_t33, 2, 0);
          switch_ret_t32 = true_t33;
          break;
        case 5:
          __v4061 = ((tll_node)y_v4060)->data[0];
          instr_struct(&false_t34, 3, 0);
          switch_ret_t32 = false_t34;
          break;
      }
      switch_ret_t31 = switch_ret_t32;
      break;
    case 5:
      x_v4062 = ((tll_node)x_v4059)->data[0];
      switch(((tll_node)y_v4060)->tag) {
        case 4:
          instr_struct(&true_t36, 2, 0);
          switch_ret_t35 = true_t36;
          break;
        case 5:
          y_v4063 = ((tll_node)y_v4060)->data[0];
          call_ret_t37 = gten_i5(x_v4062, y_v4063);
          switch_ret_t35 = call_ret_t37;
          break;
      }
      switch_ret_t31 = switch_ret_t35;
      break;
  }
  return switch_ret_t31;
}

tll_ptr lam_fun_t39(tll_ptr y_v4066, tll_env env)
{
  tll_ptr call_ret_t38;
  call_ret_t38 = gten_i5(env[0], y_v4066);
  return call_ret_t38;
}

tll_ptr lam_fun_t41(tll_ptr x_v4064, tll_env env)
{
  tll_ptr lam_clo_t40;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 1, x_v4064);
  return lam_clo_t40;
}

tll_ptr ltn_i6(tll_ptr x_v4067, tll_ptr y_v4068)
{
  tll_ptr call_ret_t49; tll_ptr false_t45; tll_ptr false_t48;
  tll_ptr switch_ret_t43; tll_ptr switch_ret_t44; tll_ptr switch_ret_t47;
  tll_ptr true_t46; tll_ptr x_v4070; tll_ptr y_v4069; tll_ptr y_v4071;
  switch(((tll_node)x_v4067)->tag) {
    case 4:
      switch(((tll_node)y_v4068)->tag) {
        case 4:
          instr_struct(&false_t45, 3, 0);
          switch_ret_t44 = false_t45;
          break;
        case 5:
          y_v4069 = ((tll_node)y_v4068)->data[0];
          instr_struct(&true_t46, 2, 0);
          switch_ret_t44 = true_t46;
          break;
      }
      switch_ret_t43 = switch_ret_t44;
      break;
    case 5:
      x_v4070 = ((tll_node)x_v4067)->data[0];
      switch(((tll_node)y_v4068)->tag) {
        case 4:
          instr_struct(&false_t48, 3, 0);
          switch_ret_t47 = false_t48;
          break;
        case 5:
          y_v4071 = ((tll_node)y_v4068)->data[0];
          call_ret_t49 = ltn_i6(x_v4070, y_v4071);
          switch_ret_t47 = call_ret_t49;
          break;
      }
      switch_ret_t43 = switch_ret_t47;
      break;
  }
  return switch_ret_t43;
}

tll_ptr lam_fun_t51(tll_ptr y_v4074, tll_env env)
{
  tll_ptr call_ret_t50;
  call_ret_t50 = ltn_i6(env[0], y_v4074);
  return call_ret_t50;
}

tll_ptr lam_fun_t53(tll_ptr x_v4072, tll_env env)
{
  tll_ptr lam_clo_t52;
  instr_clo(&lam_clo_t52, &lam_fun_t51, 1, x_v4072);
  return lam_clo_t52;
}

tll_ptr gtn_i7(tll_ptr x_v4075, tll_ptr y_v4076)
{
  tll_ptr call_ret_t59; tll_ptr false_t56; tll_ptr switch_ret_t55;
  tll_ptr switch_ret_t57; tll_ptr true_t58; tll_ptr x_v4077; tll_ptr y_v4078;
  switch(((tll_node)x_v4075)->tag) {
    case 4:
      instr_struct(&false_t56, 3, 0);
      switch_ret_t55 = false_t56;
      break;
    case 5:
      x_v4077 = ((tll_node)x_v4075)->data[0];
      switch(((tll_node)y_v4076)->tag) {
        case 4:
          instr_struct(&true_t58, 2, 0);
          switch_ret_t57 = true_t58;
          break;
        case 5:
          y_v4078 = ((tll_node)y_v4076)->data[0];
          call_ret_t59 = gtn_i7(x_v4077, y_v4078);
          switch_ret_t57 = call_ret_t59;
          break;
      }
      switch_ret_t55 = switch_ret_t57;
      break;
  }
  return switch_ret_t55;
}

tll_ptr lam_fun_t61(tll_ptr y_v4081, tll_env env)
{
  tll_ptr call_ret_t60;
  call_ret_t60 = gtn_i7(env[0], y_v4081);
  return call_ret_t60;
}

tll_ptr lam_fun_t63(tll_ptr x_v4079, tll_env env)
{
  tll_ptr lam_clo_t62;
  instr_clo(&lam_clo_t62, &lam_fun_t61, 1, x_v4079);
  return lam_clo_t62;
}

tll_ptr eqn_i8(tll_ptr x_v4082, tll_ptr y_v4083)
{
  tll_ptr __v4084; tll_ptr call_ret_t71; tll_ptr false_t68;
  tll_ptr false_t70; tll_ptr switch_ret_t65; tll_ptr switch_ret_t66;
  tll_ptr switch_ret_t69; tll_ptr true_t67; tll_ptr x_v4085; tll_ptr y_v4086;
  switch(((tll_node)x_v4082)->tag) {
    case 4:
      switch(((tll_node)y_v4083)->tag) {
        case 4:
          instr_struct(&true_t67, 2, 0);
          switch_ret_t66 = true_t67;
          break;
        case 5:
          __v4084 = ((tll_node)y_v4083)->data[0];
          instr_struct(&false_t68, 3, 0);
          switch_ret_t66 = false_t68;
          break;
      }
      switch_ret_t65 = switch_ret_t66;
      break;
    case 5:
      x_v4085 = ((tll_node)x_v4082)->data[0];
      switch(((tll_node)y_v4083)->tag) {
        case 4:
          instr_struct(&false_t70, 3, 0);
          switch_ret_t69 = false_t70;
          break;
        case 5:
          y_v4086 = ((tll_node)y_v4083)->data[0];
          call_ret_t71 = eqn_i8(x_v4085, y_v4086);
          switch_ret_t69 = call_ret_t71;
          break;
      }
      switch_ret_t65 = switch_ret_t69;
      break;
  }
  return switch_ret_t65;
}

tll_ptr lam_fun_t73(tll_ptr y_v4089, tll_env env)
{
  tll_ptr call_ret_t72;
  call_ret_t72 = eqn_i8(env[0], y_v4089);
  return call_ret_t72;
}

tll_ptr lam_fun_t75(tll_ptr x_v4087, tll_env env)
{
  tll_ptr lam_clo_t74;
  instr_clo(&lam_clo_t74, &lam_fun_t73, 1, x_v4087);
  return lam_clo_t74;
}

tll_ptr pred_i9(tll_ptr x_v4090)
{
  tll_ptr O_t78; tll_ptr switch_ret_t77; tll_ptr x_v4091;
  switch(((tll_node)x_v4090)->tag) {
    case 4:
      instr_struct(&O_t78, 4, 0);
      switch_ret_t77 = O_t78;
      break;
    case 5:
      x_v4091 = ((tll_node)x_v4090)->data[0];
      switch_ret_t77 = x_v4091;
      break;
  }
  return switch_ret_t77;
}

tll_ptr lam_fun_t80(tll_ptr x_v4092, tll_env env)
{
  tll_ptr call_ret_t79;
  call_ret_t79 = pred_i9(x_v4092);
  return call_ret_t79;
}

tll_ptr addn_i10(tll_ptr x_v4093, tll_ptr y_v4094)
{
  tll_ptr S_t84; tll_ptr call_ret_t83; tll_ptr switch_ret_t82;
  tll_ptr x_v4095;
  switch(((tll_node)x_v4093)->tag) {
    case 4:
      switch_ret_t82 = y_v4094;
      break;
    case 5:
      x_v4095 = ((tll_node)x_v4093)->data[0];
      call_ret_t83 = addn_i10(x_v4095, y_v4094);
      instr_struct(&S_t84, 5, 1, call_ret_t83);
      switch_ret_t82 = S_t84;
      break;
  }
  return switch_ret_t82;
}

tll_ptr lam_fun_t86(tll_ptr y_v4098, tll_env env)
{
  tll_ptr call_ret_t85;
  call_ret_t85 = addn_i10(env[0], y_v4098);
  return call_ret_t85;
}

tll_ptr lam_fun_t88(tll_ptr x_v4096, tll_env env)
{
  tll_ptr lam_clo_t87;
  instr_clo(&lam_clo_t87, &lam_fun_t86, 1, x_v4096);
  return lam_clo_t87;
}

tll_ptr subn_i11(tll_ptr x_v4099, tll_ptr y_v4100)
{
  tll_ptr call_ret_t91; tll_ptr call_ret_t92; tll_ptr switch_ret_t90;
  tll_ptr y_v4101;
  switch(((tll_node)y_v4100)->tag) {
    case 4:
      switch_ret_t90 = x_v4099;
      break;
    case 5:
      y_v4101 = ((tll_node)y_v4100)->data[0];
      call_ret_t92 = pred_i9(x_v4099);
      call_ret_t91 = subn_i11(call_ret_t92, y_v4101);
      switch_ret_t90 = call_ret_t91;
      break;
  }
  return switch_ret_t90;
}

tll_ptr lam_fun_t94(tll_ptr y_v4104, tll_env env)
{
  tll_ptr call_ret_t93;
  call_ret_t93 = subn_i11(env[0], y_v4104);
  return call_ret_t93;
}

tll_ptr lam_fun_t96(tll_ptr x_v4102, tll_env env)
{
  tll_ptr lam_clo_t95;
  instr_clo(&lam_clo_t95, &lam_fun_t94, 1, x_v4102);
  return lam_clo_t95;
}

tll_ptr muln_i12(tll_ptr x_v4105, tll_ptr y_v4106)
{
  tll_ptr O_t99; tll_ptr call_ret_t100; tll_ptr call_ret_t101;
  tll_ptr switch_ret_t98; tll_ptr x_v4107;
  switch(((tll_node)x_v4105)->tag) {
    case 4:
      instr_struct(&O_t99, 4, 0);
      switch_ret_t98 = O_t99;
      break;
    case 5:
      x_v4107 = ((tll_node)x_v4105)->data[0];
      call_ret_t101 = muln_i12(x_v4107, y_v4106);
      call_ret_t100 = addn_i10(y_v4106, call_ret_t101);
      switch_ret_t98 = call_ret_t100;
      break;
  }
  return switch_ret_t98;
}

tll_ptr lam_fun_t103(tll_ptr y_v4110, tll_env env)
{
  tll_ptr call_ret_t102;
  call_ret_t102 = muln_i12(env[0], y_v4110);
  return call_ret_t102;
}

tll_ptr lam_fun_t105(tll_ptr x_v4108, tll_env env)
{
  tll_ptr lam_clo_t104;
  instr_clo(&lam_clo_t104, &lam_fun_t103, 1, x_v4108);
  return lam_clo_t104;
}

tll_ptr divn_i13(tll_ptr x_v4111, tll_ptr y_v4112)
{
  tll_ptr O_t109; tll_ptr S_t112; tll_ptr call_ret_t107;
  tll_ptr call_ret_t110; tll_ptr call_ret_t111; tll_ptr switch_ret_t108;
  call_ret_t107 = ltn_i6(x_v4111, y_v4112);
  switch(((tll_node)call_ret_t107)->tag) {
    case 2:
      instr_struct(&O_t109, 4, 0);
      switch_ret_t108 = O_t109;
      break;
    case 3:
      call_ret_t111 = subn_i11(x_v4111, y_v4112);
      call_ret_t110 = divn_i13(call_ret_t111, y_v4112);
      instr_struct(&S_t112, 5, 1, call_ret_t110);
      switch_ret_t108 = S_t112;
      break;
  }
  return switch_ret_t108;
}

tll_ptr lam_fun_t114(tll_ptr y_v4115, tll_env env)
{
  tll_ptr call_ret_t113;
  call_ret_t113 = divn_i13(env[0], y_v4115);
  return call_ret_t113;
}

tll_ptr lam_fun_t116(tll_ptr x_v4113, tll_env env)
{
  tll_ptr lam_clo_t115;
  instr_clo(&lam_clo_t115, &lam_fun_t114, 1, x_v4113);
  return lam_clo_t115;
}

tll_ptr modn_i14(tll_ptr x_v4116, tll_ptr y_v4117)
{
  tll_ptr call_ret_t118; tll_ptr call_ret_t119; tll_ptr call_ret_t120;
  call_ret_t120 = divn_i13(x_v4116, y_v4117);
  call_ret_t119 = muln_i12(call_ret_t120, y_v4117);
  call_ret_t118 = subn_i11(x_v4116, call_ret_t119);
  return call_ret_t118;
}

tll_ptr lam_fun_t122(tll_ptr y_v4120, tll_env env)
{
  tll_ptr call_ret_t121;
  call_ret_t121 = modn_i14(env[0], y_v4120);
  return call_ret_t121;
}

tll_ptr lam_fun_t124(tll_ptr x_v4118, tll_env env)
{
  tll_ptr lam_clo_t123;
  instr_clo(&lam_clo_t123, &lam_fun_t122, 1, x_v4118);
  return lam_clo_t123;
}

tll_ptr cats_i15(tll_ptr s1_v4121, tll_ptr s2_v4122)
{
  tll_ptr String_t128; tll_ptr c_v4123; tll_ptr call_ret_t127;
  tll_ptr s1_v4124; tll_ptr switch_ret_t126;
  switch(((tll_node)s1_v4121)->tag) {
    case 7:
      switch_ret_t126 = s2_v4122;
      break;
    case 8:
      c_v4123 = ((tll_node)s1_v4121)->data[0];
      s1_v4124 = ((tll_node)s1_v4121)->data[1];
      call_ret_t127 = cats_i15(s1_v4124, s2_v4122);
      instr_struct(&String_t128, 8, 2, c_v4123, call_ret_t127);
      switch_ret_t126 = String_t128;
      break;
  }
  return switch_ret_t126;
}

tll_ptr lam_fun_t130(tll_ptr s2_v4127, tll_env env)
{
  tll_ptr call_ret_t129;
  call_ret_t129 = cats_i15(env[0], s2_v4127);
  return call_ret_t129;
}

tll_ptr lam_fun_t132(tll_ptr s1_v4125, tll_env env)
{
  tll_ptr lam_clo_t131;
  instr_clo(&lam_clo_t131, &lam_fun_t130, 1, s1_v4125);
  return lam_clo_t131;
}

tll_ptr strlen_i16(tll_ptr s_v4128)
{
  tll_ptr O_t135; tll_ptr S_t137; tll_ptr __v4129; tll_ptr call_ret_t136;
  tll_ptr s_v4130; tll_ptr switch_ret_t134;
  switch(((tll_node)s_v4128)->tag) {
    case 7:
      instr_struct(&O_t135, 4, 0);
      switch_ret_t134 = O_t135;
      break;
    case 8:
      __v4129 = ((tll_node)s_v4128)->data[0];
      s_v4130 = ((tll_node)s_v4128)->data[1];
      call_ret_t136 = strlen_i16(s_v4130);
      instr_struct(&S_t137, 5, 1, call_ret_t136);
      switch_ret_t134 = S_t137;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t139(tll_ptr s_v4131, tll_env env)
{
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i16(s_v4131);
  return call_ret_t138;
}

tll_ptr lenUU_i39(tll_ptr A_v4132, tll_ptr xs_v4133)
{
  tll_ptr O_t142; tll_ptr S_t147; tll_ptr call_ret_t145; tll_ptr consUU_t148;
  tll_ptr n_v4136; tll_ptr nilUU_t143; tll_ptr pair_struct_t144;
  tll_ptr pair_struct_t149; tll_ptr switch_ret_t141; tll_ptr switch_ret_t146;
  tll_ptr x_v4134; tll_ptr xs_v4135; tll_ptr xs_v4137;
  switch(((tll_node)xs_v4133)->tag) {
    case 20:
      instr_struct(&O_t142, 4, 0);
      instr_struct(&nilUU_t143, 20, 0);
      instr_struct(&pair_struct_t144, 0, 2, O_t142, nilUU_t143);
      switch_ret_t141 = pair_struct_t144;
      break;
    case 21:
      x_v4134 = ((tll_node)xs_v4133)->data[0];
      xs_v4135 = ((tll_node)xs_v4133)->data[1];
      call_ret_t145 = lenUU_i39(0, xs_v4135);
      switch(((tll_node)call_ret_t145)->tag) {
        case 0:
          n_v4136 = ((tll_node)call_ret_t145)->data[0];
          xs_v4137 = ((tll_node)call_ret_t145)->data[1];
          instr_free_struct(call_ret_t145);
          instr_struct(&S_t147, 5, 1, n_v4136);
          instr_struct(&consUU_t148, 21, 2, x_v4134, xs_v4137);
          instr_struct(&pair_struct_t149, 0, 2, S_t147, consUU_t148);
          switch_ret_t146 = pair_struct_t149;
          break;
      }
      switch_ret_t141 = switch_ret_t146;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t151(tll_ptr xs_v4140, tll_env env)
{
  tll_ptr call_ret_t150;
  call_ret_t150 = lenUU_i39(env[0], xs_v4140);
  return call_ret_t150;
}

tll_ptr lam_fun_t153(tll_ptr A_v4138, tll_env env)
{
  tll_ptr lam_clo_t152;
  instr_clo(&lam_clo_t152, &lam_fun_t151, 1, A_v4138);
  return lam_clo_t152;
}

tll_ptr lenUL_i38(tll_ptr A_v4141, tll_ptr xs_v4142)
{
  tll_ptr O_t156; tll_ptr S_t161; tll_ptr call_ret_t159; tll_ptr consUL_t162;
  tll_ptr n_v4145; tll_ptr nilUL_t157; tll_ptr pair_struct_t158;
  tll_ptr pair_struct_t163; tll_ptr switch_ret_t155; tll_ptr switch_ret_t160;
  tll_ptr x_v4143; tll_ptr xs_v4144; tll_ptr xs_v4146;
  switch(((tll_node)xs_v4142)->tag) {
    case 18:
      instr_free_struct(xs_v4142);
      instr_struct(&O_t156, 4, 0);
      instr_struct(&nilUL_t157, 18, 0);
      instr_struct(&pair_struct_t158, 0, 2, O_t156, nilUL_t157);
      switch_ret_t155 = pair_struct_t158;
      break;
    case 19:
      x_v4143 = ((tll_node)xs_v4142)->data[0];
      xs_v4144 = ((tll_node)xs_v4142)->data[1];
      instr_free_struct(xs_v4142);
      call_ret_t159 = lenUL_i38(0, xs_v4144);
      switch(((tll_node)call_ret_t159)->tag) {
        case 0:
          n_v4145 = ((tll_node)call_ret_t159)->data[0];
          xs_v4146 = ((tll_node)call_ret_t159)->data[1];
          instr_free_struct(call_ret_t159);
          instr_struct(&S_t161, 5, 1, n_v4145);
          instr_struct(&consUL_t162, 19, 2, x_v4143, xs_v4146);
          instr_struct(&pair_struct_t163, 0, 2, S_t161, consUL_t162);
          switch_ret_t160 = pair_struct_t163;
          break;
      }
      switch_ret_t155 = switch_ret_t160;
      break;
  }
  return switch_ret_t155;
}

tll_ptr lam_fun_t165(tll_ptr xs_v4149, tll_env env)
{
  tll_ptr call_ret_t164;
  call_ret_t164 = lenUL_i38(env[0], xs_v4149);
  return call_ret_t164;
}

tll_ptr lam_fun_t167(tll_ptr A_v4147, tll_env env)
{
  tll_ptr lam_clo_t166;
  instr_clo(&lam_clo_t166, &lam_fun_t165, 1, A_v4147);
  return lam_clo_t166;
}

tll_ptr lenLL_i36(tll_ptr A_v4150, tll_ptr xs_v4151)
{
  tll_ptr O_t170; tll_ptr S_t175; tll_ptr call_ret_t173; tll_ptr consLL_t176;
  tll_ptr n_v4154; tll_ptr nilLL_t171; tll_ptr pair_struct_t172;
  tll_ptr pair_struct_t177; tll_ptr switch_ret_t169; tll_ptr switch_ret_t174;
  tll_ptr x_v4152; tll_ptr xs_v4153; tll_ptr xs_v4155;
  switch(((tll_node)xs_v4151)->tag) {
    case 14:
      instr_free_struct(xs_v4151);
      instr_struct(&O_t170, 4, 0);
      instr_struct(&nilLL_t171, 14, 0);
      instr_struct(&pair_struct_t172, 0, 2, O_t170, nilLL_t171);
      switch_ret_t169 = pair_struct_t172;
      break;
    case 15:
      x_v4152 = ((tll_node)xs_v4151)->data[0];
      xs_v4153 = ((tll_node)xs_v4151)->data[1];
      instr_free_struct(xs_v4151);
      call_ret_t173 = lenLL_i36(0, xs_v4153);
      switch(((tll_node)call_ret_t173)->tag) {
        case 0:
          n_v4154 = ((tll_node)call_ret_t173)->data[0];
          xs_v4155 = ((tll_node)call_ret_t173)->data[1];
          instr_free_struct(call_ret_t173);
          instr_struct(&S_t175, 5, 1, n_v4154);
          instr_struct(&consLL_t176, 15, 2, x_v4152, xs_v4155);
          instr_struct(&pair_struct_t177, 0, 2, S_t175, consLL_t176);
          switch_ret_t174 = pair_struct_t177;
          break;
      }
      switch_ret_t169 = switch_ret_t174;
      break;
  }
  return switch_ret_t169;
}

tll_ptr lam_fun_t179(tll_ptr xs_v4158, tll_env env)
{
  tll_ptr call_ret_t178;
  call_ret_t178 = lenLL_i36(env[0], xs_v4158);
  return call_ret_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v4156, tll_env env)
{
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v4156);
  return lam_clo_t180;
}

tll_ptr appendUU_i43(tll_ptr A_v4159, tll_ptr xs_v4160, tll_ptr ys_v4161)
{
  tll_ptr call_ret_t184; tll_ptr consUU_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v4162; tll_ptr xs_v4163;
  switch(((tll_node)xs_v4160)->tag) {
    case 20:
      switch_ret_t183 = ys_v4161;
      break;
    case 21:
      x_v4162 = ((tll_node)xs_v4160)->data[0];
      xs_v4163 = ((tll_node)xs_v4160)->data[1];
      call_ret_t184 = appendUU_i43(0, xs_v4163, ys_v4161);
      instr_struct(&consUU_t185, 21, 2, x_v4162, call_ret_t184);
      switch_ret_t183 = consUU_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v4169, tll_env env)
{
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUU_i43(env[1], env[0], ys_v4169);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v4167, tll_env env)
{
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v4167, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v4164, tll_env env)
{
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v4164);
  return lam_clo_t190;
}

tll_ptr appendUL_i42(tll_ptr A_v4170, tll_ptr xs_v4171, tll_ptr ys_v4172)
{
  tll_ptr call_ret_t194; tll_ptr consUL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v4173; tll_ptr xs_v4174;
  switch(((tll_node)xs_v4171)->tag) {
    case 18:
      instr_free_struct(xs_v4171);
      switch_ret_t193 = ys_v4172;
      break;
    case 19:
      x_v4173 = ((tll_node)xs_v4171)->data[0];
      xs_v4174 = ((tll_node)xs_v4171)->data[1];
      instr_free_struct(xs_v4171);
      call_ret_t194 = appendUL_i42(0, xs_v4174, ys_v4172);
      instr_struct(&consUL_t195, 19, 2, x_v4173, call_ret_t194);
      switch_ret_t193 = consUL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v4180, tll_env env)
{
  tll_ptr call_ret_t196;
  call_ret_t196 = appendUL_i42(env[1], env[0], ys_v4180);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v4178, tll_env env)
{
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v4178, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v4175, tll_env env)
{
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v4175);
  return lam_clo_t200;
}

tll_ptr appendLL_i40(tll_ptr A_v4181, tll_ptr xs_v4182, tll_ptr ys_v4183)
{
  tll_ptr call_ret_t204; tll_ptr consLL_t205; tll_ptr switch_ret_t203;
  tll_ptr x_v4184; tll_ptr xs_v4185;
  switch(((tll_node)xs_v4182)->tag) {
    case 14:
      instr_free_struct(xs_v4182);
      switch_ret_t203 = ys_v4183;
      break;
    case 15:
      x_v4184 = ((tll_node)xs_v4182)->data[0];
      xs_v4185 = ((tll_node)xs_v4182)->data[1];
      instr_free_struct(xs_v4182);
      call_ret_t204 = appendLL_i40(0, xs_v4185, ys_v4183);
      instr_struct(&consLL_t205, 15, 2, x_v4184, call_ret_t204);
      switch_ret_t203 = consLL_t205;
      break;
  }
  return switch_ret_t203;
}

tll_ptr lam_fun_t207(tll_ptr ys_v4191, tll_env env)
{
  tll_ptr call_ret_t206;
  call_ret_t206 = appendLL_i40(env[1], env[0], ys_v4191);
  return call_ret_t206;
}

tll_ptr lam_fun_t209(tll_ptr xs_v4189, tll_env env)
{
  tll_ptr lam_clo_t208;
  instr_clo(&lam_clo_t208, &lam_fun_t207, 2, xs_v4189, env[0]);
  return lam_clo_t208;
}

tll_ptr lam_fun_t211(tll_ptr A_v4186, tll_env env)
{
  tll_ptr lam_clo_t210;
  instr_clo(&lam_clo_t210, &lam_fun_t209, 1, A_v4186);
  return lam_clo_t210;
}

tll_ptr lam_fun_t221(tll_ptr __v4208, tll_env env)
{
  tll_ptr __v4213; tll_ptr __v4214; tll_ptr ch_v4212; tll_ptr false_t219;
  tll_ptr send_ch_t218; tll_ptr tt_t220;
  instr_struct(&false_t219, 3, 0);
  instr_send(&send_ch_t218, env[0], false_t219);
  ch_v4212 = send_ch_t218;
  __v4214 = ch_v4212;
  instr_struct(&tt_t220, 1, 0);
  __v4213 = tt_t220;
  return env[1];
}

tll_ptr lam_fun_t224(tll_ptr __v4193, tll_env env)
{
  tll_ptr __v4205; tll_ptr app_ret_t223; tll_ptr ch_v4203; tll_ptr ch_v4204;
  tll_ptr ch_v4207; tll_ptr lam_clo_t222; tll_ptr prim_ch_t213;
  tll_ptr recv_msg_t216; tll_ptr s_v4206; tll_ptr send_ch_t214;
  tll_ptr switch_ret_t217; tll_ptr true_t215;
  instr_open(&prim_ch_t213, &proc_stdin);
  ch_v4203 = prim_ch_t213;
  instr_struct(&true_t215, 2, 0);
  instr_send(&send_ch_t214, ch_v4203, true_t215);
  ch_v4204 = send_ch_t214;
  instr_recv(&recv_msg_t216, ch_v4204);
  __v4205 = recv_msg_t216;
  switch(((tll_node)__v4205)->tag) {
    case 0:
      s_v4206 = ((tll_node)__v4205)->data[0];
      ch_v4207 = ((tll_node)__v4205)->data[1];
      instr_free_struct(__v4205);
      instr_clo(&lam_clo_t222, &lam_fun_t221, 2, ch_v4207, s_v4206);
      switch_ret_t217 = lam_clo_t222;
      break;
  }
  instr_app(&app_ret_t223, switch_ret_t217, 0);
  instr_free_clo(switch_ret_t217);
  return app_ret_t223;
}

tll_ptr readline_i25(tll_ptr __v4192)
{
  tll_ptr lam_clo_t225;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 0);
  return lam_clo_t225;
}

tll_ptr lam_fun_t227(tll_ptr __v4215, tll_env env)
{
  tll_ptr call_ret_t226;
  call_ret_t226 = readline_i25(__v4215);
  return call_ret_t226;
}

tll_ptr lam_fun_t236(tll_ptr __v4217, tll_env env)
{
  tll_ptr __v4227; tll_ptr ch_v4223; tll_ptr ch_v4224; tll_ptr ch_v4225;
  tll_ptr ch_v4226; tll_ptr false_t234; tll_ptr prim_ch_t229;
  tll_ptr send_ch_t230; tll_ptr send_ch_t232; tll_ptr send_ch_t233;
  tll_ptr true_t231; tll_ptr tt_t235;
  instr_open(&prim_ch_t229, &proc_stdout);
  ch_v4223 = prim_ch_t229;
  instr_struct(&true_t231, 2, 0);
  instr_send(&send_ch_t230, ch_v4223, true_t231);
  ch_v4224 = send_ch_t230;
  instr_send(&send_ch_t232, ch_v4224, env[0]);
  ch_v4225 = send_ch_t232;
  instr_struct(&false_t234, 3, 0);
  instr_send(&send_ch_t233, ch_v4225, false_t234);
  ch_v4226 = send_ch_t233;
  __v4227 = ch_v4226;
  instr_struct(&tt_t235, 1, 0);
  return tt_t235;
}

tll_ptr print_i26(tll_ptr s_v4216)
{
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, s_v4216);
  return lam_clo_t237;
}

tll_ptr lam_fun_t239(tll_ptr s_v4228, tll_env env)
{
  tll_ptr call_ret_t238;
  call_ret_t238 = print_i26(s_v4228);
  return call_ret_t238;
}

tll_ptr lam_fun_t248(tll_ptr __v4230, tll_env env)
{
  tll_ptr __v4240; tll_ptr ch_v4236; tll_ptr ch_v4237; tll_ptr ch_v4238;
  tll_ptr ch_v4239; tll_ptr false_t246; tll_ptr prim_ch_t241;
  tll_ptr send_ch_t242; tll_ptr send_ch_t244; tll_ptr send_ch_t245;
  tll_ptr true_t243; tll_ptr tt_t247;
  instr_open(&prim_ch_t241, &proc_stderr);
  ch_v4236 = prim_ch_t241;
  instr_struct(&true_t243, 2, 0);
  instr_send(&send_ch_t242, ch_v4236, true_t243);
  ch_v4237 = send_ch_t242;
  instr_send(&send_ch_t244, ch_v4237, env[0]);
  ch_v4238 = send_ch_t244;
  instr_struct(&false_t246, 3, 0);
  instr_send(&send_ch_t245, ch_v4238, false_t246);
  ch_v4239 = send_ch_t245;
  __v4240 = ch_v4239;
  instr_struct(&tt_t247, 1, 0);
  return tt_t247;
}

tll_ptr prerr_i27(tll_ptr s_v4229)
{
  tll_ptr lam_clo_t249;
  instr_clo(&lam_clo_t249, &lam_fun_t248, 1, s_v4229);
  return lam_clo_t249;
}

tll_ptr lam_fun_t251(tll_ptr s_v4241, tll_env env)
{
  tll_ptr call_ret_t250;
  call_ret_t250 = prerr_i27(s_v4241);
  return call_ret_t250;
}

tll_ptr lam_fun_t259(tll_ptr __v4266, tll_env env)
{
  tll_ptr app_ret_t258; tll_ptr c_v4268; tll_ptr call_ret_t257;
  tll_ptr send_ch_t256;
  instr_send(&send_ch_t256, env[0], env[1]);
  c_v4268 = send_ch_t256;
  call_ret_t257 = ref_handler_i30(0, env[1], c_v4268);
  instr_app(&app_ret_t258, call_ret_t257, 0);
  instr_free_clo(call_ret_t257);
  return app_ret_t258;
}

tll_ptr lam_fun_t261(tll_ptr c_v4263, tll_env env)
{
  tll_ptr lam_clo_t260;
  instr_clo(&lam_clo_t260, &lam_fun_t259, 2, c_v4263, env[0]);
  return lam_clo_t260;
}

tll_ptr lam_fun_t267(tll_ptr __v4274, tll_env env)
{
  tll_ptr __v4278; tll_ptr app_ret_t266; tll_ptr c_v4280;
  tll_ptr call_ret_t265; tll_ptr m_v4279; tll_ptr recv_msg_t263;
  tll_ptr switch_ret_t264;
  instr_recv(&recv_msg_t263, env[0]);
  __v4278 = recv_msg_t263;
  switch(((tll_node)__v4278)->tag) {
    case 0:
      m_v4279 = ((tll_node)__v4278)->data[0];
      c_v4280 = ((tll_node)__v4278)->data[1];
      instr_free_struct(__v4278);
      call_ret_t265 = ref_handler_i30(0, m_v4279, c_v4280);
      switch_ret_t264 = call_ret_t265;
      break;
  }
  instr_app(&app_ret_t266, switch_ret_t264, 0);
  instr_free_clo(switch_ret_t264);
  return app_ret_t266;
}

tll_ptr lam_fun_t269(tll_ptr c_v4269, tll_env env)
{
  tll_ptr lam_clo_t268;
  instr_clo(&lam_clo_t268, &lam_fun_t267, 1, c_v4269);
  return lam_clo_t268;
}

tll_ptr lam_fun_t272(tll_ptr __v4284, tll_env env)
{
  tll_ptr __v4286; tll_ptr tt_t271;
  __v4286 = env[0];
  instr_struct(&tt_t271, 1, 0);
  return tt_t271;
}

tll_ptr lam_fun_t274(tll_ptr c_v4281, tll_env env)
{
  tll_ptr lam_clo_t273;
  instr_clo(&lam_clo_t273, &lam_fun_t272, 1, c_v4281);
  return lam_clo_t273;
}

tll_ptr lam_fun_t278(tll_ptr __v4245, tll_env env)
{
  tll_ptr __v4260; tll_ptr app_ret_t276; tll_ptr app_ret_t277;
  tll_ptr c0_v4262; tll_ptr lam_clo_t262; tll_ptr lam_clo_t270;
  tll_ptr lam_clo_t275; tll_ptr msg_v4261; tll_ptr recv_msg_t253;
  tll_ptr switch_ret_t254; tll_ptr switch_ret_t255;
  instr_recv(&recv_msg_t253, env[0]);
  __v4260 = recv_msg_t253;
  switch(((tll_node)__v4260)->tag) {
    case 0:
      msg_v4261 = ((tll_node)__v4260)->data[0];
      c0_v4262 = ((tll_node)__v4260)->data[1];
      instr_free_struct(__v4260);
      switch(((tll_node)msg_v4261)->tag) {
        case 11:
          instr_clo(&lam_clo_t262, &lam_fun_t261, 1, env[1]);
          switch_ret_t255 = lam_clo_t262;
          break;
        case 12:
          instr_clo(&lam_clo_t270, &lam_fun_t269, 0);
          switch_ret_t255 = lam_clo_t270;
          break;
        case 13:
          instr_clo(&lam_clo_t275, &lam_fun_t274, 0);
          switch_ret_t255 = lam_clo_t275;
          break;
      }
      instr_app(&app_ret_t276, switch_ret_t255, c0_v4262);
      instr_free_clo(switch_ret_t255);
      switch_ret_t254 = app_ret_t276;
      break;
  }
  instr_app(&app_ret_t277, switch_ret_t254, 0);
  instr_free_clo(switch_ret_t254);
  return app_ret_t277;
}

tll_ptr ref_handler_i30(tll_ptr A_v4242, tll_ptr m_v4243, tll_ptr c0_v4244)
{
  tll_ptr lam_clo_t279;
  instr_clo(&lam_clo_t279, &lam_fun_t278, 2, c0_v4244, m_v4243);
  return lam_clo_t279;
}

tll_ptr lam_fun_t281(tll_ptr c0_v4292, tll_env env)
{
  tll_ptr call_ret_t280;
  call_ret_t280 = ref_handler_i30(env[1], env[0], c0_v4292);
  return call_ret_t280;
}

tll_ptr lam_fun_t283(tll_ptr m_v4290, tll_env env)
{
  tll_ptr lam_clo_t282;
  instr_clo(&lam_clo_t282, &lam_fun_t281, 2, m_v4290, env[0]);
  return lam_clo_t282;
}

tll_ptr lam_fun_t285(tll_ptr A_v4287, tll_env env)
{
  tll_ptr lam_clo_t284;
  instr_clo(&lam_clo_t284, &lam_fun_t283, 1, A_v4287);
  return lam_clo_t284;
}

tll_ptr fork_fun_t289(tll_env env)
{
  tll_ptr app_ret_t288; tll_ptr call_ret_t287; tll_ptr fork_ret_t291;
  call_ret_t287 = ref_handler_i30(0, env[1], env[0]);
  instr_app(&app_ret_t288, call_ret_t287, 0);
  instr_free_clo(call_ret_t287);
  fork_ret_t291 = app_ret_t288;
  instr_free_thread(env);
  return fork_ret_t291;
}

tll_ptr lam_fun_t292(tll_ptr __v4295, tll_env env)
{
  tll_ptr fork_ch_t290;
  instr_fork(&fork_ch_t290, &fork_fun_t289, 1, env[0]);
  return fork_ch_t290;
}

tll_ptr mk_ref_i31(tll_ptr A_v4293, tll_ptr m_v4294)
{
  tll_ptr lam_clo_t293;
  instr_clo(&lam_clo_t293, &lam_fun_t292, 1, m_v4294);
  return lam_clo_t293;
}

tll_ptr lam_fun_t295(tll_ptr m_v4300, tll_env env)
{
  tll_ptr call_ret_t294;
  call_ret_t294 = mk_ref_i31(env[0], m_v4300);
  return call_ret_t294;
}

tll_ptr lam_fun_t297(tll_ptr A_v4298, tll_env env)
{
  tll_ptr lam_clo_t296;
  instr_clo(&lam_clo_t296, &lam_fun_t295, 1, A_v4298);
  return lam_clo_t296;
}

tll_ptr lam_fun_t302(tll_ptr __v4304, tll_env env)
{
  tll_ptr SET_t300; tll_ptr r_v4306; tll_ptr send_ch_t299;
  tll_ptr send_ch_t301;
  instr_struct(&SET_t300, 12, 0);
  instr_send(&send_ch_t299, env[0], SET_t300);
  r_v4306 = send_ch_t299;
  instr_send(&send_ch_t301, r_v4306, env[1]);
  return send_ch_t301;
}

tll_ptr set_ref_i32(tll_ptr A_v4301, tll_ptr m_v4302, tll_ptr r_v4303)
{
  tll_ptr lam_clo_t303;
  instr_clo(&lam_clo_t303, &lam_fun_t302, 2, r_v4303, m_v4302);
  return lam_clo_t303;
}

tll_ptr lam_fun_t305(tll_ptr r_v4312, tll_env env)
{
  tll_ptr call_ret_t304;
  call_ret_t304 = set_ref_i32(env[1], env[0], r_v4312);
  return call_ret_t304;
}

tll_ptr lam_fun_t307(tll_ptr m_v4310, tll_env env)
{
  tll_ptr lam_clo_t306;
  instr_clo(&lam_clo_t306, &lam_fun_t305, 2, m_v4310, env[0]);
  return lam_clo_t306;
}

tll_ptr lam_fun_t309(tll_ptr A_v4307, tll_env env)
{
  tll_ptr lam_clo_t308;
  instr_clo(&lam_clo_t308, &lam_fun_t307, 1, A_v4307);
  return lam_clo_t308;
}

tll_ptr lam_fun_t314(tll_ptr __v4315, tll_env env)
{
  tll_ptr GET_t312; tll_ptr r_v4317; tll_ptr recv_msg_t313;
  tll_ptr send_ch_t311;
  instr_struct(&GET_t312, 11, 0);
  instr_send(&send_ch_t311, env[0], GET_t312);
  r_v4317 = send_ch_t311;
  instr_recv(&recv_msg_t313, r_v4317);
  return recv_msg_t313;
}

tll_ptr get_ref_i33(tll_ptr A_v4313, tll_ptr r_v4314)
{
  tll_ptr lam_clo_t315;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 1, r_v4314);
  return lam_clo_t315;
}

tll_ptr lam_fun_t317(tll_ptr r_v4320, tll_env env)
{
  tll_ptr call_ret_t316;
  call_ret_t316 = get_ref_i33(env[0], r_v4320);
  return call_ret_t316;
}

tll_ptr lam_fun_t319(tll_ptr A_v4318, tll_env env)
{
  tll_ptr lam_clo_t318;
  instr_clo(&lam_clo_t318, &lam_fun_t317, 1, A_v4318);
  return lam_clo_t318;
}

tll_ptr lam_fun_t324(tll_ptr __v4323, tll_env env)
{
  tll_ptr FREE_t322; tll_ptr close_tmp_t323; tll_ptr r_v4325;
  tll_ptr send_ch_t321;
  instr_struct(&FREE_t322, 13, 0);
  instr_send(&send_ch_t321, env[0], FREE_t322);
  r_v4325 = send_ch_t321;
  instr_close(&close_tmp_t323, r_v4325);
  return close_tmp_t323;
}

tll_ptr free_ref_i34(tll_ptr A_v4321, tll_ptr r_v4322)
{
  tll_ptr lam_clo_t325;
  instr_clo(&lam_clo_t325, &lam_fun_t324, 1, r_v4322);
  return lam_clo_t325;
}

tll_ptr lam_fun_t327(tll_ptr r_v4328, tll_env env)
{
  tll_ptr call_ret_t326;
  call_ret_t326 = free_ref_i34(env[0], r_v4328);
  return call_ret_t326;
}

tll_ptr lam_fun_t329(tll_ptr A_v4326, tll_env env)
{
  tll_ptr lam_clo_t328;
  instr_clo(&lam_clo_t328, &lam_fun_t327, 1, A_v4326);
  return lam_clo_t328;
}

tll_ptr lam_fun_t468(tll_ptr __v4344, tll_env env)
{
  tll_ptr __v4346; tll_ptr app_ret_t464; tll_ptr app_ret_t467;
  tll_ptr call_ret_t463; tll_ptr call_ret_t465; tll_ptr call_ret_t466;
  call_ret_t463 = free_ref_i34(0, env[0]);
  instr_app(&app_ret_t464, call_ret_t463, 0);
  instr_free_clo(call_ret_t463);
  __v4346 = app_ret_t464;
  call_ret_t466 = cats_i15(env[2], env[1]);
  call_ret_t465 = print_i26(call_ret_t466);
  instr_app(&app_ret_t467, call_ret_t465, 0);
  instr_free_clo(call_ret_t465);
  return app_ret_t467;
}

tll_ptr lam_fun_t471(tll_ptr __v4333, tll_env env)
{
  tll_ptr Ascii_t406; tll_ptr Ascii_t415; tll_ptr Ascii_t424;
  tll_ptr Ascii_t433; tll_ptr Ascii_t442; tll_ptr Ascii_t451;
  tll_ptr EmptyString_t452; tll_ptr String_t453; tll_ptr String_t454;
  tll_ptr String_t455; tll_ptr String_t456; tll_ptr String_t457;
  tll_ptr String_t458; tll_ptr __v4341; tll_ptr app_ret_t459;
  tll_ptr app_ret_t461; tll_ptr app_ret_t470; tll_ptr call_ret_t397;
  tll_ptr call_ret_t460; tll_ptr false_t398; tll_ptr false_t402;
  tll_ptr false_t407; tll_ptr false_t410; tll_ptr false_t416;
  tll_ptr false_t420; tll_ptr false_t421; tll_ptr false_t423;
  tll_ptr false_t425; tll_ptr false_t428; tll_ptr false_t431;
  tll_ptr false_t432; tll_ptr false_t434; tll_ptr false_t437;
  tll_ptr false_t438; tll_ptr false_t440; tll_ptr false_t441;
  tll_ptr false_t443; tll_ptr false_t444; tll_ptr false_t445;
  tll_ptr false_t446; tll_ptr false_t448; tll_ptr false_t450;
  tll_ptr lam_clo_t469; tll_ptr r_v4340; tll_ptr r_v4343; tll_ptr s1_v4342;
  tll_ptr switch_ret_t462; tll_ptr true_t399; tll_ptr true_t400;
  tll_ptr true_t401; tll_ptr true_t403; tll_ptr true_t404; tll_ptr true_t405;
  tll_ptr true_t408; tll_ptr true_t409; tll_ptr true_t411; tll_ptr true_t412;
  tll_ptr true_t413; tll_ptr true_t414; tll_ptr true_t417; tll_ptr true_t418;
  tll_ptr true_t419; tll_ptr true_t422; tll_ptr true_t426; tll_ptr true_t427;
  tll_ptr true_t429; tll_ptr true_t430; tll_ptr true_t435; tll_ptr true_t436;
  tll_ptr true_t439; tll_ptr true_t447; tll_ptr true_t449;
  instr_struct(&false_t398, 3, 0);
  instr_struct(&true_t399, 2, 0);
  instr_struct(&true_t400, 2, 0);
  instr_struct(&true_t401, 2, 0);
  instr_struct(&false_t402, 3, 0);
  instr_struct(&true_t403, 2, 0);
  instr_struct(&true_t404, 2, 0);
  instr_struct(&true_t405, 2, 0);
  instr_struct(&Ascii_t406, 6, 8,
               false_t398, true_t399, true_t400, true_t401, false_t402,
               true_t403, true_t404, true_t405);
  instr_struct(&false_t407, 3, 0);
  instr_struct(&true_t408, 2, 0);
  instr_struct(&true_t409, 2, 0);
  instr_struct(&false_t410, 3, 0);
  instr_struct(&true_t411, 2, 0);
  instr_struct(&true_t412, 2, 0);
  instr_struct(&true_t413, 2, 0);
  instr_struct(&true_t414, 2, 0);
  instr_struct(&Ascii_t415, 6, 8,
               false_t407, true_t408, true_t409, false_t410, true_t411,
               true_t412, true_t413, true_t414);
  instr_struct(&false_t416, 3, 0);
  instr_struct(&true_t417, 2, 0);
  instr_struct(&true_t418, 2, 0);
  instr_struct(&true_t419, 2, 0);
  instr_struct(&false_t420, 3, 0);
  instr_struct(&false_t421, 3, 0);
  instr_struct(&true_t422, 2, 0);
  instr_struct(&false_t423, 3, 0);
  instr_struct(&Ascii_t424, 6, 8,
               false_t416, true_t417, true_t418, true_t419, false_t420,
               false_t421, true_t422, false_t423);
  instr_struct(&false_t425, 3, 0);
  instr_struct(&true_t426, 2, 0);
  instr_struct(&true_t427, 2, 0);
  instr_struct(&false_t428, 3, 0);
  instr_struct(&true_t429, 2, 0);
  instr_struct(&true_t430, 2, 0);
  instr_struct(&false_t431, 3, 0);
  instr_struct(&false_t432, 3, 0);
  instr_struct(&Ascii_t433, 6, 8,
               false_t425, true_t426, true_t427, false_t428, true_t429,
               true_t430, false_t431, false_t432);
  instr_struct(&false_t434, 3, 0);
  instr_struct(&true_t435, 2, 0);
  instr_struct(&true_t436, 2, 0);
  instr_struct(&false_t437, 3, 0);
  instr_struct(&false_t438, 3, 0);
  instr_struct(&true_t439, 2, 0);
  instr_struct(&false_t440, 3, 0);
  instr_struct(&false_t441, 3, 0);
  instr_struct(&Ascii_t442, 6, 8,
               false_t434, true_t435, true_t436, false_t437, false_t438,
               true_t439, false_t440, false_t441);
  instr_struct(&false_t443, 3, 0);
  instr_struct(&false_t444, 3, 0);
  instr_struct(&false_t445, 3, 0);
  instr_struct(&false_t446, 3, 0);
  instr_struct(&true_t447, 2, 0);
  instr_struct(&false_t448, 3, 0);
  instr_struct(&true_t449, 2, 0);
  instr_struct(&false_t450, 3, 0);
  instr_struct(&Ascii_t451, 6, 8,
               false_t443, false_t444, false_t445, false_t446, true_t447,
               false_t448, true_t449, false_t450);
  instr_struct(&EmptyString_t452, 7, 0);
  instr_struct(&String_t453, 8, 2, Ascii_t451, EmptyString_t452);
  instr_struct(&String_t454, 8, 2, Ascii_t442, String_t453);
  instr_struct(&String_t455, 8, 2, Ascii_t433, String_t454);
  instr_struct(&String_t456, 8, 2, Ascii_t424, String_t455);
  instr_struct(&String_t457, 8, 2, Ascii_t415, String_t456);
  instr_struct(&String_t458, 8, 2, Ascii_t406, String_t457);
  call_ret_t397 = set_ref_i32(0, String_t458, env[0]);
  instr_app(&app_ret_t459, call_ret_t397, 0);
  instr_free_clo(call_ret_t397);
  r_v4340 = app_ret_t459;
  call_ret_t460 = get_ref_i33(0, r_v4340);
  instr_app(&app_ret_t461, call_ret_t460, 0);
  instr_free_clo(call_ret_t460);
  __v4341 = app_ret_t461;
  switch(((tll_node)__v4341)->tag) {
    case 0:
      s1_v4342 = ((tll_node)__v4341)->data[0];
      r_v4343 = ((tll_node)__v4341)->data[1];
      instr_free_struct(__v4341);
      instr_clo(&lam_clo_t469, &lam_fun_t468, 3, r_v4343, s1_v4342, env[1]);
      switch_ret_t462 = lam_clo_t469;
      break;
  }
  instr_app(&app_ret_t470, switch_ret_t462, 0);
  instr_free_clo(switch_ret_t462);
  return app_ret_t470;
}

int main()
{
  instr_init();
  tll_ptr Ascii_t340; tll_ptr Ascii_t349; tll_ptr Ascii_t358;
  tll_ptr Ascii_t367; tll_ptr Ascii_t376; tll_ptr Ascii_t385;
  tll_ptr EmptyString_t386; tll_ptr String_t387; tll_ptr String_t388;
  tll_ptr String_t389; tll_ptr String_t390; tll_ptr String_t391;
  tll_ptr String_t392; tll_ptr __v4330; tll_ptr app_ret_t393;
  tll_ptr app_ret_t395; tll_ptr app_ret_t473; tll_ptr call_ret_t331;
  tll_ptr call_ret_t394; tll_ptr false_t332; tll_ptr false_t335;
  tll_ptr false_t337; tll_ptr false_t338; tll_ptr false_t339;
  tll_ptr false_t341; tll_ptr false_t344; tll_ptr false_t345;
  tll_ptr false_t347; tll_ptr false_t350; tll_ptr false_t353;
  tll_ptr false_t356; tll_ptr false_t357; tll_ptr false_t359;
  tll_ptr false_t362; tll_ptr false_t365; tll_ptr false_t366;
  tll_ptr false_t368; tll_ptr false_t371; tll_ptr false_t377;
  tll_ptr false_t378; tll_ptr false_t380; tll_ptr false_t381;
  tll_ptr false_t382; tll_ptr false_t383; tll_ptr false_t384;
  tll_ptr lam_clo_t106; tll_ptr lam_clo_t117; tll_ptr lam_clo_t125;
  tll_ptr lam_clo_t133; tll_ptr lam_clo_t14; tll_ptr lam_clo_t140;
  tll_ptr lam_clo_t154; tll_ptr lam_clo_t168; tll_ptr lam_clo_t182;
  tll_ptr lam_clo_t192; tll_ptr lam_clo_t20; tll_ptr lam_clo_t202;
  tll_ptr lam_clo_t212; tll_ptr lam_clo_t228; tll_ptr lam_clo_t240;
  tll_ptr lam_clo_t252; tll_ptr lam_clo_t286; tll_ptr lam_clo_t298;
  tll_ptr lam_clo_t30; tll_ptr lam_clo_t310; tll_ptr lam_clo_t320;
  tll_ptr lam_clo_t330; tll_ptr lam_clo_t42; tll_ptr lam_clo_t472;
  tll_ptr lam_clo_t54; tll_ptr lam_clo_t64; tll_ptr lam_clo_t7;
  tll_ptr lam_clo_t76; tll_ptr lam_clo_t81; tll_ptr lam_clo_t89;
  tll_ptr lam_clo_t97; tll_ptr r_v4329; tll_ptr r_v4332; tll_ptr s0_v4331;
  tll_ptr switch_ret_t396; tll_ptr true_t333; tll_ptr true_t334;
  tll_ptr true_t336; tll_ptr true_t342; tll_ptr true_t343; tll_ptr true_t346;
  tll_ptr true_t348; tll_ptr true_t351; tll_ptr true_t352; tll_ptr true_t354;
  tll_ptr true_t355; tll_ptr true_t360; tll_ptr true_t361; tll_ptr true_t363;
  tll_ptr true_t364; tll_ptr true_t369; tll_ptr true_t370; tll_ptr true_t372;
  tll_ptr true_t373; tll_ptr true_t374; tll_ptr true_t375; tll_ptr true_t379;
  instr_clo(&lam_clo_t7, &lam_fun_t6, 0);
  andbclo_i44 = lam_clo_t7;
  instr_clo(&lam_clo_t14, &lam_fun_t13, 0);
  orbclo_i45 = lam_clo_t14;
  instr_clo(&lam_clo_t20, &lam_fun_t19, 0);
  notbclo_i46 = lam_clo_t20;
  instr_clo(&lam_clo_t30, &lam_fun_t29, 0);
  ltenclo_i47 = lam_clo_t30;
  instr_clo(&lam_clo_t42, &lam_fun_t41, 0);
  gtenclo_i48 = lam_clo_t42;
  instr_clo(&lam_clo_t54, &lam_fun_t53, 0);
  ltnclo_i49 = lam_clo_t54;
  instr_clo(&lam_clo_t64, &lam_fun_t63, 0);
  gtnclo_i50 = lam_clo_t64;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 0);
  eqnclo_i51 = lam_clo_t76;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 0);
  predclo_i52 = lam_clo_t81;
  instr_clo(&lam_clo_t89, &lam_fun_t88, 0);
  addnclo_i53 = lam_clo_t89;
  instr_clo(&lam_clo_t97, &lam_fun_t96, 0);
  subnclo_i54 = lam_clo_t97;
  instr_clo(&lam_clo_t106, &lam_fun_t105, 0);
  mulnclo_i55 = lam_clo_t106;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 0);
  divnclo_i56 = lam_clo_t117;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 0);
  modnclo_i57 = lam_clo_t125;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 0);
  catsclo_i58 = lam_clo_t133;
  instr_clo(&lam_clo_t140, &lam_fun_t139, 0);
  strlenclo_i59 = lam_clo_t140;
  instr_clo(&lam_clo_t154, &lam_fun_t153, 0);
  lenUUclo_i60 = lam_clo_t154;
  instr_clo(&lam_clo_t168, &lam_fun_t167, 0);
  lenULclo_i61 = lam_clo_t168;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 0);
  lenLLclo_i62 = lam_clo_t182;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 0);
  appendUUclo_i63 = lam_clo_t192;
  instr_clo(&lam_clo_t202, &lam_fun_t201, 0);
  appendULclo_i64 = lam_clo_t202;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  appendLLclo_i65 = lam_clo_t212;
  instr_clo(&lam_clo_t228, &lam_fun_t227, 0);
  readlineclo_i66 = lam_clo_t228;
  instr_clo(&lam_clo_t240, &lam_fun_t239, 0);
  printclo_i67 = lam_clo_t240;
  instr_clo(&lam_clo_t252, &lam_fun_t251, 0);
  prerrclo_i68 = lam_clo_t252;
  instr_clo(&lam_clo_t286, &lam_fun_t285, 0);
  ref_handlerclo_i69 = lam_clo_t286;
  instr_clo(&lam_clo_t298, &lam_fun_t297, 0);
  mk_refclo_i70 = lam_clo_t298;
  instr_clo(&lam_clo_t310, &lam_fun_t309, 0);
  set_refclo_i71 = lam_clo_t310;
  instr_clo(&lam_clo_t320, &lam_fun_t319, 0);
  get_refclo_i72 = lam_clo_t320;
  instr_clo(&lam_clo_t330, &lam_fun_t329, 0);
  free_refclo_i73 = lam_clo_t330;
  instr_struct(&false_t332, 3, 0);
  instr_struct(&true_t333, 2, 0);
  instr_struct(&true_t334, 2, 0);
  instr_struct(&false_t335, 3, 0);
  instr_struct(&true_t336, 2, 0);
  instr_struct(&false_t337, 3, 0);
  instr_struct(&false_t338, 3, 0);
  instr_struct(&false_t339, 3, 0);
  instr_struct(&Ascii_t340, 6, 8,
               false_t332, true_t333, true_t334, false_t335, true_t336,
               false_t337, false_t338, false_t339);
  instr_struct(&false_t341, 3, 0);
  instr_struct(&true_t342, 2, 0);
  instr_struct(&true_t343, 2, 0);
  instr_struct(&false_t344, 3, 0);
  instr_struct(&false_t345, 3, 0);
  instr_struct(&true_t346, 2, 0);
  instr_struct(&false_t347, 3, 0);
  instr_struct(&true_t348, 2, 0);
  instr_struct(&Ascii_t349, 6, 8,
               false_t341, true_t342, true_t343, false_t344, false_t345,
               true_t346, false_t347, true_t348);
  instr_struct(&false_t350, 3, 0);
  instr_struct(&true_t351, 2, 0);
  instr_struct(&true_t352, 2, 0);
  instr_struct(&false_t353, 3, 0);
  instr_struct(&true_t354, 2, 0);
  instr_struct(&true_t355, 2, 0);
  instr_struct(&false_t356, 3, 0);
  instr_struct(&false_t357, 3, 0);
  instr_struct(&Ascii_t358, 6, 8,
               false_t350, true_t351, true_t352, false_t353, true_t354,
               true_t355, false_t356, false_t357);
  instr_struct(&false_t359, 3, 0);
  instr_struct(&true_t360, 2, 0);
  instr_struct(&true_t361, 2, 0);
  instr_struct(&false_t362, 3, 0);
  instr_struct(&true_t363, 2, 0);
  instr_struct(&true_t364, 2, 0);
  instr_struct(&false_t365, 3, 0);
  instr_struct(&false_t366, 3, 0);
  instr_struct(&Ascii_t367, 6, 8,
               false_t359, true_t360, true_t361, false_t362, true_t363,
               true_t364, false_t365, false_t366);
  instr_struct(&false_t368, 3, 0);
  instr_struct(&true_t369, 2, 0);
  instr_struct(&true_t370, 2, 0);
  instr_struct(&false_t371, 3, 0);
  instr_struct(&true_t372, 2, 0);
  instr_struct(&true_t373, 2, 0);
  instr_struct(&true_t374, 2, 0);
  instr_struct(&true_t375, 2, 0);
  instr_struct(&Ascii_t376, 6, 8,
               false_t368, true_t369, true_t370, false_t371, true_t372,
               true_t373, true_t374, true_t375);
  instr_struct(&false_t377, 3, 0);
  instr_struct(&false_t378, 3, 0);
  instr_struct(&true_t379, 2, 0);
  instr_struct(&false_t380, 3, 0);
  instr_struct(&false_t381, 3, 0);
  instr_struct(&false_t382, 3, 0);
  instr_struct(&false_t383, 3, 0);
  instr_struct(&false_t384, 3, 0);
  instr_struct(&Ascii_t385, 6, 8,
               false_t377, false_t378, true_t379, false_t380, false_t381,
               false_t382, false_t383, false_t384);
  instr_struct(&EmptyString_t386, 7, 0);
  instr_struct(&String_t387, 8, 2, Ascii_t385, EmptyString_t386);
  instr_struct(&String_t388, 8, 2, Ascii_t376, String_t387);
  instr_struct(&String_t389, 8, 2, Ascii_t367, String_t388);
  instr_struct(&String_t390, 8, 2, Ascii_t358, String_t389);
  instr_struct(&String_t391, 8, 2, Ascii_t349, String_t390);
  instr_struct(&String_t392, 8, 2, Ascii_t340, String_t391);
  call_ret_t331 = mk_ref_i31(0, String_t392);
  instr_app(&app_ret_t393, call_ret_t331, 0);
  instr_free_clo(call_ret_t331);
  r_v4329 = app_ret_t393;
  call_ret_t394 = get_ref_i33(0, r_v4329);
  instr_app(&app_ret_t395, call_ret_t394, 0);
  instr_free_clo(call_ret_t394);
  __v4330 = app_ret_t395;
  switch(((tll_node)__v4330)->tag) {
    case 0:
      s0_v4331 = ((tll_node)__v4330)->data[0];
      r_v4332 = ((tll_node)__v4330)->data[1];
      instr_free_struct(__v4330);
      instr_clo(&lam_clo_t472, &lam_fun_t471, 2, r_v4332, s0_v4331);
      switch_ret_t396 = lam_clo_t472;
      break;
  }
  instr_app(&app_ret_t473, switch_ret_t396, 0);
  instr_free_clo(switch_ret_t396);
  instr_free_struct(app_ret_t473);
  return 0;
}

