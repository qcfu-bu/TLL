#include "runtime.h"

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
tll_ptr ref_handlerclo_i63;
tll_ptr strlenclo_i53;
tll_ptr subnclo_i48;

tll_ptr andb_i1(tll_ptr b1_v3297, tll_ptr b2_v3298)
{
  tll_ptr false_t2; tll_ptr switch_ret_t1;
  switch(((tll_node)b1_v3297)->tag) {
    case 2:
      switch_ret_t1 = b2_v3298;
      break;
    case 3:
      instr_struct(&false_t2, 3, 0);
      switch_ret_t1 = false_t2;
      break;
  }
  return switch_ret_t1;
}

tll_ptr lam_fun_t4(tll_ptr b2_v3301, tll_env env)
{
  tll_ptr call_ret_t3;
  call_ret_t3 = andb_i1(env[0], b2_v3301);
  return call_ret_t3;
}

tll_ptr lam_fun_t6(tll_ptr b1_v3299, tll_env env)
{
  tll_ptr lam_clo_t5;
  instr_clo(&lam_clo_t5, &lam_fun_t4, 1, b1_v3299);
  return lam_clo_t5;
}

tll_ptr orb_i2(tll_ptr b1_v3302, tll_ptr b2_v3303)
{
  tll_ptr switch_ret_t8; tll_ptr true_t9;
  switch(((tll_node)b1_v3302)->tag) {
    case 2:
      instr_struct(&true_t9, 2, 0);
      switch_ret_t8 = true_t9;
      break;
    case 3:
      switch_ret_t8 = b2_v3303;
      break;
  }
  return switch_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b2_v3306, tll_env env)
{
  tll_ptr call_ret_t10;
  call_ret_t10 = orb_i2(env[0], b2_v3306);
  return call_ret_t10;
}

tll_ptr lam_fun_t13(tll_ptr b1_v3304, tll_env env)
{
  tll_ptr lam_clo_t12;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 1, b1_v3304);
  return lam_clo_t12;
}

tll_ptr notb_i3(tll_ptr b_v3307)
{
  tll_ptr false_t16; tll_ptr switch_ret_t15; tll_ptr true_t17;
  switch(((tll_node)b_v3307)->tag) {
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

tll_ptr lam_fun_t19(tll_ptr b_v3308, tll_env env)
{
  tll_ptr call_ret_t18;
  call_ret_t18 = notb_i3(b_v3308);
  return call_ret_t18;
}

tll_ptr lten_i4(tll_ptr x_v3309, tll_ptr y_v3310)
{
  tll_ptr call_ret_t25; tll_ptr false_t24; tll_ptr switch_ret_t21;
  tll_ptr switch_ret_t23; tll_ptr true_t22; tll_ptr x_v3311; tll_ptr y_v3312;
  switch(((tll_node)x_v3309)->tag) {
    case 4:
      instr_struct(&true_t22, 2, 0);
      switch_ret_t21 = true_t22;
      break;
    case 5:
      x_v3311 = ((tll_node)x_v3309)->data[0];
      switch(((tll_node)y_v3310)->tag) {
        case 4:
          instr_struct(&false_t24, 3, 0);
          switch_ret_t23 = false_t24;
          break;
        case 5:
          y_v3312 = ((tll_node)y_v3310)->data[0];
          call_ret_t25 = lten_i4(x_v3311, y_v3312);
          switch_ret_t23 = call_ret_t25;
          break;
      }
      switch_ret_t21 = switch_ret_t23;
      break;
  }
  return switch_ret_t21;
}

tll_ptr lam_fun_t27(tll_ptr y_v3315, tll_env env)
{
  tll_ptr call_ret_t26;
  call_ret_t26 = lten_i4(env[0], y_v3315);
  return call_ret_t26;
}

tll_ptr lam_fun_t29(tll_ptr x_v3313, tll_env env)
{
  tll_ptr lam_clo_t28;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 1, x_v3313);
  return lam_clo_t28;
}

tll_ptr gten_i5(tll_ptr x_v3316, tll_ptr y_v3317)
{
  tll_ptr __v3318; tll_ptr call_ret_t37; tll_ptr false_t34;
  tll_ptr switch_ret_t31; tll_ptr switch_ret_t32; tll_ptr switch_ret_t35;
  tll_ptr true_t33; tll_ptr true_t36; tll_ptr x_v3319; tll_ptr y_v3320;
  switch(((tll_node)x_v3316)->tag) {
    case 4:
      switch(((tll_node)y_v3317)->tag) {
        case 4:
          instr_struct(&true_t33, 2, 0);
          switch_ret_t32 = true_t33;
          break;
        case 5:
          __v3318 = ((tll_node)y_v3317)->data[0];
          instr_struct(&false_t34, 3, 0);
          switch_ret_t32 = false_t34;
          break;
      }
      switch_ret_t31 = switch_ret_t32;
      break;
    case 5:
      x_v3319 = ((tll_node)x_v3316)->data[0];
      switch(((tll_node)y_v3317)->tag) {
        case 4:
          instr_struct(&true_t36, 2, 0);
          switch_ret_t35 = true_t36;
          break;
        case 5:
          y_v3320 = ((tll_node)y_v3317)->data[0];
          call_ret_t37 = gten_i5(x_v3319, y_v3320);
          switch_ret_t35 = call_ret_t37;
          break;
      }
      switch_ret_t31 = switch_ret_t35;
      break;
  }
  return switch_ret_t31;
}

tll_ptr lam_fun_t39(tll_ptr y_v3323, tll_env env)
{
  tll_ptr call_ret_t38;
  call_ret_t38 = gten_i5(env[0], y_v3323);
  return call_ret_t38;
}

tll_ptr lam_fun_t41(tll_ptr x_v3321, tll_env env)
{
  tll_ptr lam_clo_t40;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 1, x_v3321);
  return lam_clo_t40;
}

tll_ptr ltn_i6(tll_ptr x_v3324, tll_ptr y_v3325)
{
  tll_ptr call_ret_t49; tll_ptr false_t45; tll_ptr false_t48;
  tll_ptr switch_ret_t43; tll_ptr switch_ret_t44; tll_ptr switch_ret_t47;
  tll_ptr true_t46; tll_ptr x_v3327; tll_ptr y_v3326; tll_ptr y_v3328;
  switch(((tll_node)x_v3324)->tag) {
    case 4:
      switch(((tll_node)y_v3325)->tag) {
        case 4:
          instr_struct(&false_t45, 3, 0);
          switch_ret_t44 = false_t45;
          break;
        case 5:
          y_v3326 = ((tll_node)y_v3325)->data[0];
          instr_struct(&true_t46, 2, 0);
          switch_ret_t44 = true_t46;
          break;
      }
      switch_ret_t43 = switch_ret_t44;
      break;
    case 5:
      x_v3327 = ((tll_node)x_v3324)->data[0];
      switch(((tll_node)y_v3325)->tag) {
        case 4:
          instr_struct(&false_t48, 3, 0);
          switch_ret_t47 = false_t48;
          break;
        case 5:
          y_v3328 = ((tll_node)y_v3325)->data[0];
          call_ret_t49 = ltn_i6(x_v3327, y_v3328);
          switch_ret_t47 = call_ret_t49;
          break;
      }
      switch_ret_t43 = switch_ret_t47;
      break;
  }
  return switch_ret_t43;
}

tll_ptr lam_fun_t51(tll_ptr y_v3331, tll_env env)
{
  tll_ptr call_ret_t50;
  call_ret_t50 = ltn_i6(env[0], y_v3331);
  return call_ret_t50;
}

tll_ptr lam_fun_t53(tll_ptr x_v3329, tll_env env)
{
  tll_ptr lam_clo_t52;
  instr_clo(&lam_clo_t52, &lam_fun_t51, 1, x_v3329);
  return lam_clo_t52;
}

tll_ptr gtn_i7(tll_ptr x_v3332, tll_ptr y_v3333)
{
  tll_ptr call_ret_t59; tll_ptr false_t56; tll_ptr switch_ret_t55;
  tll_ptr switch_ret_t57; tll_ptr true_t58; tll_ptr x_v3334; tll_ptr y_v3335;
  switch(((tll_node)x_v3332)->tag) {
    case 4:
      instr_struct(&false_t56, 3, 0);
      switch_ret_t55 = false_t56;
      break;
    case 5:
      x_v3334 = ((tll_node)x_v3332)->data[0];
      switch(((tll_node)y_v3333)->tag) {
        case 4:
          instr_struct(&true_t58, 2, 0);
          switch_ret_t57 = true_t58;
          break;
        case 5:
          y_v3335 = ((tll_node)y_v3333)->data[0];
          call_ret_t59 = gtn_i7(x_v3334, y_v3335);
          switch_ret_t57 = call_ret_t59;
          break;
      }
      switch_ret_t55 = switch_ret_t57;
      break;
  }
  return switch_ret_t55;
}

tll_ptr lam_fun_t61(tll_ptr y_v3338, tll_env env)
{
  tll_ptr call_ret_t60;
  call_ret_t60 = gtn_i7(env[0], y_v3338);
  return call_ret_t60;
}

tll_ptr lam_fun_t63(tll_ptr x_v3336, tll_env env)
{
  tll_ptr lam_clo_t62;
  instr_clo(&lam_clo_t62, &lam_fun_t61, 1, x_v3336);
  return lam_clo_t62;
}

tll_ptr eqn_i8(tll_ptr x_v3339, tll_ptr y_v3340)
{
  tll_ptr __v3341; tll_ptr call_ret_t71; tll_ptr false_t68;
  tll_ptr false_t70; tll_ptr switch_ret_t65; tll_ptr switch_ret_t66;
  tll_ptr switch_ret_t69; tll_ptr true_t67; tll_ptr x_v3342; tll_ptr y_v3343;
  switch(((tll_node)x_v3339)->tag) {
    case 4:
      switch(((tll_node)y_v3340)->tag) {
        case 4:
          instr_struct(&true_t67, 2, 0);
          switch_ret_t66 = true_t67;
          break;
        case 5:
          __v3341 = ((tll_node)y_v3340)->data[0];
          instr_struct(&false_t68, 3, 0);
          switch_ret_t66 = false_t68;
          break;
      }
      switch_ret_t65 = switch_ret_t66;
      break;
    case 5:
      x_v3342 = ((tll_node)x_v3339)->data[0];
      switch(((tll_node)y_v3340)->tag) {
        case 4:
          instr_struct(&false_t70, 3, 0);
          switch_ret_t69 = false_t70;
          break;
        case 5:
          y_v3343 = ((tll_node)y_v3340)->data[0];
          call_ret_t71 = eqn_i8(x_v3342, y_v3343);
          switch_ret_t69 = call_ret_t71;
          break;
      }
      switch_ret_t65 = switch_ret_t69;
      break;
  }
  return switch_ret_t65;
}

tll_ptr lam_fun_t73(tll_ptr y_v3346, tll_env env)
{
  tll_ptr call_ret_t72;
  call_ret_t72 = eqn_i8(env[0], y_v3346);
  return call_ret_t72;
}

tll_ptr lam_fun_t75(tll_ptr x_v3344, tll_env env)
{
  tll_ptr lam_clo_t74;
  instr_clo(&lam_clo_t74, &lam_fun_t73, 1, x_v3344);
  return lam_clo_t74;
}

tll_ptr pred_i9(tll_ptr x_v3347)
{
  tll_ptr O_t78; tll_ptr switch_ret_t77; tll_ptr x_v3348;
  switch(((tll_node)x_v3347)->tag) {
    case 4:
      instr_struct(&O_t78, 4, 0);
      switch_ret_t77 = O_t78;
      break;
    case 5:
      x_v3348 = ((tll_node)x_v3347)->data[0];
      switch_ret_t77 = x_v3348;
      break;
  }
  return switch_ret_t77;
}

tll_ptr lam_fun_t80(tll_ptr x_v3349, tll_env env)
{
  tll_ptr call_ret_t79;
  call_ret_t79 = pred_i9(x_v3349);
  return call_ret_t79;
}

tll_ptr addn_i10(tll_ptr x_v3350, tll_ptr y_v3351)
{
  tll_ptr S_t84; tll_ptr call_ret_t83; tll_ptr switch_ret_t82;
  tll_ptr x_v3352;
  switch(((tll_node)x_v3350)->tag) {
    case 4:
      switch_ret_t82 = y_v3351;
      break;
    case 5:
      x_v3352 = ((tll_node)x_v3350)->data[0];
      call_ret_t83 = addn_i10(x_v3352, y_v3351);
      instr_struct(&S_t84, 5, 1, call_ret_t83);
      switch_ret_t82 = S_t84;
      break;
  }
  return switch_ret_t82;
}

tll_ptr lam_fun_t86(tll_ptr y_v3355, tll_env env)
{
  tll_ptr call_ret_t85;
  call_ret_t85 = addn_i10(env[0], y_v3355);
  return call_ret_t85;
}

tll_ptr lam_fun_t88(tll_ptr x_v3353, tll_env env)
{
  tll_ptr lam_clo_t87;
  instr_clo(&lam_clo_t87, &lam_fun_t86, 1, x_v3353);
  return lam_clo_t87;
}

tll_ptr subn_i11(tll_ptr x_v3356, tll_ptr y_v3357)
{
  tll_ptr call_ret_t91; tll_ptr call_ret_t92; tll_ptr switch_ret_t90;
  tll_ptr y_v3358;
  switch(((tll_node)y_v3357)->tag) {
    case 4:
      switch_ret_t90 = x_v3356;
      break;
    case 5:
      y_v3358 = ((tll_node)y_v3357)->data[0];
      call_ret_t92 = pred_i9(x_v3356);
      call_ret_t91 = subn_i11(call_ret_t92, y_v3358);
      switch_ret_t90 = call_ret_t91;
      break;
  }
  return switch_ret_t90;
}

tll_ptr lam_fun_t94(tll_ptr y_v3361, tll_env env)
{
  tll_ptr call_ret_t93;
  call_ret_t93 = subn_i11(env[0], y_v3361);
  return call_ret_t93;
}

tll_ptr lam_fun_t96(tll_ptr x_v3359, tll_env env)
{
  tll_ptr lam_clo_t95;
  instr_clo(&lam_clo_t95, &lam_fun_t94, 1, x_v3359);
  return lam_clo_t95;
}

tll_ptr muln_i12(tll_ptr x_v3362, tll_ptr y_v3363)
{
  tll_ptr O_t99; tll_ptr call_ret_t100; tll_ptr call_ret_t101;
  tll_ptr switch_ret_t98; tll_ptr x_v3364;
  switch(((tll_node)x_v3362)->tag) {
    case 4:
      instr_struct(&O_t99, 4, 0);
      switch_ret_t98 = O_t99;
      break;
    case 5:
      x_v3364 = ((tll_node)x_v3362)->data[0];
      call_ret_t101 = muln_i12(x_v3364, y_v3363);
      call_ret_t100 = addn_i10(y_v3363, call_ret_t101);
      switch_ret_t98 = call_ret_t100;
      break;
  }
  return switch_ret_t98;
}

tll_ptr lam_fun_t103(tll_ptr y_v3367, tll_env env)
{
  tll_ptr call_ret_t102;
  call_ret_t102 = muln_i12(env[0], y_v3367);
  return call_ret_t102;
}

tll_ptr lam_fun_t105(tll_ptr x_v3365, tll_env env)
{
  tll_ptr lam_clo_t104;
  instr_clo(&lam_clo_t104, &lam_fun_t103, 1, x_v3365);
  return lam_clo_t104;
}

tll_ptr divn_i13(tll_ptr x_v3368, tll_ptr y_v3369)
{
  tll_ptr O_t109; tll_ptr S_t112; tll_ptr call_ret_t107;
  tll_ptr call_ret_t110; tll_ptr call_ret_t111; tll_ptr switch_ret_t108;
  call_ret_t107 = ltn_i6(x_v3368, y_v3369);
  switch(((tll_node)call_ret_t107)->tag) {
    case 2:
      instr_struct(&O_t109, 4, 0);
      switch_ret_t108 = O_t109;
      break;
    case 3:
      call_ret_t111 = subn_i11(x_v3368, y_v3369);
      call_ret_t110 = divn_i13(call_ret_t111, y_v3369);
      instr_struct(&S_t112, 5, 1, call_ret_t110);
      switch_ret_t108 = S_t112;
      break;
  }
  return switch_ret_t108;
}

tll_ptr lam_fun_t114(tll_ptr y_v3372, tll_env env)
{
  tll_ptr call_ret_t113;
  call_ret_t113 = divn_i13(env[0], y_v3372);
  return call_ret_t113;
}

tll_ptr lam_fun_t116(tll_ptr x_v3370, tll_env env)
{
  tll_ptr lam_clo_t115;
  instr_clo(&lam_clo_t115, &lam_fun_t114, 1, x_v3370);
  return lam_clo_t115;
}

tll_ptr modn_i14(tll_ptr x_v3373, tll_ptr y_v3374)
{
  tll_ptr call_ret_t118; tll_ptr call_ret_t119; tll_ptr call_ret_t120;
  call_ret_t120 = divn_i13(x_v3373, y_v3374);
  call_ret_t119 = muln_i12(call_ret_t120, y_v3374);
  call_ret_t118 = subn_i11(x_v3373, call_ret_t119);
  return call_ret_t118;
}

tll_ptr lam_fun_t122(tll_ptr y_v3377, tll_env env)
{
  tll_ptr call_ret_t121;
  call_ret_t121 = modn_i14(env[0], y_v3377);
  return call_ret_t121;
}

tll_ptr lam_fun_t124(tll_ptr x_v3375, tll_env env)
{
  tll_ptr lam_clo_t123;
  instr_clo(&lam_clo_t123, &lam_fun_t122, 1, x_v3375);
  return lam_clo_t123;
}

tll_ptr cats_i15(tll_ptr s1_v3378, tll_ptr s2_v3379)
{
  tll_ptr String_t128; tll_ptr c_v3380; tll_ptr call_ret_t127;
  tll_ptr s1_v3381; tll_ptr switch_ret_t126;
  switch(((tll_node)s1_v3378)->tag) {
    case 7:
      switch_ret_t126 = s2_v3379;
      break;
    case 8:
      c_v3380 = ((tll_node)s1_v3378)->data[0];
      s1_v3381 = ((tll_node)s1_v3378)->data[1];
      call_ret_t127 = cats_i15(s1_v3381, s2_v3379);
      instr_struct(&String_t128, 8, 2, c_v3380, call_ret_t127);
      switch_ret_t126 = String_t128;
      break;
  }
  return switch_ret_t126;
}

tll_ptr lam_fun_t130(tll_ptr s2_v3384, tll_env env)
{
  tll_ptr call_ret_t129;
  call_ret_t129 = cats_i15(env[0], s2_v3384);
  return call_ret_t129;
}

tll_ptr lam_fun_t132(tll_ptr s1_v3382, tll_env env)
{
  tll_ptr lam_clo_t131;
  instr_clo(&lam_clo_t131, &lam_fun_t130, 1, s1_v3382);
  return lam_clo_t131;
}

tll_ptr strlen_i16(tll_ptr s_v3385)
{
  tll_ptr O_t135; tll_ptr S_t137; tll_ptr __v3386; tll_ptr call_ret_t136;
  tll_ptr s_v3387; tll_ptr switch_ret_t134;
  switch(((tll_node)s_v3385)->tag) {
    case 7:
      instr_struct(&O_t135, 4, 0);
      switch_ret_t134 = O_t135;
      break;
    case 8:
      __v3386 = ((tll_node)s_v3385)->data[0];
      s_v3387 = ((tll_node)s_v3385)->data[1];
      call_ret_t136 = strlen_i16(s_v3387);
      instr_struct(&S_t137, 5, 1, call_ret_t136);
      switch_ret_t134 = S_t137;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t139(tll_ptr s_v3388, tll_env env)
{
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i16(s_v3388);
  return call_ret_t138;
}

tll_ptr lenUU_i33(tll_ptr A_v3389, tll_ptr xs_v3390)
{
  tll_ptr O_t142; tll_ptr S_t147; tll_ptr call_ret_t145; tll_ptr consUU_t148;
  tll_ptr n_v3393; tll_ptr nilUU_t143; tll_ptr pair_struct_t144;
  tll_ptr pair_struct_t149; tll_ptr switch_ret_t141; tll_ptr switch_ret_t146;
  tll_ptr x_v3391; tll_ptr xs_v3392; tll_ptr xs_v3394;
  switch(((tll_node)xs_v3390)->tag) {
    case 20:
      instr_struct(&O_t142, 4, 0);
      instr_struct(&nilUU_t143, 20, 0);
      instr_struct(&pair_struct_t144, 0, 2, O_t142, nilUU_t143);
      switch_ret_t141 = pair_struct_t144;
      break;
    case 21:
      x_v3391 = ((tll_node)xs_v3390)->data[0];
      xs_v3392 = ((tll_node)xs_v3390)->data[1];
      call_ret_t145 = lenUU_i33(0, xs_v3392);
      switch(((tll_node)call_ret_t145)->tag) {
        case 0:
          n_v3393 = ((tll_node)call_ret_t145)->data[0];
          xs_v3394 = ((tll_node)call_ret_t145)->data[1];
          instr_free_struct(call_ret_t145);
          instr_struct(&S_t147, 5, 1, n_v3393);
          instr_struct(&consUU_t148, 21, 2, x_v3391, xs_v3394);
          instr_struct(&pair_struct_t149, 0, 2, S_t147, consUU_t148);
          switch_ret_t146 = pair_struct_t149;
          break;
      }
      switch_ret_t141 = switch_ret_t146;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t151(tll_ptr xs_v3397, tll_env env)
{
  tll_ptr call_ret_t150;
  call_ret_t150 = lenUU_i33(env[0], xs_v3397);
  return call_ret_t150;
}

tll_ptr lam_fun_t153(tll_ptr A_v3395, tll_env env)
{
  tll_ptr lam_clo_t152;
  instr_clo(&lam_clo_t152, &lam_fun_t151, 1, A_v3395);
  return lam_clo_t152;
}

tll_ptr lenUL_i32(tll_ptr A_v3398, tll_ptr xs_v3399)
{
  tll_ptr O_t156; tll_ptr S_t161; tll_ptr call_ret_t159; tll_ptr consUL_t162;
  tll_ptr n_v3402; tll_ptr nilUL_t157; tll_ptr pair_struct_t158;
  tll_ptr pair_struct_t163; tll_ptr switch_ret_t155; tll_ptr switch_ret_t160;
  tll_ptr x_v3400; tll_ptr xs_v3401; tll_ptr xs_v3403;
  switch(((tll_node)xs_v3399)->tag) {
    case 18:
      instr_free_struct(xs_v3399);
      instr_struct(&O_t156, 4, 0);
      instr_struct(&nilUL_t157, 18, 0);
      instr_struct(&pair_struct_t158, 0, 2, O_t156, nilUL_t157);
      switch_ret_t155 = pair_struct_t158;
      break;
    case 19:
      x_v3400 = ((tll_node)xs_v3399)->data[0];
      xs_v3401 = ((tll_node)xs_v3399)->data[1];
      instr_free_struct(xs_v3399);
      call_ret_t159 = lenUL_i32(0, xs_v3401);
      switch(((tll_node)call_ret_t159)->tag) {
        case 0:
          n_v3402 = ((tll_node)call_ret_t159)->data[0];
          xs_v3403 = ((tll_node)call_ret_t159)->data[1];
          instr_free_struct(call_ret_t159);
          instr_struct(&S_t161, 5, 1, n_v3402);
          instr_struct(&consUL_t162, 19, 2, x_v3400, xs_v3403);
          instr_struct(&pair_struct_t163, 0, 2, S_t161, consUL_t162);
          switch_ret_t160 = pair_struct_t163;
          break;
      }
      switch_ret_t155 = switch_ret_t160;
      break;
  }
  return switch_ret_t155;
}

tll_ptr lam_fun_t165(tll_ptr xs_v3406, tll_env env)
{
  tll_ptr call_ret_t164;
  call_ret_t164 = lenUL_i32(env[0], xs_v3406);
  return call_ret_t164;
}

tll_ptr lam_fun_t167(tll_ptr A_v3404, tll_env env)
{
  tll_ptr lam_clo_t166;
  instr_clo(&lam_clo_t166, &lam_fun_t165, 1, A_v3404);
  return lam_clo_t166;
}

tll_ptr lenLL_i30(tll_ptr A_v3407, tll_ptr xs_v3408)
{
  tll_ptr O_t170; tll_ptr S_t175; tll_ptr call_ret_t173; tll_ptr consLL_t176;
  tll_ptr n_v3411; tll_ptr nilLL_t171; tll_ptr pair_struct_t172;
  tll_ptr pair_struct_t177; tll_ptr switch_ret_t169; tll_ptr switch_ret_t174;
  tll_ptr x_v3409; tll_ptr xs_v3410; tll_ptr xs_v3412;
  switch(((tll_node)xs_v3408)->tag) {
    case 14:
      instr_free_struct(xs_v3408);
      instr_struct(&O_t170, 4, 0);
      instr_struct(&nilLL_t171, 14, 0);
      instr_struct(&pair_struct_t172, 0, 2, O_t170, nilLL_t171);
      switch_ret_t169 = pair_struct_t172;
      break;
    case 15:
      x_v3409 = ((tll_node)xs_v3408)->data[0];
      xs_v3410 = ((tll_node)xs_v3408)->data[1];
      instr_free_struct(xs_v3408);
      call_ret_t173 = lenLL_i30(0, xs_v3410);
      switch(((tll_node)call_ret_t173)->tag) {
        case 0:
          n_v3411 = ((tll_node)call_ret_t173)->data[0];
          xs_v3412 = ((tll_node)call_ret_t173)->data[1];
          instr_free_struct(call_ret_t173);
          instr_struct(&S_t175, 5, 1, n_v3411);
          instr_struct(&consLL_t176, 15, 2, x_v3409, xs_v3412);
          instr_struct(&pair_struct_t177, 0, 2, S_t175, consLL_t176);
          switch_ret_t174 = pair_struct_t177;
          break;
      }
      switch_ret_t169 = switch_ret_t174;
      break;
  }
  return switch_ret_t169;
}

tll_ptr lam_fun_t179(tll_ptr xs_v3415, tll_env env)
{
  tll_ptr call_ret_t178;
  call_ret_t178 = lenLL_i30(env[0], xs_v3415);
  return call_ret_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v3413, tll_env env)
{
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v3413);
  return lam_clo_t180;
}

tll_ptr appendUU_i37(tll_ptr A_v3416, tll_ptr xs_v3417, tll_ptr ys_v3418)
{
  tll_ptr call_ret_t184; tll_ptr consUU_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v3419; tll_ptr xs_v3420;
  switch(((tll_node)xs_v3417)->tag) {
    case 20:
      switch_ret_t183 = ys_v3418;
      break;
    case 21:
      x_v3419 = ((tll_node)xs_v3417)->data[0];
      xs_v3420 = ((tll_node)xs_v3417)->data[1];
      call_ret_t184 = appendUU_i37(0, xs_v3420, ys_v3418);
      instr_struct(&consUU_t185, 21, 2, x_v3419, call_ret_t184);
      switch_ret_t183 = consUU_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v3426, tll_env env)
{
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUU_i37(env[1], env[0], ys_v3426);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v3424, tll_env env)
{
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v3424, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v3421, tll_env env)
{
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v3421);
  return lam_clo_t190;
}

tll_ptr appendUL_i36(tll_ptr A_v3427, tll_ptr xs_v3428, tll_ptr ys_v3429)
{
  tll_ptr call_ret_t194; tll_ptr consUL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v3430; tll_ptr xs_v3431;
  switch(((tll_node)xs_v3428)->tag) {
    case 18:
      instr_free_struct(xs_v3428);
      switch_ret_t193 = ys_v3429;
      break;
    case 19:
      x_v3430 = ((tll_node)xs_v3428)->data[0];
      xs_v3431 = ((tll_node)xs_v3428)->data[1];
      instr_free_struct(xs_v3428);
      call_ret_t194 = appendUL_i36(0, xs_v3431, ys_v3429);
      instr_struct(&consUL_t195, 19, 2, x_v3430, call_ret_t194);
      switch_ret_t193 = consUL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v3437, tll_env env)
{
  tll_ptr call_ret_t196;
  call_ret_t196 = appendUL_i36(env[1], env[0], ys_v3437);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v3435, tll_env env)
{
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v3435, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v3432, tll_env env)
{
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v3432);
  return lam_clo_t200;
}

tll_ptr appendLL_i34(tll_ptr A_v3438, tll_ptr xs_v3439, tll_ptr ys_v3440)
{
  tll_ptr call_ret_t204; tll_ptr consLL_t205; tll_ptr switch_ret_t203;
  tll_ptr x_v3441; tll_ptr xs_v3442;
  switch(((tll_node)xs_v3439)->tag) {
    case 14:
      instr_free_struct(xs_v3439);
      switch_ret_t203 = ys_v3440;
      break;
    case 15:
      x_v3441 = ((tll_node)xs_v3439)->data[0];
      xs_v3442 = ((tll_node)xs_v3439)->data[1];
      instr_free_struct(xs_v3439);
      call_ret_t204 = appendLL_i34(0, xs_v3442, ys_v3440);
      instr_struct(&consLL_t205, 15, 2, x_v3441, call_ret_t204);
      switch_ret_t203 = consLL_t205;
      break;
  }
  return switch_ret_t203;
}

tll_ptr lam_fun_t207(tll_ptr ys_v3448, tll_env env)
{
  tll_ptr call_ret_t206;
  call_ret_t206 = appendLL_i34(env[1], env[0], ys_v3448);
  return call_ret_t206;
}

tll_ptr lam_fun_t209(tll_ptr xs_v3446, tll_env env)
{
  tll_ptr lam_clo_t208;
  instr_clo(&lam_clo_t208, &lam_fun_t207, 2, xs_v3446, env[0]);
  return lam_clo_t208;
}

tll_ptr lam_fun_t211(tll_ptr A_v3443, tll_env env)
{
  tll_ptr lam_clo_t210;
  instr_clo(&lam_clo_t210, &lam_fun_t209, 1, A_v3443);
  return lam_clo_t210;
}

tll_ptr lam_fun_t221(tll_ptr __v3465, tll_env env)
{
  tll_ptr __v3470; tll_ptr __v3471; tll_ptr ch_v3469; tll_ptr false_t219;
  tll_ptr send_ch_t218; tll_ptr tt_t220;
  instr_struct(&false_t219, 3, 0);
  instr_send(&send_ch_t218, env[0], false_t219);
  ch_v3469 = send_ch_t218;
  __v3471 = ch_v3469;
  instr_struct(&tt_t220, 1, 0);
  __v3470 = tt_t220;
  return env[1];
}

tll_ptr lam_fun_t224(tll_ptr __v3450, tll_env env)
{
  tll_ptr __v3462; tll_ptr app_ret_t223; tll_ptr ch_v3460; tll_ptr ch_v3461;
  tll_ptr ch_v3464; tll_ptr lam_clo_t222; tll_ptr prim_ch_t213;
  tll_ptr recv_msg_t216; tll_ptr s_v3463; tll_ptr send_ch_t214;
  tll_ptr switch_ret_t217; tll_ptr true_t215;
  instr_open(&prim_ch_t213, &proc_stdin);
  ch_v3460 = prim_ch_t213;
  instr_struct(&true_t215, 2, 0);
  instr_send(&send_ch_t214, ch_v3460, true_t215);
  ch_v3461 = send_ch_t214;
  instr_recv(&recv_msg_t216, ch_v3461);
  __v3462 = recv_msg_t216;
  switch(((tll_node)__v3462)->tag) {
    case 0:
      s_v3463 = ((tll_node)__v3462)->data[0];
      ch_v3464 = ((tll_node)__v3462)->data[1];
      instr_free_struct(__v3462);
      instr_clo(&lam_clo_t222, &lam_fun_t221, 2, ch_v3464, s_v3463);
      switch_ret_t217 = lam_clo_t222;
      break;
  }
  instr_app(&app_ret_t223, switch_ret_t217, 0);
  instr_free_clo(switch_ret_t217);
  return app_ret_t223;
}

tll_ptr readline_i25(tll_ptr __v3449)
{
  tll_ptr lam_clo_t225;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 0);
  return lam_clo_t225;
}

tll_ptr lam_fun_t227(tll_ptr __v3472, tll_env env)
{
  tll_ptr call_ret_t226;
  call_ret_t226 = readline_i25(__v3472);
  return call_ret_t226;
}

tll_ptr lam_fun_t236(tll_ptr __v3474, tll_env env)
{
  tll_ptr __v3484; tll_ptr ch_v3480; tll_ptr ch_v3481; tll_ptr ch_v3482;
  tll_ptr ch_v3483; tll_ptr false_t234; tll_ptr prim_ch_t229;
  tll_ptr send_ch_t230; tll_ptr send_ch_t232; tll_ptr send_ch_t233;
  tll_ptr true_t231; tll_ptr tt_t235;
  instr_open(&prim_ch_t229, &proc_stdout);
  ch_v3480 = prim_ch_t229;
  instr_struct(&true_t231, 2, 0);
  instr_send(&send_ch_t230, ch_v3480, true_t231);
  ch_v3481 = send_ch_t230;
  instr_send(&send_ch_t232, ch_v3481, env[0]);
  ch_v3482 = send_ch_t232;
  instr_struct(&false_t234, 3, 0);
  instr_send(&send_ch_t233, ch_v3482, false_t234);
  ch_v3483 = send_ch_t233;
  __v3484 = ch_v3483;
  instr_struct(&tt_t235, 1, 0);
  return tt_t235;
}

tll_ptr print_i26(tll_ptr s_v3473)
{
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, s_v3473);
  return lam_clo_t237;
}

tll_ptr lam_fun_t239(tll_ptr s_v3485, tll_env env)
{
  tll_ptr call_ret_t238;
  call_ret_t238 = print_i26(s_v3485);
  return call_ret_t238;
}

tll_ptr lam_fun_t248(tll_ptr __v3487, tll_env env)
{
  tll_ptr __v3497; tll_ptr ch_v3493; tll_ptr ch_v3494; tll_ptr ch_v3495;
  tll_ptr ch_v3496; tll_ptr false_t246; tll_ptr prim_ch_t241;
  tll_ptr send_ch_t242; tll_ptr send_ch_t244; tll_ptr send_ch_t245;
  tll_ptr true_t243; tll_ptr tt_t247;
  instr_open(&prim_ch_t241, &proc_stderr);
  ch_v3493 = prim_ch_t241;
  instr_struct(&true_t243, 2, 0);
  instr_send(&send_ch_t242, ch_v3493, true_t243);
  ch_v3494 = send_ch_t242;
  instr_send(&send_ch_t244, ch_v3494, env[0]);
  ch_v3495 = send_ch_t244;
  instr_struct(&false_t246, 3, 0);
  instr_send(&send_ch_t245, ch_v3495, false_t246);
  ch_v3496 = send_ch_t245;
  __v3497 = ch_v3496;
  instr_struct(&tt_t247, 1, 0);
  return tt_t247;
}

tll_ptr prerr_i27(tll_ptr s_v3486)
{
  tll_ptr lam_clo_t249;
  instr_clo(&lam_clo_t249, &lam_fun_t248, 1, s_v3486);
  return lam_clo_t249;
}

tll_ptr lam_fun_t251(tll_ptr s_v3498, tll_env env)
{
  tll_ptr call_ret_t250;
  call_ret_t250 = prerr_i27(s_v3498);
  return call_ret_t250;
}

tll_ptr lam_fun_t259(tll_ptr __v3523, tll_env env)
{
  tll_ptr app_ret_t258; tll_ptr c_v3525; tll_ptr call_ret_t257;
  tll_ptr send_ch_t256;
  instr_send(&send_ch_t256, env[0], env[1]);
  c_v3525 = send_ch_t256;
  call_ret_t257 = ref_handler_i29(0, env[1], c_v3525);
  instr_app(&app_ret_t258, call_ret_t257, 0);
  instr_free_clo(call_ret_t257);
  return app_ret_t258;
}

tll_ptr lam_fun_t261(tll_ptr c_v3520, tll_env env)
{
  tll_ptr lam_clo_t260;
  instr_clo(&lam_clo_t260, &lam_fun_t259, 2, c_v3520, env[0]);
  return lam_clo_t260;
}

tll_ptr lam_fun_t267(tll_ptr __v3531, tll_env env)
{
  tll_ptr __v3535; tll_ptr app_ret_t266; tll_ptr c_v3537;
  tll_ptr call_ret_t265; tll_ptr m_v3536; tll_ptr recv_msg_t263;
  tll_ptr switch_ret_t264;
  instr_recv(&recv_msg_t263, env[0]);
  __v3535 = recv_msg_t263;
  switch(((tll_node)__v3535)->tag) {
    case 0:
      m_v3536 = ((tll_node)__v3535)->data[0];
      c_v3537 = ((tll_node)__v3535)->data[1];
      instr_free_struct(__v3535);
      call_ret_t265 = ref_handler_i29(0, m_v3536, c_v3537);
      switch_ret_t264 = call_ret_t265;
      break;
  }
  instr_app(&app_ret_t266, switch_ret_t264, 0);
  instr_free_clo(switch_ret_t264);
  return app_ret_t266;
}

tll_ptr lam_fun_t269(tll_ptr c_v3526, tll_env env)
{
  tll_ptr lam_clo_t268;
  instr_clo(&lam_clo_t268, &lam_fun_t267, 1, c_v3526);
  return lam_clo_t268;
}

tll_ptr lam_fun_t272(tll_ptr __v3541, tll_env env)
{
  tll_ptr __v3543; tll_ptr tt_t271;
  __v3543 = env[0];
  instr_struct(&tt_t271, 1, 0);
  return tt_t271;
}

tll_ptr lam_fun_t274(tll_ptr c_v3538, tll_env env)
{
  tll_ptr lam_clo_t273;
  instr_clo(&lam_clo_t273, &lam_fun_t272, 1, c_v3538);
  return lam_clo_t273;
}

tll_ptr lam_fun_t278(tll_ptr __v3502, tll_env env)
{
  tll_ptr __v3517; tll_ptr app_ret_t276; tll_ptr app_ret_t277;
  tll_ptr c0_v3519; tll_ptr lam_clo_t262; tll_ptr lam_clo_t270;
  tll_ptr lam_clo_t275; tll_ptr msg_v3518; tll_ptr recv_msg_t253;
  tll_ptr switch_ret_t254; tll_ptr switch_ret_t255;
  instr_recv(&recv_msg_t253, env[0]);
  __v3517 = recv_msg_t253;
  switch(((tll_node)__v3517)->tag) {
    case 0:
      msg_v3518 = ((tll_node)__v3517)->data[0];
      c0_v3519 = ((tll_node)__v3517)->data[1];
      instr_free_struct(__v3517);
      switch(((tll_node)msg_v3518)->tag) {
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
      instr_app(&app_ret_t276, switch_ret_t255, c0_v3519);
      instr_free_clo(switch_ret_t255);
      switch_ret_t254 = app_ret_t276;
      break;
  }
  instr_app(&app_ret_t277, switch_ret_t254, 0);
  instr_free_clo(switch_ret_t254);
  return app_ret_t277;
}

tll_ptr ref_handler_i29(tll_ptr A_v3499, tll_ptr m_v3500, tll_ptr c0_v3501)
{
  tll_ptr lam_clo_t279;
  instr_clo(&lam_clo_t279, &lam_fun_t278, 2, c0_v3501, m_v3500);
  return lam_clo_t279;
}

tll_ptr lam_fun_t281(tll_ptr c0_v3549, tll_env env)
{
  tll_ptr call_ret_t280;
  call_ret_t280 = ref_handler_i29(env[1], env[0], c0_v3549);
  return call_ret_t280;
}

tll_ptr lam_fun_t283(tll_ptr m_v3547, tll_env env)
{
  tll_ptr lam_clo_t282;
  instr_clo(&lam_clo_t282, &lam_fun_t281, 2, m_v3547, env[0]);
  return lam_clo_t282;
}

tll_ptr lam_fun_t285(tll_ptr A_v3544, tll_env env)
{
  tll_ptr lam_clo_t284;
  instr_clo(&lam_clo_t284, &lam_fun_t283, 1, A_v3544);
  return lam_clo_t284;
}

int main()
{
  instr_init();
  tll_ptr lam_clo_t106; tll_ptr lam_clo_t117; tll_ptr lam_clo_t125;
  tll_ptr lam_clo_t133; tll_ptr lam_clo_t14; tll_ptr lam_clo_t140;
  tll_ptr lam_clo_t154; tll_ptr lam_clo_t168; tll_ptr lam_clo_t182;
  tll_ptr lam_clo_t192; tll_ptr lam_clo_t20; tll_ptr lam_clo_t202;
  tll_ptr lam_clo_t212; tll_ptr lam_clo_t228; tll_ptr lam_clo_t240;
  tll_ptr lam_clo_t252; tll_ptr lam_clo_t286; tll_ptr lam_clo_t30;
  tll_ptr lam_clo_t42; tll_ptr lam_clo_t54; tll_ptr lam_clo_t64;
  tll_ptr lam_clo_t7; tll_ptr lam_clo_t76; tll_ptr lam_clo_t81;
  tll_ptr lam_clo_t89; tll_ptr lam_clo_t97;
  instr_clo(&lam_clo_t7, &lam_fun_t6, 0);
  andbclo_i38 = lam_clo_t7;
  instr_clo(&lam_clo_t14, &lam_fun_t13, 0);
  orbclo_i39 = lam_clo_t14;
  instr_clo(&lam_clo_t20, &lam_fun_t19, 0);
  notbclo_i40 = lam_clo_t20;
  instr_clo(&lam_clo_t30, &lam_fun_t29, 0);
  ltenclo_i41 = lam_clo_t30;
  instr_clo(&lam_clo_t42, &lam_fun_t41, 0);
  gtenclo_i42 = lam_clo_t42;
  instr_clo(&lam_clo_t54, &lam_fun_t53, 0);
  ltnclo_i43 = lam_clo_t54;
  instr_clo(&lam_clo_t64, &lam_fun_t63, 0);
  gtnclo_i44 = lam_clo_t64;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 0);
  eqnclo_i45 = lam_clo_t76;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 0);
  predclo_i46 = lam_clo_t81;
  instr_clo(&lam_clo_t89, &lam_fun_t88, 0);
  addnclo_i47 = lam_clo_t89;
  instr_clo(&lam_clo_t97, &lam_fun_t96, 0);
  subnclo_i48 = lam_clo_t97;
  instr_clo(&lam_clo_t106, &lam_fun_t105, 0);
  mulnclo_i49 = lam_clo_t106;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 0);
  divnclo_i50 = lam_clo_t117;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 0);
  modnclo_i51 = lam_clo_t125;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 0);
  catsclo_i52 = lam_clo_t133;
  instr_clo(&lam_clo_t140, &lam_fun_t139, 0);
  strlenclo_i53 = lam_clo_t140;
  instr_clo(&lam_clo_t154, &lam_fun_t153, 0);
  lenUUclo_i54 = lam_clo_t154;
  instr_clo(&lam_clo_t168, &lam_fun_t167, 0);
  lenULclo_i55 = lam_clo_t168;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 0);
  lenLLclo_i56 = lam_clo_t182;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 0);
  appendUUclo_i57 = lam_clo_t192;
  instr_clo(&lam_clo_t202, &lam_fun_t201, 0);
  appendULclo_i58 = lam_clo_t202;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  appendLLclo_i59 = lam_clo_t212;
  instr_clo(&lam_clo_t228, &lam_fun_t227, 0);
  readlineclo_i60 = lam_clo_t228;
  instr_clo(&lam_clo_t240, &lam_fun_t239, 0);
  printclo_i61 = lam_clo_t240;
  instr_clo(&lam_clo_t252, &lam_fun_t251, 0);
  prerrclo_i62 = lam_clo_t252;
  instr_clo(&lam_clo_t286, &lam_fun_t285, 0);
  ref_handlerclo_i63 = lam_clo_t286;
  return 0;
}

