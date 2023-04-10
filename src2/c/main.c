#include "runtime.h"

tll_ptr addnclo_i84;
tll_ptr andbclo_i81;
tll_ptr appendLLclo_i102;
tll_ptr appendLLclo_i96;
tll_ptr appendULclo_i101;
tll_ptr appendULclo_i95;
tll_ptr appendUUclo_i100;
tll_ptr appendUUclo_i94;
tll_ptr catsclo_i89;
tll_ptr eqnclo_i86;
tll_ptr gtenclo_i88;
tll_ptr idLclo_i104;
tll_ptr idUclo_i103;
tll_ptr lenLLclo_i93;
tll_ptr lenULclo_i92;
tll_ptr lenUUclo_i91;
tll_ptr ls0_i76;
tll_ptr ls1_i77;
tll_ptr ls2_i78;
tll_ptr ltenclo_i87;
tll_ptr mulnclo_i85;
tll_ptr notbclo_i83;
tll_ptr orbclo_i82;
tll_ptr prerrclo_i99;
tll_ptr printclo_i98;
tll_ptr readlineclo_i97;
tll_ptr strlenclo_i90;

tll_ptr andb_i33(tll_ptr b1_v3289, tll_ptr b2_v3290)
{
  tll_ptr false_t2; tll_ptr switch_ret_t1;
  switch(((tll_node)b1_v3289)->tag) {
    case 14:
      switch_ret_t1 = b2_v3290;
      break;
    case 15:
      instr_struct(&false_t2, 15, 0);
      switch_ret_t1 = false_t2;
      break;
  }
  return switch_ret_t1;
}

tll_ptr lam_fun_t4(tll_ptr b2_v3293, tll_env env)
{
  tll_ptr call_ret_t3;
  call_ret_t3 = andb_i33(env[0], b2_v3293);
  return call_ret_t3;
}

tll_ptr lam_fun_t6(tll_ptr b1_v3291, tll_env env)
{
  tll_ptr lam_clo_t5;
  instr_clo(&lam_clo_t5, &lam_fun_t4, 1, b1_v3291);
  return lam_clo_t5;
}

tll_ptr orb_i34(tll_ptr b1_v3294, tll_ptr b2_v3295)
{
  tll_ptr switch_ret_t8; tll_ptr true_t9;
  switch(((tll_node)b1_v3294)->tag) {
    case 14:
      instr_struct(&true_t9, 14, 0);
      switch_ret_t8 = true_t9;
      break;
    case 15:
      switch_ret_t8 = b2_v3295;
      break;
  }
  return switch_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b2_v3298, tll_env env)
{
  tll_ptr call_ret_t10;
  call_ret_t10 = orb_i34(env[0], b2_v3298);
  return call_ret_t10;
}

tll_ptr lam_fun_t13(tll_ptr b1_v3296, tll_env env)
{
  tll_ptr lam_clo_t12;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 1, b1_v3296);
  return lam_clo_t12;
}

tll_ptr notb_i35(tll_ptr b_v3299)
{
  tll_ptr false_t16; tll_ptr switch_ret_t15; tll_ptr true_t17;
  switch(((tll_node)b_v3299)->tag) {
    case 14:
      instr_struct(&false_t16, 15, 0);
      switch_ret_t15 = false_t16;
      break;
    case 15:
      instr_struct(&true_t17, 14, 0);
      switch_ret_t15 = true_t17;
      break;
  }
  return switch_ret_t15;
}

tll_ptr lam_fun_t19(tll_ptr b_v3300, tll_env env)
{
  tll_ptr call_ret_t18;
  call_ret_t18 = notb_i35(b_v3300);
  return call_ret_t18;
}

tll_ptr addn_i36(tll_ptr x_v3301, tll_ptr y_v3302)
{
  tll_ptr S_t23; tll_ptr call_ret_t22; tll_ptr switch_ret_t21;
  tll_ptr x_v3303;
  switch(((tll_node)x_v3301)->tag) {
    case 16:
      switch_ret_t21 = y_v3302;
      break;
    case 17:
      x_v3303 = ((tll_node)x_v3301)->data[0];
      call_ret_t22 = addn_i36(x_v3303, y_v3302);
      instr_struct(&S_t23, 17, 1, call_ret_t22);
      switch_ret_t21 = S_t23;
      break;
  }
  return switch_ret_t21;
}

tll_ptr lam_fun_t25(tll_ptr y_v3306, tll_env env)
{
  tll_ptr call_ret_t24;
  call_ret_t24 = addn_i36(env[0], y_v3306);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr x_v3304, tll_env env)
{
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, x_v3304);
  return lam_clo_t26;
}

tll_ptr muln_i37(tll_ptr x_v3307, tll_ptr y_v3308)
{
  tll_ptr call_ret_t30; tll_ptr call_ret_t31; tll_ptr switch_ret_t29;
  tll_ptr x_v3309;
  switch(((tll_node)x_v3307)->tag) {
    case 16:
      switch_ret_t29 = y_v3308;
      break;
    case 17:
      x_v3309 = ((tll_node)x_v3307)->data[0];
      call_ret_t31 = muln_i37(x_v3309, y_v3308);
      call_ret_t30 = addn_i36(y_v3308, call_ret_t31);
      switch_ret_t29 = call_ret_t30;
      break;
  }
  return switch_ret_t29;
}

tll_ptr lam_fun_t33(tll_ptr y_v3312, tll_env env)
{
  tll_ptr call_ret_t32;
  call_ret_t32 = muln_i37(env[0], y_v3312);
  return call_ret_t32;
}

tll_ptr lam_fun_t35(tll_ptr x_v3310, tll_env env)
{
  tll_ptr lam_clo_t34;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 1, x_v3310);
  return lam_clo_t34;
}

tll_ptr eqn_i38(tll_ptr x_v3313, tll_ptr y_v3314)
{
  tll_ptr __v3315; tll_ptr call_ret_t43; tll_ptr false_t40;
  tll_ptr false_t42; tll_ptr switch_ret_t37; tll_ptr switch_ret_t38;
  tll_ptr switch_ret_t41; tll_ptr true_t39; tll_ptr x_v3316; tll_ptr y_v3317;
  switch(((tll_node)x_v3313)->tag) {
    case 16:
      switch(((tll_node)y_v3314)->tag) {
        case 16:
          instr_struct(&true_t39, 14, 0);
          switch_ret_t38 = true_t39;
          break;
        case 17:
          __v3315 = ((tll_node)y_v3314)->data[0];
          instr_struct(&false_t40, 15, 0);
          switch_ret_t38 = false_t40;
          break;
      }
      switch_ret_t37 = switch_ret_t38;
      break;
    case 17:
      x_v3316 = ((tll_node)x_v3313)->data[0];
      switch(((tll_node)y_v3314)->tag) {
        case 16:
          instr_struct(&false_t42, 15, 0);
          switch_ret_t41 = false_t42;
          break;
        case 17:
          y_v3317 = ((tll_node)y_v3314)->data[0];
          call_ret_t43 = eqn_i38(x_v3316, y_v3317);
          switch_ret_t41 = call_ret_t43;
          break;
      }
      switch_ret_t37 = switch_ret_t41;
      break;
  }
  return switch_ret_t37;
}

tll_ptr lam_fun_t45(tll_ptr y_v3320, tll_env env)
{
  tll_ptr call_ret_t44;
  call_ret_t44 = eqn_i38(env[0], y_v3320);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v3318, tll_env env)
{
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v3318);
  return lam_clo_t46;
}

tll_ptr lten_i39(tll_ptr x_v3321, tll_ptr y_v3322)
{
  tll_ptr call_ret_t53; tll_ptr false_t52; tll_ptr switch_ret_t49;
  tll_ptr switch_ret_t51; tll_ptr true_t50; tll_ptr x_v3323; tll_ptr y_v3324;
  switch(((tll_node)x_v3321)->tag) {
    case 16:
      instr_struct(&true_t50, 14, 0);
      switch_ret_t49 = true_t50;
      break;
    case 17:
      x_v3323 = ((tll_node)x_v3321)->data[0];
      switch(((tll_node)y_v3322)->tag) {
        case 16:
          instr_struct(&false_t52, 15, 0);
          switch_ret_t51 = false_t52;
          break;
        case 17:
          y_v3324 = ((tll_node)y_v3322)->data[0];
          call_ret_t53 = lten_i39(x_v3323, y_v3324);
          switch_ret_t51 = call_ret_t53;
          break;
      }
      switch_ret_t49 = switch_ret_t51;
      break;
  }
  return switch_ret_t49;
}

tll_ptr lam_fun_t55(tll_ptr y_v3327, tll_env env)
{
  tll_ptr call_ret_t54;
  call_ret_t54 = lten_i39(env[0], y_v3327);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v3325, tll_env env)
{
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v3325);
  return lam_clo_t56;
}

tll_ptr gten_i40(tll_ptr x_v3328, tll_ptr y_v3329)
{
  tll_ptr __v3330; tll_ptr call_ret_t65; tll_ptr false_t62;
  tll_ptr switch_ret_t59; tll_ptr switch_ret_t60; tll_ptr switch_ret_t63;
  tll_ptr true_t61; tll_ptr true_t64; tll_ptr x_v3331; tll_ptr y_v3332;
  switch(((tll_node)x_v3328)->tag) {
    case 16:
      switch(((tll_node)y_v3329)->tag) {
        case 16:
          instr_struct(&true_t61, 14, 0);
          switch_ret_t60 = true_t61;
          break;
        case 17:
          __v3330 = ((tll_node)y_v3329)->data[0];
          instr_struct(&false_t62, 15, 0);
          switch_ret_t60 = false_t62;
          break;
      }
      switch_ret_t59 = switch_ret_t60;
      break;
    case 17:
      x_v3331 = ((tll_node)x_v3328)->data[0];
      switch(((tll_node)y_v3329)->tag) {
        case 16:
          instr_struct(&true_t64, 14, 0);
          switch_ret_t63 = true_t64;
          break;
        case 17:
          y_v3332 = ((tll_node)y_v3329)->data[0];
          call_ret_t65 = gten_i40(x_v3331, y_v3332);
          switch_ret_t63 = call_ret_t65;
          break;
      }
      switch_ret_t59 = switch_ret_t63;
      break;
  }
  return switch_ret_t59;
}

tll_ptr lam_fun_t67(tll_ptr y_v3335, tll_env env)
{
  tll_ptr call_ret_t66;
  call_ret_t66 = gten_i40(env[0], y_v3335);
  return call_ret_t66;
}

tll_ptr lam_fun_t69(tll_ptr x_v3333, tll_env env)
{
  tll_ptr lam_clo_t68;
  instr_clo(&lam_clo_t68, &lam_fun_t67, 1, x_v3333);
  return lam_clo_t68;
}

tll_ptr cats_i43(tll_ptr s1_v3336, tll_ptr s2_v3337)
{
  tll_ptr String_t73; tll_ptr c_v3338; tll_ptr call_ret_t72;
  tll_ptr s1_v3339; tll_ptr switch_ret_t71;
  switch(((tll_node)s1_v3336)->tag) {
    case 19:
      switch_ret_t71 = s2_v3337;
      break;
    case 20:
      c_v3338 = ((tll_node)s1_v3336)->data[0];
      s1_v3339 = ((tll_node)s1_v3336)->data[1];
      call_ret_t72 = cats_i43(s1_v3339, s2_v3337);
      instr_struct(&String_t73, 20, 2, c_v3338, call_ret_t72);
      switch_ret_t71 = String_t73;
      break;
  }
  return switch_ret_t71;
}

tll_ptr lam_fun_t75(tll_ptr s2_v3342, tll_env env)
{
  tll_ptr call_ret_t74;
  call_ret_t74 = cats_i43(env[0], s2_v3342);
  return call_ret_t74;
}

tll_ptr lam_fun_t77(tll_ptr s1_v3340, tll_env env)
{
  tll_ptr lam_clo_t76;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 1, s1_v3340);
  return lam_clo_t76;
}

tll_ptr strlen_i44(tll_ptr s_v3343)
{
  tll_ptr O_t80; tll_ptr S_t82; tll_ptr __v3344; tll_ptr call_ret_t81;
  tll_ptr s_v3345; tll_ptr switch_ret_t79;
  switch(((tll_node)s_v3343)->tag) {
    case 19:
      instr_struct(&O_t80, 16, 0);
      switch_ret_t79 = O_t80;
      break;
    case 20:
      __v3344 = ((tll_node)s_v3343)->data[0];
      s_v3345 = ((tll_node)s_v3343)->data[1];
      call_ret_t81 = strlen_i44(s_v3345);
      instr_struct(&S_t82, 17, 1, call_ret_t81);
      switch_ret_t79 = S_t82;
      break;
  }
  return switch_ret_t79;
}

tll_ptr lam_fun_t84(tll_ptr s_v3346, tll_env env)
{
  tll_ptr call_ret_t83;
  call_ret_t83 = strlen_i44(s_v3346);
  return call_ret_t83;
}

tll_ptr lenUU_i48(tll_ptr A_v3347, tll_ptr xs_v3348)
{
  tll_ptr O_t87; tll_ptr S_t92; tll_ptr call_ret_t90; tll_ptr consUU_t93;
  tll_ptr n_v3351; tll_ptr nilUU_t88; tll_ptr pair_struct_t89;
  tll_ptr pair_struct_t94; tll_ptr switch_ret_t86; tll_ptr switch_ret_t91;
  tll_ptr x_v3349; tll_ptr xs_v3350; tll_ptr xs_v3352;
  switch(((tll_node)xs_v3348)->tag) {
    case 27:
      instr_struct(&O_t87, 16, 0);
      instr_struct(&nilUU_t88, 27, 0);
      instr_struct(&pair_struct_t89, 0, 2, O_t87, nilUU_t88);
      switch_ret_t86 = pair_struct_t89;
      break;
    case 28:
      x_v3349 = ((tll_node)xs_v3348)->data[0];
      xs_v3350 = ((tll_node)xs_v3348)->data[1];
      call_ret_t90 = lenUU_i48(0, xs_v3350);
      switch(((tll_node)call_ret_t90)->tag) {
        case 0:
          n_v3351 = ((tll_node)call_ret_t90)->data[0];
          xs_v3352 = ((tll_node)call_ret_t90)->data[1];
          instr_free_struct(call_ret_t90);
          instr_struct(&S_t92, 17, 1, n_v3351);
          instr_struct(&consUU_t93, 28, 2, x_v3349, xs_v3352);
          instr_struct(&pair_struct_t94, 0, 2, S_t92, consUU_t93);
          switch_ret_t91 = pair_struct_t94;
          break;
      }
      switch_ret_t86 = switch_ret_t91;
      break;
  }
  return switch_ret_t86;
}

tll_ptr lam_fun_t96(tll_ptr xs_v3355, tll_env env)
{
  tll_ptr call_ret_t95;
  call_ret_t95 = lenUU_i48(env[0], xs_v3355);
  return call_ret_t95;
}

tll_ptr lam_fun_t98(tll_ptr A_v3353, tll_env env)
{
  tll_ptr lam_clo_t97;
  instr_clo(&lam_clo_t97, &lam_fun_t96, 1, A_v3353);
  return lam_clo_t97;
}

tll_ptr lenUL_i47(tll_ptr A_v3356, tll_ptr xs_v3357)
{
  tll_ptr O_t101; tll_ptr S_t106; tll_ptr call_ret_t104; tll_ptr consUL_t107;
  tll_ptr n_v3360; tll_ptr nilUL_t102; tll_ptr pair_struct_t103;
  tll_ptr pair_struct_t108; tll_ptr switch_ret_t100; tll_ptr switch_ret_t105;
  tll_ptr x_v3358; tll_ptr xs_v3359; tll_ptr xs_v3361;
  switch(((tll_node)xs_v3357)->tag) {
    case 25:
      instr_free_struct(xs_v3357);
      instr_struct(&O_t101, 16, 0);
      instr_struct(&nilUL_t102, 25, 0);
      instr_struct(&pair_struct_t103, 0, 2, O_t101, nilUL_t102);
      switch_ret_t100 = pair_struct_t103;
      break;
    case 26:
      x_v3358 = ((tll_node)xs_v3357)->data[0];
      xs_v3359 = ((tll_node)xs_v3357)->data[1];
      instr_free_struct(xs_v3357);
      call_ret_t104 = lenUL_i47(0, xs_v3359);
      switch(((tll_node)call_ret_t104)->tag) {
        case 0:
          n_v3360 = ((tll_node)call_ret_t104)->data[0];
          xs_v3361 = ((tll_node)call_ret_t104)->data[1];
          instr_free_struct(call_ret_t104);
          instr_struct(&S_t106, 17, 1, n_v3360);
          instr_struct(&consUL_t107, 26, 2, x_v3358, xs_v3361);
          instr_struct(&pair_struct_t108, 0, 2, S_t106, consUL_t107);
          switch_ret_t105 = pair_struct_t108;
          break;
      }
      switch_ret_t100 = switch_ret_t105;
      break;
  }
  return switch_ret_t100;
}

tll_ptr lam_fun_t110(tll_ptr xs_v3364, tll_env env)
{
  tll_ptr call_ret_t109;
  call_ret_t109 = lenUL_i47(env[0], xs_v3364);
  return call_ret_t109;
}

tll_ptr lam_fun_t112(tll_ptr A_v3362, tll_env env)
{
  tll_ptr lam_clo_t111;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 1, A_v3362);
  return lam_clo_t111;
}

tll_ptr lenLL_i45(tll_ptr A_v3365, tll_ptr xs_v3366)
{
  tll_ptr O_t115; tll_ptr S_t120; tll_ptr call_ret_t118; tll_ptr consLL_t121;
  tll_ptr n_v3369; tll_ptr nilLL_t116; tll_ptr pair_struct_t117;
  tll_ptr pair_struct_t122; tll_ptr switch_ret_t114; tll_ptr switch_ret_t119;
  tll_ptr x_v3367; tll_ptr xs_v3368; tll_ptr xs_v3370;
  switch(((tll_node)xs_v3366)->tag) {
    case 21:
      instr_free_struct(xs_v3366);
      instr_struct(&O_t115, 16, 0);
      instr_struct(&nilLL_t116, 21, 0);
      instr_struct(&pair_struct_t117, 0, 2, O_t115, nilLL_t116);
      switch_ret_t114 = pair_struct_t117;
      break;
    case 22:
      x_v3367 = ((tll_node)xs_v3366)->data[0];
      xs_v3368 = ((tll_node)xs_v3366)->data[1];
      instr_free_struct(xs_v3366);
      call_ret_t118 = lenLL_i45(0, xs_v3368);
      switch(((tll_node)call_ret_t118)->tag) {
        case 0:
          n_v3369 = ((tll_node)call_ret_t118)->data[0];
          xs_v3370 = ((tll_node)call_ret_t118)->data[1];
          instr_free_struct(call_ret_t118);
          instr_struct(&S_t120, 17, 1, n_v3369);
          instr_struct(&consLL_t121, 22, 2, x_v3367, xs_v3370);
          instr_struct(&pair_struct_t122, 0, 2, S_t120, consLL_t121);
          switch_ret_t119 = pair_struct_t122;
          break;
      }
      switch_ret_t114 = switch_ret_t119;
      break;
  }
  return switch_ret_t114;
}

tll_ptr lam_fun_t124(tll_ptr xs_v3373, tll_env env)
{
  tll_ptr call_ret_t123;
  call_ret_t123 = lenLL_i45(env[0], xs_v3373);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr A_v3371, tll_env env)
{
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, A_v3371);
  return lam_clo_t125;
}

tll_ptr appendUU_i52(tll_ptr A_v3374, tll_ptr xs_v3375, tll_ptr ys_v3376)
{
  tll_ptr call_ret_t129; tll_ptr consUU_t130; tll_ptr switch_ret_t128;
  tll_ptr x_v3377; tll_ptr xs_v3378;
  switch(((tll_node)xs_v3375)->tag) {
    case 27:
      switch_ret_t128 = ys_v3376;
      break;
    case 28:
      x_v3377 = ((tll_node)xs_v3375)->data[0];
      xs_v3378 = ((tll_node)xs_v3375)->data[1];
      call_ret_t129 = appendUU_i52(0, xs_v3378, ys_v3376);
      instr_struct(&consUU_t130, 28, 2, x_v3377, call_ret_t129);
      switch_ret_t128 = consUU_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr ys_v3384, tll_env env)
{
  tll_ptr call_ret_t131;
  call_ret_t131 = appendUU_i52(env[1], env[0], ys_v3384);
  return call_ret_t131;
}

tll_ptr lam_fun_t134(tll_ptr xs_v3382, tll_env env)
{
  tll_ptr lam_clo_t133;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 2, xs_v3382, env[0]);
  return lam_clo_t133;
}

tll_ptr lam_fun_t136(tll_ptr A_v3379, tll_env env)
{
  tll_ptr lam_clo_t135;
  instr_clo(&lam_clo_t135, &lam_fun_t134, 1, A_v3379);
  return lam_clo_t135;
}

tll_ptr appendUL_i51(tll_ptr A_v3385, tll_ptr xs_v3386, tll_ptr ys_v3387)
{
  tll_ptr call_ret_t139; tll_ptr consUL_t140; tll_ptr switch_ret_t138;
  tll_ptr x_v3388; tll_ptr xs_v3389;
  switch(((tll_node)xs_v3386)->tag) {
    case 25:
      instr_free_struct(xs_v3386);
      switch_ret_t138 = ys_v3387;
      break;
    case 26:
      x_v3388 = ((tll_node)xs_v3386)->data[0];
      xs_v3389 = ((tll_node)xs_v3386)->data[1];
      instr_free_struct(xs_v3386);
      call_ret_t139 = appendUL_i51(0, xs_v3389, ys_v3387);
      instr_struct(&consUL_t140, 26, 2, x_v3388, call_ret_t139);
      switch_ret_t138 = consUL_t140;
      break;
  }
  return switch_ret_t138;
}

tll_ptr lam_fun_t142(tll_ptr ys_v3395, tll_env env)
{
  tll_ptr call_ret_t141;
  call_ret_t141 = appendUL_i51(env[1], env[0], ys_v3395);
  return call_ret_t141;
}

tll_ptr lam_fun_t144(tll_ptr xs_v3393, tll_env env)
{
  tll_ptr lam_clo_t143;
  instr_clo(&lam_clo_t143, &lam_fun_t142, 2, xs_v3393, env[0]);
  return lam_clo_t143;
}

tll_ptr lam_fun_t146(tll_ptr A_v3390, tll_env env)
{
  tll_ptr lam_clo_t145;
  instr_clo(&lam_clo_t145, &lam_fun_t144, 1, A_v3390);
  return lam_clo_t145;
}

tll_ptr appendLL_i49(tll_ptr A_v3396, tll_ptr xs_v3397, tll_ptr ys_v3398)
{
  tll_ptr call_ret_t149; tll_ptr consLL_t150; tll_ptr switch_ret_t148;
  tll_ptr x_v3399; tll_ptr xs_v3400;
  switch(((tll_node)xs_v3397)->tag) {
    case 21:
      instr_free_struct(xs_v3397);
      switch_ret_t148 = ys_v3398;
      break;
    case 22:
      x_v3399 = ((tll_node)xs_v3397)->data[0];
      xs_v3400 = ((tll_node)xs_v3397)->data[1];
      instr_free_struct(xs_v3397);
      call_ret_t149 = appendLL_i49(0, xs_v3400, ys_v3398);
      instr_struct(&consLL_t150, 22, 2, x_v3399, call_ret_t149);
      switch_ret_t148 = consLL_t150;
      break;
  }
  return switch_ret_t148;
}

tll_ptr lam_fun_t152(tll_ptr ys_v3406, tll_env env)
{
  tll_ptr call_ret_t151;
  call_ret_t151 = appendLL_i49(env[1], env[0], ys_v3406);
  return call_ret_t151;
}

tll_ptr lam_fun_t154(tll_ptr xs_v3404, tll_env env)
{
  tll_ptr lam_clo_t153;
  instr_clo(&lam_clo_t153, &lam_fun_t152, 2, xs_v3404, env[0]);
  return lam_clo_t153;
}

tll_ptr lam_fun_t156(tll_ptr A_v3401, tll_env env)
{
  tll_ptr lam_clo_t155;
  instr_clo(&lam_clo_t155, &lam_fun_t154, 1, A_v3401);
  return lam_clo_t155;
}

tll_ptr lam_fun_t166(tll_ptr __v3423, tll_env env)
{
  tll_ptr __v3428; tll_ptr __v3429; tll_ptr ch_v3427; tll_ptr false_t164;
  tll_ptr send_ch_t163; tll_ptr tt_t165;
  instr_struct(&false_t164, 15, 0);
  instr_send(&send_ch_t163, env[0], false_t164);
  ch_v3427 = send_ch_t163;
  __v3429 = ch_v3427;
  instr_struct(&tt_t165, 13, 0);
  __v3428 = tt_t165;
  return env[1];
}

tll_ptr lam_fun_t169(tll_ptr __v3408, tll_env env)
{
  tll_ptr __v3420; tll_ptr app_ret_t168; tll_ptr ch_v3418; tll_ptr ch_v3419;
  tll_ptr ch_v3422; tll_ptr lam_clo_t167; tll_ptr prim_ch_t158;
  tll_ptr recv_msg_t161; tll_ptr s_v3421; tll_ptr send_ch_t159;
  tll_ptr switch_ret_t162; tll_ptr true_t160;
  instr_open(&prim_ch_t158, &proc_stdin);
  ch_v3418 = prim_ch_t158;
  instr_struct(&true_t160, 14, 0);
  instr_send(&send_ch_t159, ch_v3418, true_t160);
  ch_v3419 = send_ch_t159;
  instr_recv(&recv_msg_t161, ch_v3419);
  __v3420 = recv_msg_t161;
  switch(((tll_node)__v3420)->tag) {
    case 0:
      s_v3421 = ((tll_node)__v3420)->data[0];
      ch_v3422 = ((tll_node)__v3420)->data[1];
      instr_free_struct(__v3420);
      instr_clo(&lam_clo_t167, &lam_fun_t166, 2, ch_v3422, s_v3421);
      switch_ret_t162 = lam_clo_t167;
      break;
  }
  instr_app(&app_ret_t168, switch_ret_t162, 0);
  instr_free_clo(switch_ret_t162);
  return app_ret_t168;
}

tll_ptr readline_i59(tll_ptr __v3407)
{
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 0);
  return lam_clo_t170;
}

tll_ptr lam_fun_t172(tll_ptr __v3430, tll_env env)
{
  tll_ptr call_ret_t171;
  call_ret_t171 = readline_i59(__v3430);
  return call_ret_t171;
}

tll_ptr lam_fun_t181(tll_ptr __v3432, tll_env env)
{
  tll_ptr __v3442; tll_ptr ch_v3438; tll_ptr ch_v3439; tll_ptr ch_v3440;
  tll_ptr ch_v3441; tll_ptr false_t179; tll_ptr prim_ch_t174;
  tll_ptr send_ch_t175; tll_ptr send_ch_t177; tll_ptr send_ch_t178;
  tll_ptr true_t176; tll_ptr tt_t180;
  instr_open(&prim_ch_t174, &proc_stdout);
  ch_v3438 = prim_ch_t174;
  instr_struct(&true_t176, 14, 0);
  instr_send(&send_ch_t175, ch_v3438, true_t176);
  ch_v3439 = send_ch_t175;
  instr_send(&send_ch_t177, ch_v3439, env[0]);
  ch_v3440 = send_ch_t177;
  instr_struct(&false_t179, 15, 0);
  instr_send(&send_ch_t178, ch_v3440, false_t179);
  ch_v3441 = send_ch_t178;
  __v3442 = ch_v3441;
  instr_struct(&tt_t180, 13, 0);
  return tt_t180;
}

tll_ptr print_i60(tll_ptr s_v3431)
{
  tll_ptr lam_clo_t182;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 1, s_v3431);
  return lam_clo_t182;
}

tll_ptr lam_fun_t184(tll_ptr s_v3443, tll_env env)
{
  tll_ptr call_ret_t183;
  call_ret_t183 = print_i60(s_v3443);
  return call_ret_t183;
}

tll_ptr lam_fun_t193(tll_ptr __v3445, tll_env env)
{
  tll_ptr __v3455; tll_ptr ch_v3451; tll_ptr ch_v3452; tll_ptr ch_v3453;
  tll_ptr ch_v3454; tll_ptr false_t191; tll_ptr prim_ch_t186;
  tll_ptr send_ch_t187; tll_ptr send_ch_t189; tll_ptr send_ch_t190;
  tll_ptr true_t188; tll_ptr tt_t192;
  instr_open(&prim_ch_t186, &proc_stderr);
  ch_v3451 = prim_ch_t186;
  instr_struct(&true_t188, 14, 0);
  instr_send(&send_ch_t187, ch_v3451, true_t188);
  ch_v3452 = send_ch_t187;
  instr_send(&send_ch_t189, ch_v3452, env[0]);
  ch_v3453 = send_ch_t189;
  instr_struct(&false_t191, 15, 0);
  instr_send(&send_ch_t190, ch_v3453, false_t191);
  ch_v3454 = send_ch_t190;
  __v3455 = ch_v3454;
  instr_struct(&tt_t192, 13, 0);
  return tt_t192;
}

tll_ptr prerr_i61(tll_ptr s_v3444)
{
  tll_ptr lam_clo_t194;
  instr_clo(&lam_clo_t194, &lam_fun_t193, 1, s_v3444);
  return lam_clo_t194;
}

tll_ptr lam_fun_t196(tll_ptr s_v3456, tll_env env)
{
  tll_ptr call_ret_t195;
  call_ret_t195 = prerr_i61(s_v3456);
  return call_ret_t195;
}

tll_ptr appendUU_i69(tll_ptr A_v3457, tll_ptr xs_v3458, tll_ptr ys_v3459)
{
  tll_ptr ConsUU_t200; tll_ptr call_ret_t199; tll_ptr switch_ret_t198;
  tll_ptr x_v3460; tll_ptr xs_v3461;
  switch(((tll_node)xs_v3458)->tag) {
    case 35:
      switch_ret_t198 = ys_v3459;
      break;
    case 36:
      x_v3460 = ((tll_node)xs_v3458)->data[0];
      xs_v3461 = ((tll_node)xs_v3458)->data[1];
      call_ret_t199 = appendUU_i69(0, xs_v3461, ys_v3459);
      instr_struct(&ConsUU_t200, 36, 2, x_v3460, call_ret_t199);
      switch_ret_t198 = ConsUU_t200;
      break;
  }
  return switch_ret_t198;
}

tll_ptr lam_fun_t202(tll_ptr ys_v3467, tll_env env)
{
  tll_ptr call_ret_t201;
  call_ret_t201 = appendUU_i69(env[1], env[0], ys_v3467);
  return call_ret_t201;
}

tll_ptr lam_fun_t204(tll_ptr xs_v3465, tll_env env)
{
  tll_ptr lam_clo_t203;
  instr_clo(&lam_clo_t203, &lam_fun_t202, 2, xs_v3465, env[0]);
  return lam_clo_t203;
}

tll_ptr lam_fun_t206(tll_ptr A_v3462, tll_env env)
{
  tll_ptr lam_clo_t205;
  instr_clo(&lam_clo_t205, &lam_fun_t204, 1, A_v3462);
  return lam_clo_t205;
}

tll_ptr appendUL_i68(tll_ptr A_v3468, tll_ptr xs_v3469, tll_ptr ys_v3470)
{
  tll_ptr ConsUL_t210; tll_ptr call_ret_t209; tll_ptr switch_ret_t208;
  tll_ptr x_v3471; tll_ptr xs_v3472;
  switch(((tll_node)xs_v3469)->tag) {
    case 33:
      instr_free_struct(xs_v3469);
      switch_ret_t208 = ys_v3470;
      break;
    case 34:
      x_v3471 = ((tll_node)xs_v3469)->data[0];
      xs_v3472 = ((tll_node)xs_v3469)->data[1];
      instr_free_struct(xs_v3469);
      call_ret_t209 = appendUL_i68(0, xs_v3472, ys_v3470);
      instr_struct(&ConsUL_t210, 34, 2, x_v3471, call_ret_t209);
      switch_ret_t208 = ConsUL_t210;
      break;
  }
  return switch_ret_t208;
}

tll_ptr lam_fun_t212(tll_ptr ys_v3478, tll_env env)
{
  tll_ptr call_ret_t211;
  call_ret_t211 = appendUL_i68(env[1], env[0], ys_v3478);
  return call_ret_t211;
}

tll_ptr lam_fun_t214(tll_ptr xs_v3476, tll_env env)
{
  tll_ptr lam_clo_t213;
  instr_clo(&lam_clo_t213, &lam_fun_t212, 2, xs_v3476, env[0]);
  return lam_clo_t213;
}

tll_ptr lam_fun_t216(tll_ptr A_v3473, tll_env env)
{
  tll_ptr lam_clo_t215;
  instr_clo(&lam_clo_t215, &lam_fun_t214, 1, A_v3473);
  return lam_clo_t215;
}

tll_ptr appendLL_i66(tll_ptr A_v3479, tll_ptr xs_v3480, tll_ptr ys_v3481)
{
  tll_ptr ConsLL_t220; tll_ptr call_ret_t219; tll_ptr switch_ret_t218;
  tll_ptr x_v3482; tll_ptr xs_v3483;
  switch(((tll_node)xs_v3480)->tag) {
    case 29:
      instr_free_struct(xs_v3480);
      switch_ret_t218 = ys_v3481;
      break;
    case 30:
      x_v3482 = ((tll_node)xs_v3480)->data[0];
      xs_v3483 = ((tll_node)xs_v3480)->data[1];
      instr_free_struct(xs_v3480);
      call_ret_t219 = appendLL_i66(0, xs_v3483, ys_v3481);
      instr_struct(&ConsLL_t220, 30, 2, x_v3482, call_ret_t219);
      switch_ret_t218 = ConsLL_t220;
      break;
  }
  return switch_ret_t218;
}

tll_ptr lam_fun_t222(tll_ptr ys_v3489, tll_env env)
{
  tll_ptr call_ret_t221;
  call_ret_t221 = appendLL_i66(env[1], env[0], ys_v3489);
  return call_ret_t221;
}

tll_ptr lam_fun_t224(tll_ptr xs_v3487, tll_env env)
{
  tll_ptr lam_clo_t223;
  instr_clo(&lam_clo_t223, &lam_fun_t222, 2, xs_v3487, env[0]);
  return lam_clo_t223;
}

tll_ptr lam_fun_t226(tll_ptr A_v3484, tll_env env)
{
  tll_ptr lam_clo_t225;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 1, A_v3484);
  return lam_clo_t225;
}

tll_ptr idU_i80(tll_ptr A_v3490, tll_ptr x_v3491)
{
  
  
  return x_v3491;
}

tll_ptr lam_fun_t236(tll_ptr x_v3494, tll_env env)
{
  tll_ptr call_ret_t235;
  call_ret_t235 = idU_i80(env[0], x_v3494);
  return call_ret_t235;
}

tll_ptr lam_fun_t238(tll_ptr A_v3492, tll_env env)
{
  tll_ptr lam_clo_t237;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 1, A_v3492);
  return lam_clo_t237;
}

tll_ptr idL_i79(tll_ptr A_v3495, tll_ptr x_v3496)
{
  
  
  return x_v3496;
}

tll_ptr lam_fun_t241(tll_ptr x_v3499, tll_env env)
{
  tll_ptr call_ret_t240;
  call_ret_t240 = idL_i79(env[0], x_v3499);
  return call_ret_t240;
}

tll_ptr lam_fun_t243(tll_ptr A_v3497, tll_env env)
{
  tll_ptr lam_clo_t242;
  instr_clo(&lam_clo_t242, &lam_fun_t241, 1, A_v3497);
  return lam_clo_t242;
}

int main()
{
  instr_init();
  tll_ptr ConsUU_t230; tll_ptr ConsUU_t233; tll_ptr NilUU_t229;
  tll_ptr NilUU_t232; tll_ptr O_t228; tll_ptr O_t231; tll_ptr app_ret_t247;
  tll_ptr app_ret_t251; tll_ptr call_ret_t234; tll_ptr call_ret_t245;
  tll_ptr call_ret_t248; tll_ptr call_ret_t249; tll_ptr call_ret_t250;
  tll_ptr lam_clo_t113; tll_ptr lam_clo_t127; tll_ptr lam_clo_t137;
  tll_ptr lam_clo_t14; tll_ptr lam_clo_t147; tll_ptr lam_clo_t157;
  tll_ptr lam_clo_t173; tll_ptr lam_clo_t185; tll_ptr lam_clo_t197;
  tll_ptr lam_clo_t20; tll_ptr lam_clo_t207; tll_ptr lam_clo_t217;
  tll_ptr lam_clo_t227; tll_ptr lam_clo_t239; tll_ptr lam_clo_t244;
  tll_ptr lam_clo_t28; tll_ptr lam_clo_t36; tll_ptr lam_clo_t48;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t7; tll_ptr lam_clo_t70;
  tll_ptr lam_clo_t78; tll_ptr lam_clo_t85; tll_ptr lam_clo_t99;
  tll_ptr s_v3500; tll_ptr tt_t246;
  instr_clo(&lam_clo_t7, &lam_fun_t6, 0);
  andbclo_i81 = lam_clo_t7;
  instr_clo(&lam_clo_t14, &lam_fun_t13, 0);
  orbclo_i82 = lam_clo_t14;
  instr_clo(&lam_clo_t20, &lam_fun_t19, 0);
  notbclo_i83 = lam_clo_t20;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  addnclo_i84 = lam_clo_t28;
  instr_clo(&lam_clo_t36, &lam_fun_t35, 0);
  mulnclo_i85 = lam_clo_t36;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  eqnclo_i86 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  ltenclo_i87 = lam_clo_t58;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 0);
  gtenclo_i88 = lam_clo_t70;
  instr_clo(&lam_clo_t78, &lam_fun_t77, 0);
  catsclo_i89 = lam_clo_t78;
  instr_clo(&lam_clo_t85, &lam_fun_t84, 0);
  strlenclo_i90 = lam_clo_t85;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 0);
  lenUUclo_i91 = lam_clo_t99;
  instr_clo(&lam_clo_t113, &lam_fun_t112, 0);
  lenULclo_i92 = lam_clo_t113;
  instr_clo(&lam_clo_t127, &lam_fun_t126, 0);
  lenLLclo_i93 = lam_clo_t127;
  instr_clo(&lam_clo_t137, &lam_fun_t136, 0);
  appendUUclo_i94 = lam_clo_t137;
  instr_clo(&lam_clo_t147, &lam_fun_t146, 0);
  appendULclo_i95 = lam_clo_t147;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 0);
  appendLLclo_i96 = lam_clo_t157;
  instr_clo(&lam_clo_t173, &lam_fun_t172, 0);
  readlineclo_i97 = lam_clo_t173;
  instr_clo(&lam_clo_t185, &lam_fun_t184, 0);
  printclo_i98 = lam_clo_t185;
  instr_clo(&lam_clo_t197, &lam_fun_t196, 0);
  prerrclo_i99 = lam_clo_t197;
  instr_clo(&lam_clo_t207, &lam_fun_t206, 0);
  appendUUclo_i100 = lam_clo_t207;
  instr_clo(&lam_clo_t217, &lam_fun_t216, 0);
  appendULclo_i101 = lam_clo_t217;
  instr_clo(&lam_clo_t227, &lam_fun_t226, 0);
  appendLLclo_i102 = lam_clo_t227;
  instr_struct(&O_t228, 16, 0);
  instr_struct(&NilUU_t229, 35, 0);
  instr_struct(&ConsUU_t230, 36, 2, O_t228, NilUU_t229);
  ls0_i76 = ConsUU_t230;
  instr_struct(&O_t231, 16, 0);
  instr_struct(&NilUU_t232, 35, 0);
  instr_struct(&ConsUU_t233, 36, 2, O_t231, NilUU_t232);
  ls1_i77 = ConsUU_t233;
  call_ret_t234 = appendUU_i69(0, ls0_i76, ls1_i77);
  ls2_i78 = call_ret_t234;
  instr_clo(&lam_clo_t239, &lam_fun_t238, 0);
  idUclo_i103 = lam_clo_t239;
  instr_clo(&lam_clo_t244, &lam_fun_t243, 0);
  idLclo_i104 = lam_clo_t244;
  instr_struct(&tt_t246, 13, 0);
  call_ret_t245 = readline_i59(tt_t246);
  instr_app(&app_ret_t247, call_ret_t245, 0);
  instr_free_clo(call_ret_t245);
  s_v3500 = app_ret_t247;
  call_ret_t250 = idU_i80(0, s_v3500);
  call_ret_t249 = print_i60(call_ret_t250);
  call_ret_t248 = idL_i79(0, call_ret_t249);
  instr_app(&app_ret_t251, call_ret_t248, 0);
  instr_free_clo(call_ret_t248);
  instr_free_struct(app_ret_t251);
  return 0;
}

