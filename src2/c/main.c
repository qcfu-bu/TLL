#include "runtime.h"

tll_ptr addnclo_i57;
tll_ptr andbclo_i54;
tll_ptr appendLLclo_i69;
tll_ptr appendULclo_i68;
tll_ptr appendUUclo_i67;
tll_ptr catsclo_i62;
tll_ptr eqnclo_i59;
tll_ptr gtenclo_i61;
tll_ptr lenLLclo_i66;
tll_ptr lenULclo_i65;
tll_ptr lenUUclo_i64;
tll_ptr ltenclo_i60;
tll_ptr mulnclo_i58;
tll_ptr notbclo_i56;
tll_ptr orbclo_i55;
tll_ptr prerrclo_i72;
tll_ptr printclo_i71;
tll_ptr readlineclo_i70;
tll_ptr strlenclo_i63;

tll_ptr andb_i25(tll_ptr b1_v2392, tll_ptr b2_v2393)
{
  tll_ptr false_t2; tll_ptr switch_ret_t1;
  switch(((tll_node)b1_v2392)->tag) {
    case 12:
      switch_ret_t1 = b2_v2393;
      break;
    case 13:
      instr_struct(&false_t2, 13, 0);
      switch_ret_t1 = false_t2;
      break;
  }
  return switch_ret_t1;
}

tll_ptr lam_fun_t4(tll_ptr b2_v2396, tll_env env)
{
  tll_ptr call_ret_t3;
  call_ret_t3 = andb_i25(env[0], b2_v2396);
  return call_ret_t3;
}

tll_ptr lam_fun_t6(tll_ptr b1_v2394, tll_env env)
{
  tll_ptr lam_clo_t5;
  instr_clo(&lam_clo_t5, &lam_fun_t4, 1, b1_v2394);
  return lam_clo_t5;
}

tll_ptr orb_i26(tll_ptr b1_v2397, tll_ptr b2_v2398)
{
  tll_ptr switch_ret_t8; tll_ptr true_t9;
  switch(((tll_node)b1_v2397)->tag) {
    case 12:
      instr_struct(&true_t9, 12, 0);
      switch_ret_t8 = true_t9;
      break;
    case 13:
      switch_ret_t8 = b2_v2398;
      break;
  }
  return switch_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b2_v2401, tll_env env)
{
  tll_ptr call_ret_t10;
  call_ret_t10 = orb_i26(env[0], b2_v2401);
  return call_ret_t10;
}

tll_ptr lam_fun_t13(tll_ptr b1_v2399, tll_env env)
{
  tll_ptr lam_clo_t12;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 1, b1_v2399);
  return lam_clo_t12;
}

tll_ptr notb_i27(tll_ptr b_v2402)
{
  tll_ptr false_t16; tll_ptr switch_ret_t15; tll_ptr true_t17;
  switch(((tll_node)b_v2402)->tag) {
    case 12:
      instr_struct(&false_t16, 13, 0);
      switch_ret_t15 = false_t16;
      break;
    case 13:
      instr_struct(&true_t17, 12, 0);
      switch_ret_t15 = true_t17;
      break;
  }
  return switch_ret_t15;
}

tll_ptr lam_fun_t19(tll_ptr b_v2403, tll_env env)
{
  tll_ptr call_ret_t18;
  call_ret_t18 = notb_i27(b_v2403);
  return call_ret_t18;
}

tll_ptr addn_i28(tll_ptr x_v2404, tll_ptr y_v2405)
{
  tll_ptr S_t23; tll_ptr call_ret_t22; tll_ptr switch_ret_t21;
  tll_ptr x_v2406;
  switch(((tll_node)x_v2404)->tag) {
    case 14:
      switch_ret_t21 = y_v2405;
      break;
    case 15:
      x_v2406 = ((tll_node)x_v2404)->data[0];
      call_ret_t22 = addn_i28(x_v2406, y_v2405);
      instr_struct(&S_t23, 15, 1, call_ret_t22);
      switch_ret_t21 = S_t23;
      break;
  }
  return switch_ret_t21;
}

tll_ptr lam_fun_t25(tll_ptr y_v2409, tll_env env)
{
  tll_ptr call_ret_t24;
  call_ret_t24 = addn_i28(env[0], y_v2409);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr x_v2407, tll_env env)
{
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, x_v2407);
  return lam_clo_t26;
}

tll_ptr muln_i29(tll_ptr x_v2410, tll_ptr y_v2411)
{
  tll_ptr call_ret_t30; tll_ptr call_ret_t31; tll_ptr switch_ret_t29;
  tll_ptr x_v2412;
  switch(((tll_node)x_v2410)->tag) {
    case 14:
      switch_ret_t29 = y_v2411;
      break;
    case 15:
      x_v2412 = ((tll_node)x_v2410)->data[0];
      call_ret_t31 = muln_i29(x_v2412, y_v2411);
      call_ret_t30 = addn_i28(y_v2411, call_ret_t31);
      switch_ret_t29 = call_ret_t30;
      break;
  }
  return switch_ret_t29;
}

tll_ptr lam_fun_t33(tll_ptr y_v2415, tll_env env)
{
  tll_ptr call_ret_t32;
  call_ret_t32 = muln_i29(env[0], y_v2415);
  return call_ret_t32;
}

tll_ptr lam_fun_t35(tll_ptr x_v2413, tll_env env)
{
  tll_ptr lam_clo_t34;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 1, x_v2413);
  return lam_clo_t34;
}

tll_ptr eqn_i30(tll_ptr x_v2416, tll_ptr y_v2417)
{
  tll_ptr __v2418; tll_ptr call_ret_t43; tll_ptr false_t40;
  tll_ptr false_t42; tll_ptr switch_ret_t37; tll_ptr switch_ret_t38;
  tll_ptr switch_ret_t41; tll_ptr true_t39; tll_ptr x_v2419; tll_ptr y_v2420;
  switch(((tll_node)x_v2416)->tag) {
    case 14:
      switch(((tll_node)y_v2417)->tag) {
        case 14:
          instr_struct(&true_t39, 12, 0);
          switch_ret_t38 = true_t39;
          break;
        case 15:
          __v2418 = ((tll_node)y_v2417)->data[0];
          instr_struct(&false_t40, 13, 0);
          switch_ret_t38 = false_t40;
          break;
      }
      switch_ret_t37 = switch_ret_t38;
      break;
    case 15:
      x_v2419 = ((tll_node)x_v2416)->data[0];
      switch(((tll_node)y_v2417)->tag) {
        case 14:
          instr_struct(&false_t42, 13, 0);
          switch_ret_t41 = false_t42;
          break;
        case 15:
          y_v2420 = ((tll_node)y_v2417)->data[0];
          call_ret_t43 = eqn_i30(x_v2419, y_v2420);
          switch_ret_t41 = call_ret_t43;
          break;
      }
      switch_ret_t37 = switch_ret_t41;
      break;
  }
  return switch_ret_t37;
}

tll_ptr lam_fun_t45(tll_ptr y_v2423, tll_env env)
{
  tll_ptr call_ret_t44;
  call_ret_t44 = eqn_i30(env[0], y_v2423);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v2421, tll_env env)
{
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v2421);
  return lam_clo_t46;
}

tll_ptr lten_i31(tll_ptr x_v2424, tll_ptr y_v2425)
{
  tll_ptr call_ret_t53; tll_ptr false_t52; tll_ptr switch_ret_t49;
  tll_ptr switch_ret_t51; tll_ptr true_t50; tll_ptr x_v2426; tll_ptr y_v2427;
  switch(((tll_node)x_v2424)->tag) {
    case 14:
      instr_struct(&true_t50, 12, 0);
      switch_ret_t49 = true_t50;
      break;
    case 15:
      x_v2426 = ((tll_node)x_v2424)->data[0];
      switch(((tll_node)y_v2425)->tag) {
        case 14:
          instr_struct(&false_t52, 13, 0);
          switch_ret_t51 = false_t52;
          break;
        case 15:
          y_v2427 = ((tll_node)y_v2425)->data[0];
          call_ret_t53 = lten_i31(x_v2426, y_v2427);
          switch_ret_t51 = call_ret_t53;
          break;
      }
      switch_ret_t49 = switch_ret_t51;
      break;
  }
  return switch_ret_t49;
}

tll_ptr lam_fun_t55(tll_ptr y_v2430, tll_env env)
{
  tll_ptr call_ret_t54;
  call_ret_t54 = lten_i31(env[0], y_v2430);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v2428, tll_env env)
{
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v2428);
  return lam_clo_t56;
}

tll_ptr gten_i32(tll_ptr x_v2431, tll_ptr y_v2432)
{
  tll_ptr __v2433; tll_ptr call_ret_t65; tll_ptr false_t62;
  tll_ptr switch_ret_t59; tll_ptr switch_ret_t60; tll_ptr switch_ret_t63;
  tll_ptr true_t61; tll_ptr true_t64; tll_ptr x_v2434; tll_ptr y_v2435;
  switch(((tll_node)x_v2431)->tag) {
    case 14:
      switch(((tll_node)y_v2432)->tag) {
        case 14:
          instr_struct(&true_t61, 12, 0);
          switch_ret_t60 = true_t61;
          break;
        case 15:
          __v2433 = ((tll_node)y_v2432)->data[0];
          instr_struct(&false_t62, 13, 0);
          switch_ret_t60 = false_t62;
          break;
      }
      switch_ret_t59 = switch_ret_t60;
      break;
    case 15:
      x_v2434 = ((tll_node)x_v2431)->data[0];
      switch(((tll_node)y_v2432)->tag) {
        case 14:
          instr_struct(&true_t64, 12, 0);
          switch_ret_t63 = true_t64;
          break;
        case 15:
          y_v2435 = ((tll_node)y_v2432)->data[0];
          call_ret_t65 = gten_i32(x_v2434, y_v2435);
          switch_ret_t63 = call_ret_t65;
          break;
      }
      switch_ret_t59 = switch_ret_t63;
      break;
  }
  return switch_ret_t59;
}

tll_ptr lam_fun_t67(tll_ptr y_v2438, tll_env env)
{
  tll_ptr call_ret_t66;
  call_ret_t66 = gten_i32(env[0], y_v2438);
  return call_ret_t66;
}

tll_ptr lam_fun_t69(tll_ptr x_v2436, tll_env env)
{
  tll_ptr lam_clo_t68;
  instr_clo(&lam_clo_t68, &lam_fun_t67, 1, x_v2436);
  return lam_clo_t68;
}

tll_ptr cats_i35(tll_ptr s1_v2439, tll_ptr s2_v2440)
{
  tll_ptr String_t73; tll_ptr c_v2441; tll_ptr call_ret_t72;
  tll_ptr s1_v2442; tll_ptr switch_ret_t71;
  switch(((tll_node)s1_v2439)->tag) {
    case 17:
      switch_ret_t71 = s2_v2440;
      break;
    case 18:
      c_v2441 = ((tll_node)s1_v2439)->data[0];
      s1_v2442 = ((tll_node)s1_v2439)->data[1];
      call_ret_t72 = cats_i35(s1_v2442, s2_v2440);
      instr_struct(&String_t73, 18, 2, c_v2441, call_ret_t72);
      switch_ret_t71 = String_t73;
      break;
  }
  return switch_ret_t71;
}

tll_ptr lam_fun_t75(tll_ptr s2_v2445, tll_env env)
{
  tll_ptr call_ret_t74;
  call_ret_t74 = cats_i35(env[0], s2_v2445);
  return call_ret_t74;
}

tll_ptr lam_fun_t77(tll_ptr s1_v2443, tll_env env)
{
  tll_ptr lam_clo_t76;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 1, s1_v2443);
  return lam_clo_t76;
}

tll_ptr strlen_i36(tll_ptr s_v2446)
{
  tll_ptr O_t80; tll_ptr S_t82; tll_ptr __v2447; tll_ptr call_ret_t81;
  tll_ptr s_v2448; tll_ptr switch_ret_t79;
  switch(((tll_node)s_v2446)->tag) {
    case 17:
      instr_struct(&O_t80, 14, 0);
      switch_ret_t79 = O_t80;
      break;
    case 18:
      __v2447 = ((tll_node)s_v2446)->data[0];
      s_v2448 = ((tll_node)s_v2446)->data[1];
      call_ret_t81 = strlen_i36(s_v2448);
      instr_struct(&S_t82, 15, 1, call_ret_t81);
      switch_ret_t79 = S_t82;
      break;
  }
  return switch_ret_t79;
}

tll_ptr lam_fun_t84(tll_ptr s_v2449, tll_env env)
{
  tll_ptr call_ret_t83;
  call_ret_t83 = strlen_i36(s_v2449);
  return call_ret_t83;
}

tll_ptr lenUU_i40(tll_ptr A_v2450, tll_ptr xs_v2451)
{
  tll_ptr O_t87; tll_ptr S_t92; tll_ptr call_ret_t90; tll_ptr consUU_t93;
  tll_ptr n_v2454; tll_ptr nilUU_t88; tll_ptr pair_struct_t89;
  tll_ptr pair_struct_t94; tll_ptr switch_ret_t86; tll_ptr switch_ret_t91;
  tll_ptr x_v2452; tll_ptr xs_v2453; tll_ptr xs_v2455;
  switch(((tll_node)xs_v2451)->tag) {
    case 25:
      instr_struct(&O_t87, 14, 0);
      instr_struct(&nilUU_t88, 25, 0);
      instr_struct(&pair_struct_t89, 0, 2, O_t87, nilUU_t88);
      switch_ret_t86 = pair_struct_t89;
      break;
    case 26:
      x_v2452 = ((tll_node)xs_v2451)->data[0];
      xs_v2453 = ((tll_node)xs_v2451)->data[1];
      call_ret_t90 = lenUU_i40(0, xs_v2453);
      switch(((tll_node)call_ret_t90)->tag) {
        case 0:
          n_v2454 = ((tll_node)call_ret_t90)->data[0];
          xs_v2455 = ((tll_node)call_ret_t90)->data[1];
          instr_free_struct(call_ret_t90);
          instr_struct(&S_t92, 15, 1, n_v2454);
          instr_struct(&consUU_t93, 26, 2, x_v2452, xs_v2455);
          instr_struct(&pair_struct_t94, 0, 2, S_t92, consUU_t93);
          switch_ret_t91 = pair_struct_t94;
          break;
      }
      switch_ret_t86 = switch_ret_t91;
      break;
  }
  return switch_ret_t86;
}

tll_ptr lam_fun_t96(tll_ptr xs_v2458, tll_env env)
{
  tll_ptr call_ret_t95;
  call_ret_t95 = lenUU_i40(env[0], xs_v2458);
  return call_ret_t95;
}

tll_ptr lam_fun_t98(tll_ptr A_v2456, tll_env env)
{
  tll_ptr lam_clo_t97;
  instr_clo(&lam_clo_t97, &lam_fun_t96, 1, A_v2456);
  return lam_clo_t97;
}

tll_ptr lenUL_i39(tll_ptr A_v2459, tll_ptr xs_v2460)
{
  tll_ptr O_t101; tll_ptr S_t106; tll_ptr call_ret_t104; tll_ptr consUL_t107;
  tll_ptr n_v2463; tll_ptr nilUL_t102; tll_ptr pair_struct_t103;
  tll_ptr pair_struct_t108; tll_ptr switch_ret_t100; tll_ptr switch_ret_t105;
  tll_ptr x_v2461; tll_ptr xs_v2462; tll_ptr xs_v2464;
  switch(((tll_node)xs_v2460)->tag) {
    case 23:
      instr_free_struct(xs_v2460);
      instr_struct(&O_t101, 14, 0);
      instr_struct(&nilUL_t102, 23, 0);
      instr_struct(&pair_struct_t103, 0, 2, O_t101, nilUL_t102);
      switch_ret_t100 = pair_struct_t103;
      break;
    case 24:
      x_v2461 = ((tll_node)xs_v2460)->data[0];
      xs_v2462 = ((tll_node)xs_v2460)->data[1];
      instr_free_struct(xs_v2460);
      call_ret_t104 = lenUL_i39(0, xs_v2462);
      switch(((tll_node)call_ret_t104)->tag) {
        case 0:
          n_v2463 = ((tll_node)call_ret_t104)->data[0];
          xs_v2464 = ((tll_node)call_ret_t104)->data[1];
          instr_free_struct(call_ret_t104);
          instr_struct(&S_t106, 15, 1, n_v2463);
          instr_struct(&consUL_t107, 24, 2, x_v2461, xs_v2464);
          instr_struct(&pair_struct_t108, 0, 2, S_t106, consUL_t107);
          switch_ret_t105 = pair_struct_t108;
          break;
      }
      switch_ret_t100 = switch_ret_t105;
      break;
  }
  return switch_ret_t100;
}

tll_ptr lam_fun_t110(tll_ptr xs_v2467, tll_env env)
{
  tll_ptr call_ret_t109;
  call_ret_t109 = lenUL_i39(env[0], xs_v2467);
  return call_ret_t109;
}

tll_ptr lam_fun_t112(tll_ptr A_v2465, tll_env env)
{
  tll_ptr lam_clo_t111;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 1, A_v2465);
  return lam_clo_t111;
}

tll_ptr lenLL_i37(tll_ptr A_v2468, tll_ptr xs_v2469)
{
  tll_ptr O_t115; tll_ptr S_t120; tll_ptr call_ret_t118; tll_ptr consLL_t121;
  tll_ptr n_v2472; tll_ptr nilLL_t116; tll_ptr pair_struct_t117;
  tll_ptr pair_struct_t122; tll_ptr switch_ret_t114; tll_ptr switch_ret_t119;
  tll_ptr x_v2470; tll_ptr xs_v2471; tll_ptr xs_v2473;
  switch(((tll_node)xs_v2469)->tag) {
    case 19:
      instr_free_struct(xs_v2469);
      instr_struct(&O_t115, 14, 0);
      instr_struct(&nilLL_t116, 19, 0);
      instr_struct(&pair_struct_t117, 0, 2, O_t115, nilLL_t116);
      switch_ret_t114 = pair_struct_t117;
      break;
    case 20:
      x_v2470 = ((tll_node)xs_v2469)->data[0];
      xs_v2471 = ((tll_node)xs_v2469)->data[1];
      instr_free_struct(xs_v2469);
      call_ret_t118 = lenLL_i37(0, xs_v2471);
      switch(((tll_node)call_ret_t118)->tag) {
        case 0:
          n_v2472 = ((tll_node)call_ret_t118)->data[0];
          xs_v2473 = ((tll_node)call_ret_t118)->data[1];
          instr_free_struct(call_ret_t118);
          instr_struct(&S_t120, 15, 1, n_v2472);
          instr_struct(&consLL_t121, 20, 2, x_v2470, xs_v2473);
          instr_struct(&pair_struct_t122, 0, 2, S_t120, consLL_t121);
          switch_ret_t119 = pair_struct_t122;
          break;
      }
      switch_ret_t114 = switch_ret_t119;
      break;
  }
  return switch_ret_t114;
}

tll_ptr lam_fun_t124(tll_ptr xs_v2476, tll_env env)
{
  tll_ptr call_ret_t123;
  call_ret_t123 = lenLL_i37(env[0], xs_v2476);
  return call_ret_t123;
}

tll_ptr lam_fun_t126(tll_ptr A_v2474, tll_env env)
{
  tll_ptr lam_clo_t125;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 1, A_v2474);
  return lam_clo_t125;
}

tll_ptr appendUU_i44(tll_ptr A_v2477, tll_ptr xs_v2478, tll_ptr ys_v2479)
{
  tll_ptr call_ret_t129; tll_ptr consUU_t130; tll_ptr switch_ret_t128;
  tll_ptr x_v2480; tll_ptr xs_v2481;
  switch(((tll_node)xs_v2478)->tag) {
    case 25:
      switch_ret_t128 = ys_v2479;
      break;
    case 26:
      x_v2480 = ((tll_node)xs_v2478)->data[0];
      xs_v2481 = ((tll_node)xs_v2478)->data[1];
      call_ret_t129 = appendUU_i44(0, xs_v2481, ys_v2479);
      instr_struct(&consUU_t130, 26, 2, x_v2480, call_ret_t129);
      switch_ret_t128 = consUU_t130;
      break;
  }
  return switch_ret_t128;
}

tll_ptr lam_fun_t132(tll_ptr ys_v2487, tll_env env)
{
  tll_ptr call_ret_t131;
  call_ret_t131 = appendUU_i44(env[1], env[0], ys_v2487);
  return call_ret_t131;
}

tll_ptr lam_fun_t134(tll_ptr xs_v2485, tll_env env)
{
  tll_ptr lam_clo_t133;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 2, xs_v2485, env[0]);
  return lam_clo_t133;
}

tll_ptr lam_fun_t136(tll_ptr A_v2482, tll_env env)
{
  tll_ptr lam_clo_t135;
  instr_clo(&lam_clo_t135, &lam_fun_t134, 1, A_v2482);
  return lam_clo_t135;
}

tll_ptr appendUL_i43(tll_ptr A_v2488, tll_ptr xs_v2489, tll_ptr ys_v2490)
{
  tll_ptr call_ret_t139; tll_ptr consUL_t140; tll_ptr switch_ret_t138;
  tll_ptr x_v2491; tll_ptr xs_v2492;
  switch(((tll_node)xs_v2489)->tag) {
    case 23:
      instr_free_struct(xs_v2489);
      switch_ret_t138 = ys_v2490;
      break;
    case 24:
      x_v2491 = ((tll_node)xs_v2489)->data[0];
      xs_v2492 = ((tll_node)xs_v2489)->data[1];
      instr_free_struct(xs_v2489);
      call_ret_t139 = appendUL_i43(0, xs_v2492, ys_v2490);
      instr_struct(&consUL_t140, 24, 2, x_v2491, call_ret_t139);
      switch_ret_t138 = consUL_t140;
      break;
  }
  return switch_ret_t138;
}

tll_ptr lam_fun_t142(tll_ptr ys_v2498, tll_env env)
{
  tll_ptr call_ret_t141;
  call_ret_t141 = appendUL_i43(env[1], env[0], ys_v2498);
  return call_ret_t141;
}

tll_ptr lam_fun_t144(tll_ptr xs_v2496, tll_env env)
{
  tll_ptr lam_clo_t143;
  instr_clo(&lam_clo_t143, &lam_fun_t142, 2, xs_v2496, env[0]);
  return lam_clo_t143;
}

tll_ptr lam_fun_t146(tll_ptr A_v2493, tll_env env)
{
  tll_ptr lam_clo_t145;
  instr_clo(&lam_clo_t145, &lam_fun_t144, 1, A_v2493);
  return lam_clo_t145;
}

tll_ptr appendLL_i41(tll_ptr A_v2499, tll_ptr xs_v2500, tll_ptr ys_v2501)
{
  tll_ptr call_ret_t149; tll_ptr consLL_t150; tll_ptr switch_ret_t148;
  tll_ptr x_v2502; tll_ptr xs_v2503;
  switch(((tll_node)xs_v2500)->tag) {
    case 19:
      instr_free_struct(xs_v2500);
      switch_ret_t148 = ys_v2501;
      break;
    case 20:
      x_v2502 = ((tll_node)xs_v2500)->data[0];
      xs_v2503 = ((tll_node)xs_v2500)->data[1];
      instr_free_struct(xs_v2500);
      call_ret_t149 = appendLL_i41(0, xs_v2503, ys_v2501);
      instr_struct(&consLL_t150, 20, 2, x_v2502, call_ret_t149);
      switch_ret_t148 = consLL_t150;
      break;
  }
  return switch_ret_t148;
}

tll_ptr lam_fun_t152(tll_ptr ys_v2509, tll_env env)
{
  tll_ptr call_ret_t151;
  call_ret_t151 = appendLL_i41(env[1], env[0], ys_v2509);
  return call_ret_t151;
}

tll_ptr lam_fun_t154(tll_ptr xs_v2507, tll_env env)
{
  tll_ptr lam_clo_t153;
  instr_clo(&lam_clo_t153, &lam_fun_t152, 2, xs_v2507, env[0]);
  return lam_clo_t153;
}

tll_ptr lam_fun_t156(tll_ptr A_v2504, tll_env env)
{
  tll_ptr lam_clo_t155;
  instr_clo(&lam_clo_t155, &lam_fun_t154, 1, A_v2504);
  return lam_clo_t155;
}

tll_ptr lam_fun_t166(tll_ptr __v2526, tll_env env)
{
  tll_ptr __v2531; tll_ptr __v2532; tll_ptr ch_v2530; tll_ptr false_t164;
  tll_ptr send_ch_t163; tll_ptr tt_t165;
  instr_struct(&false_t164, 13, 0);
  instr_send(&send_ch_t163, env[0], false_t164);
  ch_v2530 = send_ch_t163;
  __v2532 = ch_v2530;
  instr_struct(&tt_t165, 11, 0);
  __v2531 = tt_t165;
  return env[1];
}

tll_ptr lam_fun_t169(tll_ptr __v2511, tll_env env)
{
  tll_ptr __v2523; tll_ptr app_ret_t168; tll_ptr ch_v2521; tll_ptr ch_v2522;
  tll_ptr ch_v2525; tll_ptr lam_clo_t167; tll_ptr prim_ch_t158;
  tll_ptr recv_msg_t161; tll_ptr s_v2524; tll_ptr send_ch_t159;
  tll_ptr switch_ret_t162; tll_ptr true_t160;
  instr_open(&prim_ch_t158, &proc_stdin);
  ch_v2521 = prim_ch_t158;
  instr_struct(&true_t160, 12, 0);
  instr_send(&send_ch_t159, ch_v2521, true_t160);
  ch_v2522 = send_ch_t159;
  instr_recv(&recv_msg_t161, ch_v2522);
  __v2523 = recv_msg_t161;
  switch(((tll_node)__v2523)->tag) {
    case 0:
      s_v2524 = ((tll_node)__v2523)->data[0];
      ch_v2525 = ((tll_node)__v2523)->data[1];
      instr_free_struct(__v2523);
      instr_clo(&lam_clo_t167, &lam_fun_t166, 2, ch_v2525, s_v2524);
      switch_ret_t162 = lam_clo_t167;
      break;
  }
  instr_app(&app_ret_t168, switch_ret_t162, 0);
  instr_free_clo(switch_ret_t162);
  return app_ret_t168;
}

tll_ptr readline_i51(tll_ptr __v2510)
{
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 0);
  return lam_clo_t170;
}

tll_ptr lam_fun_t172(tll_ptr __v2533, tll_env env)
{
  tll_ptr call_ret_t171;
  call_ret_t171 = readline_i51(__v2533);
  return call_ret_t171;
}

tll_ptr lam_fun_t181(tll_ptr __v2535, tll_env env)
{
  tll_ptr __v2545; tll_ptr ch_v2541; tll_ptr ch_v2542; tll_ptr ch_v2543;
  tll_ptr ch_v2544; tll_ptr false_t179; tll_ptr prim_ch_t174;
  tll_ptr send_ch_t175; tll_ptr send_ch_t177; tll_ptr send_ch_t178;
  tll_ptr true_t176; tll_ptr tt_t180;
  instr_open(&prim_ch_t174, &proc_stdout);
  ch_v2541 = prim_ch_t174;
  instr_struct(&true_t176, 12, 0);
  instr_send(&send_ch_t175, ch_v2541, true_t176);
  ch_v2542 = send_ch_t175;
  instr_send(&send_ch_t177, ch_v2542, env[0]);
  ch_v2543 = send_ch_t177;
  instr_struct(&false_t179, 13, 0);
  instr_send(&send_ch_t178, ch_v2543, false_t179);
  ch_v2544 = send_ch_t178;
  __v2545 = ch_v2544;
  instr_struct(&tt_t180, 11, 0);
  return tt_t180;
}

tll_ptr print_i52(tll_ptr s_v2534)
{
  tll_ptr lam_clo_t182;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 1, s_v2534);
  return lam_clo_t182;
}

tll_ptr lam_fun_t184(tll_ptr s_v2546, tll_env env)
{
  tll_ptr call_ret_t183;
  call_ret_t183 = print_i52(s_v2546);
  return call_ret_t183;
}

tll_ptr lam_fun_t193(tll_ptr __v2548, tll_env env)
{
  tll_ptr __v2558; tll_ptr ch_v2554; tll_ptr ch_v2555; tll_ptr ch_v2556;
  tll_ptr ch_v2557; tll_ptr false_t191; tll_ptr prim_ch_t186;
  tll_ptr send_ch_t187; tll_ptr send_ch_t189; tll_ptr send_ch_t190;
  tll_ptr true_t188; tll_ptr tt_t192;
  instr_open(&prim_ch_t186, &proc_stderr);
  ch_v2554 = prim_ch_t186;
  instr_struct(&true_t188, 12, 0);
  instr_send(&send_ch_t187, ch_v2554, true_t188);
  ch_v2555 = send_ch_t187;
  instr_send(&send_ch_t189, ch_v2555, env[0]);
  ch_v2556 = send_ch_t189;
  instr_struct(&false_t191, 13, 0);
  instr_send(&send_ch_t190, ch_v2556, false_t191);
  ch_v2557 = send_ch_t190;
  __v2558 = ch_v2557;
  instr_struct(&tt_t192, 11, 0);
  return tt_t192;
}

tll_ptr prerr_i53(tll_ptr s_v2547)
{
  tll_ptr lam_clo_t194;
  instr_clo(&lam_clo_t194, &lam_fun_t193, 1, s_v2547);
  return lam_clo_t194;
}

tll_ptr lam_fun_t196(tll_ptr s_v2559, tll_env env)
{
  tll_ptr call_ret_t195;
  call_ret_t195 = prerr_i53(s_v2559);
  return call_ret_t195;
}

tll_ptr fork_fun_t203(tll_env env)
{
  tll_ptr __v2567; tll_ptr app_ret_t200; tll_ptr c_v2566;
  tll_ptr call_ret_t198; tll_ptr fork_ret_t205; tll_ptr s_v2565;
  tll_ptr send_ch_t201; tll_ptr tt_t199; tll_ptr tt_t202;
  instr_struct(&tt_t199, 11, 0);
  call_ret_t198 = readline_i51(tt_t199);
  instr_app(&app_ret_t200, call_ret_t198, 0);
  instr_free_clo(call_ret_t198);
  s_v2565 = app_ret_t200;
  instr_send(&send_ch_t201, env[0], s_v2565);
  c_v2566 = send_ch_t201;
  __v2567 = c_v2566;
  instr_struct(&tt_t202, 11, 0);
  fork_ret_t205 = tt_t202;
  instr_free_thread(env);
  return fork_ret_t205;
}

tll_ptr lam_fun_t211(tll_ptr __v2571, tll_env env)
{
  tll_ptr __v2573; tll_ptr app_ret_t210; tll_ptr call_ret_t209;
  tll_ptr close_tmp_t208;
  instr_close(&close_tmp_t208, env[0]);
  __v2573 = close_tmp_t208;
  call_ret_t209 = print_i52(env[1]);
  instr_app(&app_ret_t210, call_ret_t209, 0);
  instr_free_clo(call_ret_t209);
  return app_ret_t210;
}

int main()
{
  instr_init();
  tll_ptr __v2568; tll_ptr app_ret_t213; tll_ptr c_v2560; tll_ptr c_v2570;
  tll_ptr fork_ch_t204; tll_ptr lam_clo_t113; tll_ptr lam_clo_t127;
  tll_ptr lam_clo_t137; tll_ptr lam_clo_t14; tll_ptr lam_clo_t147;
  tll_ptr lam_clo_t157; tll_ptr lam_clo_t173; tll_ptr lam_clo_t185;
  tll_ptr lam_clo_t197; tll_ptr lam_clo_t20; tll_ptr lam_clo_t212;
  tll_ptr lam_clo_t28; tll_ptr lam_clo_t36; tll_ptr lam_clo_t48;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t7; tll_ptr lam_clo_t70;
  tll_ptr lam_clo_t78; tll_ptr lam_clo_t85; tll_ptr lam_clo_t99;
  tll_ptr msg_v2569; tll_ptr recv_msg_t206; tll_ptr switch_ret_t207;
  instr_clo(&lam_clo_t7, &lam_fun_t6, 0);
  andbclo_i54 = lam_clo_t7;
  instr_clo(&lam_clo_t14, &lam_fun_t13, 0);
  orbclo_i55 = lam_clo_t14;
  instr_clo(&lam_clo_t20, &lam_fun_t19, 0);
  notbclo_i56 = lam_clo_t20;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  addnclo_i57 = lam_clo_t28;
  instr_clo(&lam_clo_t36, &lam_fun_t35, 0);
  mulnclo_i58 = lam_clo_t36;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  eqnclo_i59 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  ltenclo_i60 = lam_clo_t58;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 0);
  gtenclo_i61 = lam_clo_t70;
  instr_clo(&lam_clo_t78, &lam_fun_t77, 0);
  catsclo_i62 = lam_clo_t78;
  instr_clo(&lam_clo_t85, &lam_fun_t84, 0);
  strlenclo_i63 = lam_clo_t85;
  instr_clo(&lam_clo_t99, &lam_fun_t98, 0);
  lenUUclo_i64 = lam_clo_t99;
  instr_clo(&lam_clo_t113, &lam_fun_t112, 0);
  lenULclo_i65 = lam_clo_t113;
  instr_clo(&lam_clo_t127, &lam_fun_t126, 0);
  lenLLclo_i66 = lam_clo_t127;
  instr_clo(&lam_clo_t137, &lam_fun_t136, 0);
  appendUUclo_i67 = lam_clo_t137;
  instr_clo(&lam_clo_t147, &lam_fun_t146, 0);
  appendULclo_i68 = lam_clo_t147;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 0);
  appendLLclo_i69 = lam_clo_t157;
  instr_clo(&lam_clo_t173, &lam_fun_t172, 0);
  readlineclo_i70 = lam_clo_t173;
  instr_clo(&lam_clo_t185, &lam_fun_t184, 0);
  printclo_i71 = lam_clo_t185;
  instr_clo(&lam_clo_t197, &lam_fun_t196, 0);
  prerrclo_i72 = lam_clo_t197;
  instr_fork(&fork_ch_t204, &fork_fun_t203, 0);
  c_v2560 = fork_ch_t204;
  instr_recv(&recv_msg_t206, c_v2560);
  __v2568 = recv_msg_t206;
  switch(((tll_node)__v2568)->tag) {
    case 0:
      msg_v2569 = ((tll_node)__v2568)->data[0];
      c_v2570 = ((tll_node)__v2568)->data[1];
      instr_free_struct(__v2568);
      instr_clo(&lam_clo_t212, &lam_fun_t211, 2, c_v2570, msg_v2569);
      switch_ret_t207 = lam_clo_t212;
      break;
  }
  instr_app(&app_ret_t213, switch_ret_t207, 0);
  instr_free_clo(switch_ret_t207);
  instr_free_struct(app_ret_t213);
  return 0;
}

