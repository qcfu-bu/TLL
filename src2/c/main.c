#include "runtime.h"

tll_ptr addnclo_i74;
tll_ptr andbclo_i71;
tll_ptr appendLLclo_i86;
tll_ptr appendULclo_i85;
tll_ptr appendUUclo_i84;
tll_ptr catsclo_i79;
tll_ptr eqnclo_i76;
tll_ptr gtenclo_i78;
tll_ptr idLclo_i88;
tll_ptr idUclo_i87;
tll_ptr ls0_i66;
tll_ptr ls1_i67;
tll_ptr ls2_i68;
tll_ptr ltenclo_i77;
tll_ptr mulnclo_i75;
tll_ptr notbclo_i73;
tll_ptr orbclo_i72;
tll_ptr prerrclo_i83;
tll_ptr printclo_i82;
tll_ptr readlineclo_i81;
tll_ptr strlenclo_i80;

tll_ptr andb_i31(tll_ptr b1_v2563, tll_ptr b2_v2564)
{
  tll_ptr false_t2; tll_ptr switch_ret_t1;
  switch(((tll_node)b1_v2563)->tag) {
    case 12:
      switch_ret_t1 = b2_v2564;
      break;
    case 13:
      instr_struct(&false_t2, 13, 0);
      switch_ret_t1 = false_t2;
      break;
  }
  return switch_ret_t1;
}

tll_ptr lam_fun_t4(tll_ptr b2_v2567, tll_env env)
{
  tll_ptr call_ret_t3;
  call_ret_t3 = andb_i31(env[0], b2_v2567);
  return call_ret_t3;
}

tll_ptr lam_fun_t6(tll_ptr b1_v2565, tll_env env)
{
  tll_ptr lam_clo_t5;
  instr_clo(&lam_clo_t5, &lam_fun_t4, 1, b1_v2565);
  return lam_clo_t5;
}

tll_ptr orb_i32(tll_ptr b1_v2568, tll_ptr b2_v2569)
{
  tll_ptr switch_ret_t8; tll_ptr true_t9;
  switch(((tll_node)b1_v2568)->tag) {
    case 12:
      instr_struct(&true_t9, 12, 0);
      switch_ret_t8 = true_t9;
      break;
    case 13:
      switch_ret_t8 = b2_v2569;
      break;
  }
  return switch_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b2_v2572, tll_env env)
{
  tll_ptr call_ret_t10;
  call_ret_t10 = orb_i32(env[0], b2_v2572);
  return call_ret_t10;
}

tll_ptr lam_fun_t13(tll_ptr b1_v2570, tll_env env)
{
  tll_ptr lam_clo_t12;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 1, b1_v2570);
  return lam_clo_t12;
}

tll_ptr notb_i33(tll_ptr b_v2573)
{
  tll_ptr false_t16; tll_ptr switch_ret_t15; tll_ptr true_t17;
  switch(((tll_node)b_v2573)->tag) {
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

tll_ptr lam_fun_t19(tll_ptr b_v2574, tll_env env)
{
  tll_ptr call_ret_t18;
  call_ret_t18 = notb_i33(b_v2574);
  return call_ret_t18;
}

tll_ptr addn_i34(tll_ptr x_v2575, tll_ptr y_v2576)
{
  tll_ptr S_t23; tll_ptr call_ret_t22; tll_ptr switch_ret_t21;
  tll_ptr x_v2577;
  switch(((tll_node)x_v2575)->tag) {
    case 14:
      switch_ret_t21 = y_v2576;
      break;
    case 15:
      x_v2577 = ((tll_node)x_v2575)->data[0];
      call_ret_t22 = addn_i34(x_v2577, y_v2576);
      instr_struct(&S_t23, 15, 1, call_ret_t22);
      switch_ret_t21 = S_t23;
      break;
  }
  return switch_ret_t21;
}

tll_ptr lam_fun_t25(tll_ptr y_v2580, tll_env env)
{
  tll_ptr call_ret_t24;
  call_ret_t24 = addn_i34(env[0], y_v2580);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr x_v2578, tll_env env)
{
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, x_v2578);
  return lam_clo_t26;
}

tll_ptr muln_i35(tll_ptr x_v2581, tll_ptr y_v2582)
{
  tll_ptr call_ret_t30; tll_ptr call_ret_t31; tll_ptr switch_ret_t29;
  tll_ptr x_v2583;
  switch(((tll_node)x_v2581)->tag) {
    case 14:
      switch_ret_t29 = y_v2582;
      break;
    case 15:
      x_v2583 = ((tll_node)x_v2581)->data[0];
      call_ret_t31 = muln_i35(x_v2583, y_v2582);
      call_ret_t30 = addn_i34(y_v2582, call_ret_t31);
      switch_ret_t29 = call_ret_t30;
      break;
  }
  return switch_ret_t29;
}

tll_ptr lam_fun_t33(tll_ptr y_v2586, tll_env env)
{
  tll_ptr call_ret_t32;
  call_ret_t32 = muln_i35(env[0], y_v2586);
  return call_ret_t32;
}

tll_ptr lam_fun_t35(tll_ptr x_v2584, tll_env env)
{
  tll_ptr lam_clo_t34;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 1, x_v2584);
  return lam_clo_t34;
}

tll_ptr eqn_i36(tll_ptr x_v2587, tll_ptr y_v2588)
{
  tll_ptr __v2589; tll_ptr call_ret_t43; tll_ptr false_t40;
  tll_ptr false_t42; tll_ptr switch_ret_t37; tll_ptr switch_ret_t38;
  tll_ptr switch_ret_t41; tll_ptr true_t39; tll_ptr x_v2590; tll_ptr y_v2591;
  switch(((tll_node)x_v2587)->tag) {
    case 14:
      switch(((tll_node)y_v2588)->tag) {
        case 14:
          instr_struct(&true_t39, 12, 0);
          switch_ret_t38 = true_t39;
          break;
        case 15:
          __v2589 = ((tll_node)y_v2588)->data[0];
          instr_struct(&false_t40, 13, 0);
          switch_ret_t38 = false_t40;
          break;
      }
      switch_ret_t37 = switch_ret_t38;
      break;
    case 15:
      x_v2590 = ((tll_node)x_v2587)->data[0];
      switch(((tll_node)y_v2588)->tag) {
        case 14:
          instr_struct(&false_t42, 13, 0);
          switch_ret_t41 = false_t42;
          break;
        case 15:
          y_v2591 = ((tll_node)y_v2588)->data[0];
          call_ret_t43 = eqn_i36(x_v2590, y_v2591);
          switch_ret_t41 = call_ret_t43;
          break;
      }
      switch_ret_t37 = switch_ret_t41;
      break;
  }
  return switch_ret_t37;
}

tll_ptr lam_fun_t45(tll_ptr y_v2594, tll_env env)
{
  tll_ptr call_ret_t44;
  call_ret_t44 = eqn_i36(env[0], y_v2594);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v2592, tll_env env)
{
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v2592);
  return lam_clo_t46;
}

tll_ptr lten_i37(tll_ptr x_v2595, tll_ptr y_v2596)
{
  tll_ptr call_ret_t53; tll_ptr false_t52; tll_ptr switch_ret_t49;
  tll_ptr switch_ret_t51; tll_ptr true_t50; tll_ptr x_v2597; tll_ptr y_v2598;
  switch(((tll_node)x_v2595)->tag) {
    case 14:
      instr_struct(&true_t50, 12, 0);
      switch_ret_t49 = true_t50;
      break;
    case 15:
      x_v2597 = ((tll_node)x_v2595)->data[0];
      switch(((tll_node)y_v2596)->tag) {
        case 14:
          instr_struct(&false_t52, 13, 0);
          switch_ret_t51 = false_t52;
          break;
        case 15:
          y_v2598 = ((tll_node)y_v2596)->data[0];
          call_ret_t53 = lten_i37(x_v2597, y_v2598);
          switch_ret_t51 = call_ret_t53;
          break;
      }
      switch_ret_t49 = switch_ret_t51;
      break;
  }
  return switch_ret_t49;
}

tll_ptr lam_fun_t55(tll_ptr y_v2601, tll_env env)
{
  tll_ptr call_ret_t54;
  call_ret_t54 = lten_i37(env[0], y_v2601);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v2599, tll_env env)
{
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v2599);
  return lam_clo_t56;
}

tll_ptr gten_i38(tll_ptr x_v2602, tll_ptr y_v2603)
{
  tll_ptr __v2604; tll_ptr call_ret_t65; tll_ptr false_t62;
  tll_ptr switch_ret_t59; tll_ptr switch_ret_t60; tll_ptr switch_ret_t63;
  tll_ptr true_t61; tll_ptr true_t64; tll_ptr x_v2605; tll_ptr y_v2606;
  switch(((tll_node)x_v2602)->tag) {
    case 14:
      switch(((tll_node)y_v2603)->tag) {
        case 14:
          instr_struct(&true_t61, 12, 0);
          switch_ret_t60 = true_t61;
          break;
        case 15:
          __v2604 = ((tll_node)y_v2603)->data[0];
          instr_struct(&false_t62, 13, 0);
          switch_ret_t60 = false_t62;
          break;
      }
      switch_ret_t59 = switch_ret_t60;
      break;
    case 15:
      x_v2605 = ((tll_node)x_v2602)->data[0];
      switch(((tll_node)y_v2603)->tag) {
        case 14:
          instr_struct(&true_t64, 12, 0);
          switch_ret_t63 = true_t64;
          break;
        case 15:
          y_v2606 = ((tll_node)y_v2603)->data[0];
          call_ret_t65 = gten_i38(x_v2605, y_v2606);
          switch_ret_t63 = call_ret_t65;
          break;
      }
      switch_ret_t59 = switch_ret_t63;
      break;
  }
  return switch_ret_t59;
}

tll_ptr lam_fun_t67(tll_ptr y_v2609, tll_env env)
{
  tll_ptr call_ret_t66;
  call_ret_t66 = gten_i38(env[0], y_v2609);
  return call_ret_t66;
}

tll_ptr lam_fun_t69(tll_ptr x_v2607, tll_env env)
{
  tll_ptr lam_clo_t68;
  instr_clo(&lam_clo_t68, &lam_fun_t67, 1, x_v2607);
  return lam_clo_t68;
}

tll_ptr cats_i41(tll_ptr s1_v2610, tll_ptr s2_v2611)
{
  tll_ptr String_t73; tll_ptr c_v2612; tll_ptr call_ret_t72;
  tll_ptr s1_v2613; tll_ptr switch_ret_t71;
  switch(((tll_node)s1_v2610)->tag) {
    case 17:
      switch_ret_t71 = s2_v2611;
      break;
    case 18:
      c_v2612 = ((tll_node)s1_v2610)->data[0];
      s1_v2613 = ((tll_node)s1_v2610)->data[1];
      call_ret_t72 = cats_i41(s1_v2613, s2_v2611);
      instr_struct(&String_t73, 18, 2, c_v2612, call_ret_t72);
      switch_ret_t71 = String_t73;
      break;
  }
  return switch_ret_t71;
}

tll_ptr lam_fun_t75(tll_ptr s2_v2616, tll_env env)
{
  tll_ptr call_ret_t74;
  call_ret_t74 = cats_i41(env[0], s2_v2616);
  return call_ret_t74;
}

tll_ptr lam_fun_t77(tll_ptr s1_v2614, tll_env env)
{
  tll_ptr lam_clo_t76;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 1, s1_v2614);
  return lam_clo_t76;
}

tll_ptr strlen_i42(tll_ptr s_v2617)
{
  tll_ptr O_t80; tll_ptr S_t82; tll_ptr __v2618; tll_ptr call_ret_t81;
  tll_ptr s_v2619; tll_ptr switch_ret_t79;
  switch(((tll_node)s_v2617)->tag) {
    case 17:
      instr_struct(&O_t80, 14, 0);
      switch_ret_t79 = O_t80;
      break;
    case 18:
      __v2618 = ((tll_node)s_v2617)->data[0];
      s_v2619 = ((tll_node)s_v2617)->data[1];
      call_ret_t81 = strlen_i42(s_v2619);
      instr_struct(&S_t82, 15, 1, call_ret_t81);
      switch_ret_t79 = S_t82;
      break;
  }
  return switch_ret_t79;
}

tll_ptr lam_fun_t84(tll_ptr s_v2620, tll_env env)
{
  tll_ptr call_ret_t83;
  call_ret_t83 = strlen_i42(s_v2620);
  return call_ret_t83;
}

tll_ptr lam_fun_t94(tll_ptr __v2637, tll_env env)
{
  tll_ptr __v2642; tll_ptr __v2643; tll_ptr ch_v2641; tll_ptr false_t92;
  tll_ptr send_ch_t91; tll_ptr tt_t93;
  instr_struct(&false_t92, 13, 0);
  instr_send(&send_ch_t91, env[0], false_t92);
  ch_v2641 = send_ch_t91;
  __v2643 = ch_v2641;
  instr_struct(&tt_t93, 11, 0);
  __v2642 = tt_t93;
  return env[1];
}

tll_ptr lam_fun_t97(tll_ptr __v2622, tll_env env)
{
  tll_ptr __v2634; tll_ptr app_ret_t96; tll_ptr ch_v2632; tll_ptr ch_v2633;
  tll_ptr ch_v2636; tll_ptr lam_clo_t95; tll_ptr prim_ch_t86;
  tll_ptr recv_msg_t89; tll_ptr s_v2635; tll_ptr send_ch_t87;
  tll_ptr switch_ret_t90; tll_ptr true_t88;
  instr_open(&prim_ch_t86, &proc_stdin);
  ch_v2632 = prim_ch_t86;
  instr_struct(&true_t88, 12, 0);
  instr_send(&send_ch_t87, ch_v2632, true_t88);
  ch_v2633 = send_ch_t87;
  instr_recv(&recv_msg_t89, ch_v2633);
  __v2634 = recv_msg_t89;
  switch(((tll_node)__v2634)->tag) {
    case 0:
      s_v2635 = ((tll_node)__v2634)->data[0];
      ch_v2636 = ((tll_node)__v2634)->data[1];
      instr_free_struct(__v2634);
      instr_clo(&lam_clo_t95, &lam_fun_t94, 2, ch_v2636, s_v2635);
      switch_ret_t90 = lam_clo_t95;
      break;
  }
  instr_app(&app_ret_t96, switch_ret_t90, 0);
  instr_free_clo(switch_ret_t90);
  return app_ret_t96;
}

tll_ptr readline_i49(tll_ptr __v2621)
{
  tll_ptr lam_clo_t98;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  return lam_clo_t98;
}

tll_ptr lam_fun_t100(tll_ptr __v2644, tll_env env)
{
  tll_ptr call_ret_t99;
  call_ret_t99 = readline_i49(__v2644);
  return call_ret_t99;
}

tll_ptr lam_fun_t109(tll_ptr __v2646, tll_env env)
{
  tll_ptr __v2656; tll_ptr ch_v2652; tll_ptr ch_v2653; tll_ptr ch_v2654;
  tll_ptr ch_v2655; tll_ptr false_t107; tll_ptr prim_ch_t102;
  tll_ptr send_ch_t103; tll_ptr send_ch_t105; tll_ptr send_ch_t106;
  tll_ptr true_t104; tll_ptr tt_t108;
  instr_open(&prim_ch_t102, &proc_stdout);
  ch_v2652 = prim_ch_t102;
  instr_struct(&true_t104, 12, 0);
  instr_send(&send_ch_t103, ch_v2652, true_t104);
  ch_v2653 = send_ch_t103;
  instr_send(&send_ch_t105, ch_v2653, env[0]);
  ch_v2654 = send_ch_t105;
  instr_struct(&false_t107, 13, 0);
  instr_send(&send_ch_t106, ch_v2654, false_t107);
  ch_v2655 = send_ch_t106;
  __v2656 = ch_v2655;
  instr_struct(&tt_t108, 11, 0);
  return tt_t108;
}

tll_ptr print_i50(tll_ptr s_v2645)
{
  tll_ptr lam_clo_t110;
  instr_clo(&lam_clo_t110, &lam_fun_t109, 1, s_v2645);
  return lam_clo_t110;
}

tll_ptr lam_fun_t112(tll_ptr s_v2657, tll_env env)
{
  tll_ptr call_ret_t111;
  call_ret_t111 = print_i50(s_v2657);
  return call_ret_t111;
}

tll_ptr lam_fun_t121(tll_ptr __v2659, tll_env env)
{
  tll_ptr __v2669; tll_ptr ch_v2665; tll_ptr ch_v2666; tll_ptr ch_v2667;
  tll_ptr ch_v2668; tll_ptr false_t119; tll_ptr prim_ch_t114;
  tll_ptr send_ch_t115; tll_ptr send_ch_t117; tll_ptr send_ch_t118;
  tll_ptr true_t116; tll_ptr tt_t120;
  instr_open(&prim_ch_t114, &proc_stderr);
  ch_v2665 = prim_ch_t114;
  instr_struct(&true_t116, 12, 0);
  instr_send(&send_ch_t115, ch_v2665, true_t116);
  ch_v2666 = send_ch_t115;
  instr_send(&send_ch_t117, ch_v2666, env[0]);
  ch_v2667 = send_ch_t117;
  instr_struct(&false_t119, 13, 0);
  instr_send(&send_ch_t118, ch_v2667, false_t119);
  ch_v2668 = send_ch_t118;
  __v2669 = ch_v2668;
  instr_struct(&tt_t120, 11, 0);
  return tt_t120;
}

tll_ptr prerr_i51(tll_ptr s_v2658)
{
  tll_ptr lam_clo_t122;
  instr_clo(&lam_clo_t122, &lam_fun_t121, 1, s_v2658);
  return lam_clo_t122;
}

tll_ptr lam_fun_t124(tll_ptr s_v2670, tll_env env)
{
  tll_ptr call_ret_t123;
  call_ret_t123 = prerr_i51(s_v2670);
  return call_ret_t123;
}

tll_ptr appendUU_i59(tll_ptr A_v2671, tll_ptr xs_v2672, tll_ptr ys_v2673)
{
  tll_ptr ConsUU_t128; tll_ptr call_ret_t127; tll_ptr switch_ret_t126;
  tll_ptr x_v2674; tll_ptr xs_v2675;
  switch(((tll_node)xs_v2672)->tag) {
    case 25:
      switch_ret_t126 = ys_v2673;
      break;
    case 26:
      x_v2674 = ((tll_node)xs_v2672)->data[0];
      xs_v2675 = ((tll_node)xs_v2672)->data[1];
      call_ret_t127 = appendUU_i59(0, xs_v2675, ys_v2673);
      instr_struct(&ConsUU_t128, 26, 2, x_v2674, call_ret_t127);
      switch_ret_t126 = ConsUU_t128;
      break;
  }
  return switch_ret_t126;
}

tll_ptr lam_fun_t130(tll_ptr ys_v2681, tll_env env)
{
  tll_ptr call_ret_t129;
  call_ret_t129 = appendUU_i59(env[1], env[0], ys_v2681);
  return call_ret_t129;
}

tll_ptr lam_fun_t132(tll_ptr xs_v2679, tll_env env)
{
  tll_ptr lam_clo_t131;
  instr_clo(&lam_clo_t131, &lam_fun_t130, 2, xs_v2679, env[0]);
  return lam_clo_t131;
}

tll_ptr lam_fun_t134(tll_ptr A_v2676, tll_env env)
{
  tll_ptr lam_clo_t133;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 1, A_v2676);
  return lam_clo_t133;
}

tll_ptr appendUL_i58(tll_ptr A_v2682, tll_ptr xs_v2683, tll_ptr ys_v2684)
{
  tll_ptr ConsUL_t138; tll_ptr call_ret_t137; tll_ptr switch_ret_t136;
  tll_ptr x_v2685; tll_ptr xs_v2686;
  switch(((tll_node)xs_v2683)->tag) {
    case 23:
      instr_free_struct(xs_v2683);
      switch_ret_t136 = ys_v2684;
      break;
    case 24:
      x_v2685 = ((tll_node)xs_v2683)->data[0];
      xs_v2686 = ((tll_node)xs_v2683)->data[1];
      instr_free_struct(xs_v2683);
      call_ret_t137 = appendUL_i58(0, xs_v2686, ys_v2684);
      instr_struct(&ConsUL_t138, 24, 2, x_v2685, call_ret_t137);
      switch_ret_t136 = ConsUL_t138;
      break;
  }
  return switch_ret_t136;
}

tll_ptr lam_fun_t140(tll_ptr ys_v2692, tll_env env)
{
  tll_ptr call_ret_t139;
  call_ret_t139 = appendUL_i58(env[1], env[0], ys_v2692);
  return call_ret_t139;
}

tll_ptr lam_fun_t142(tll_ptr xs_v2690, tll_env env)
{
  tll_ptr lam_clo_t141;
  instr_clo(&lam_clo_t141, &lam_fun_t140, 2, xs_v2690, env[0]);
  return lam_clo_t141;
}

tll_ptr lam_fun_t144(tll_ptr A_v2687, tll_env env)
{
  tll_ptr lam_clo_t143;
  instr_clo(&lam_clo_t143, &lam_fun_t142, 1, A_v2687);
  return lam_clo_t143;
}

tll_ptr appendLL_i56(tll_ptr A_v2693, tll_ptr xs_v2694, tll_ptr ys_v2695)
{
  tll_ptr ConsLL_t148; tll_ptr call_ret_t147; tll_ptr switch_ret_t146;
  tll_ptr x_v2696; tll_ptr xs_v2697;
  switch(((tll_node)xs_v2694)->tag) {
    case 19:
      instr_free_struct(xs_v2694);
      switch_ret_t146 = ys_v2695;
      break;
    case 20:
      x_v2696 = ((tll_node)xs_v2694)->data[0];
      xs_v2697 = ((tll_node)xs_v2694)->data[1];
      instr_free_struct(xs_v2694);
      call_ret_t147 = appendLL_i56(0, xs_v2697, ys_v2695);
      instr_struct(&ConsLL_t148, 20, 2, x_v2696, call_ret_t147);
      switch_ret_t146 = ConsLL_t148;
      break;
  }
  return switch_ret_t146;
}

tll_ptr lam_fun_t150(tll_ptr ys_v2703, tll_env env)
{
  tll_ptr call_ret_t149;
  call_ret_t149 = appendLL_i56(env[1], env[0], ys_v2703);
  return call_ret_t149;
}

tll_ptr lam_fun_t152(tll_ptr xs_v2701, tll_env env)
{
  tll_ptr lam_clo_t151;
  instr_clo(&lam_clo_t151, &lam_fun_t150, 2, xs_v2701, env[0]);
  return lam_clo_t151;
}

tll_ptr lam_fun_t154(tll_ptr A_v2698, tll_env env)
{
  tll_ptr lam_clo_t153;
  instr_clo(&lam_clo_t153, &lam_fun_t152, 1, A_v2698);
  return lam_clo_t153;
}

tll_ptr idU_i70(tll_ptr A_v2704, tll_ptr x_v2705)
{
  
  
  return x_v2705;
}

tll_ptr lam_fun_t164(tll_ptr x_v2708, tll_env env)
{
  tll_ptr call_ret_t163;
  call_ret_t163 = idU_i70(env[0], x_v2708);
  return call_ret_t163;
}

tll_ptr lam_fun_t166(tll_ptr A_v2706, tll_env env)
{
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, A_v2706);
  return lam_clo_t165;
}

tll_ptr idL_i69(tll_ptr A_v2709, tll_ptr x_v2710)
{
  
  
  return x_v2710;
}

tll_ptr lam_fun_t169(tll_ptr x_v2713, tll_env env)
{
  tll_ptr call_ret_t168;
  call_ret_t168 = idL_i69(env[0], x_v2713);
  return call_ret_t168;
}

tll_ptr lam_fun_t171(tll_ptr A_v2711, tll_env env)
{
  tll_ptr lam_clo_t170;
  instr_clo(&lam_clo_t170, &lam_fun_t169, 1, A_v2711);
  return lam_clo_t170;
}

int main()
{
  instr_init();
  tll_ptr ConsUU_t158; tll_ptr ConsUU_t161; tll_ptr NilUU_t157;
  tll_ptr NilUU_t160; tll_ptr O_t156; tll_ptr O_t159; tll_ptr app_ret_t175;
  tll_ptr app_ret_t179; tll_ptr call_ret_t162; tll_ptr call_ret_t173;
  tll_ptr call_ret_t176; tll_ptr call_ret_t177; tll_ptr call_ret_t178;
  tll_ptr lam_clo_t101; tll_ptr lam_clo_t113; tll_ptr lam_clo_t125;
  tll_ptr lam_clo_t135; tll_ptr lam_clo_t14; tll_ptr lam_clo_t145;
  tll_ptr lam_clo_t155; tll_ptr lam_clo_t167; tll_ptr lam_clo_t172;
  tll_ptr lam_clo_t20; tll_ptr lam_clo_t28; tll_ptr lam_clo_t36;
  tll_ptr lam_clo_t48; tll_ptr lam_clo_t58; tll_ptr lam_clo_t7;
  tll_ptr lam_clo_t70; tll_ptr lam_clo_t78; tll_ptr lam_clo_t85;
  tll_ptr s_v2714; tll_ptr tt_t174;
  instr_clo(&lam_clo_t7, &lam_fun_t6, 0);
  andbclo_i71 = lam_clo_t7;
  instr_clo(&lam_clo_t14, &lam_fun_t13, 0);
  orbclo_i72 = lam_clo_t14;
  instr_clo(&lam_clo_t20, &lam_fun_t19, 0);
  notbclo_i73 = lam_clo_t20;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  addnclo_i74 = lam_clo_t28;
  instr_clo(&lam_clo_t36, &lam_fun_t35, 0);
  mulnclo_i75 = lam_clo_t36;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  eqnclo_i76 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  ltenclo_i77 = lam_clo_t58;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 0);
  gtenclo_i78 = lam_clo_t70;
  instr_clo(&lam_clo_t78, &lam_fun_t77, 0);
  catsclo_i79 = lam_clo_t78;
  instr_clo(&lam_clo_t85, &lam_fun_t84, 0);
  strlenclo_i80 = lam_clo_t85;
  instr_clo(&lam_clo_t101, &lam_fun_t100, 0);
  readlineclo_i81 = lam_clo_t101;
  instr_clo(&lam_clo_t113, &lam_fun_t112, 0);
  printclo_i82 = lam_clo_t113;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 0);
  prerrclo_i83 = lam_clo_t125;
  instr_clo(&lam_clo_t135, &lam_fun_t134, 0);
  appendUUclo_i84 = lam_clo_t135;
  instr_clo(&lam_clo_t145, &lam_fun_t144, 0);
  appendULclo_i85 = lam_clo_t145;
  instr_clo(&lam_clo_t155, &lam_fun_t154, 0);
  appendLLclo_i86 = lam_clo_t155;
  instr_struct(&O_t156, 14, 0);
  instr_struct(&NilUU_t157, 25, 0);
  instr_struct(&ConsUU_t158, 26, 2, O_t156, NilUU_t157);
  ls0_i66 = ConsUU_t158;
  instr_struct(&O_t159, 14, 0);
  instr_struct(&NilUU_t160, 25, 0);
  instr_struct(&ConsUU_t161, 26, 2, O_t159, NilUU_t160);
  ls1_i67 = ConsUU_t161;
  call_ret_t162 = appendUU_i59(0, ls0_i66, ls1_i67);
  ls2_i68 = call_ret_t162;
  instr_clo(&lam_clo_t167, &lam_fun_t166, 0);
  idUclo_i87 = lam_clo_t167;
  instr_clo(&lam_clo_t172, &lam_fun_t171, 0);
  idLclo_i88 = lam_clo_t172;
  instr_struct(&tt_t174, 11, 0);
  call_ret_t173 = readline_i49(tt_t174);
  instr_app(&app_ret_t175, call_ret_t173, 0);
  instr_free_clo(call_ret_t173);
  s_v2714 = app_ret_t175;
  call_ret_t178 = idU_i70(0, s_v2714);
  call_ret_t177 = print_i50(call_ret_t178);
  call_ret_t176 = idL_i69(0, call_ret_t177);
  instr_app(&app_ret_t179, call_ret_t176, 0);
  instr_free_clo(call_ret_t176);
  instr_free_struct(app_ret_t179);
  return 0;
}

