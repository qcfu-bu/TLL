#include "runtime.h"

tll_ptr addnclo_i47;
tll_ptr andbclo_i44;
tll_ptr catsclo_i52;
tll_ptr eqnclo_i49;
tll_ptr gtenclo_i51;
tll_ptr ltenclo_i50;
tll_ptr mulnclo_i48;
tll_ptr notbclo_i46;
tll_ptr orbclo_i45;
tll_ptr prerrclo_i56;
tll_ptr printclo_i55;
tll_ptr readlineclo_i54;
tll_ptr strlenclo_i53;

tll_ptr andb_i23(tll_ptr b1_v1583, tll_ptr b2_v1584)
{
  tll_ptr false_t2; tll_ptr switch_ret_t1;
  switch(((tll_node)b1_v1583)->tag) {
    case 10:
      switch_ret_t1 = b2_v1584;
      break;
    case 11:
      instr_struct(&false_t2, 11, 0);
      switch_ret_t1 = false_t2;
      break;
  }
  return switch_ret_t1;
}

tll_ptr lam_fun_t4(tll_ptr b2_v1587, tll_env env)
{
  tll_ptr call_ret_t3;
  call_ret_t3 = andb_i23(env[0], b2_v1587);
  return call_ret_t3;
}

tll_ptr lam_fun_t6(tll_ptr b1_v1585, tll_env env)
{
  tll_ptr lam_clo_t5;
  instr_clo(&lam_clo_t5, &lam_fun_t4, 1, b1_v1585);
  return lam_clo_t5;
}

tll_ptr orb_i24(tll_ptr b1_v1588, tll_ptr b2_v1589)
{
  tll_ptr switch_ret_t8; tll_ptr true_t9;
  switch(((tll_node)b1_v1588)->tag) {
    case 10:
      instr_struct(&true_t9, 10, 0);
      switch_ret_t8 = true_t9;
      break;
    case 11:
      switch_ret_t8 = b2_v1589;
      break;
  }
  return switch_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b2_v1592, tll_env env)
{
  tll_ptr call_ret_t10;
  call_ret_t10 = orb_i24(env[0], b2_v1592);
  return call_ret_t10;
}

tll_ptr lam_fun_t13(tll_ptr b1_v1590, tll_env env)
{
  tll_ptr lam_clo_t12;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 1, b1_v1590);
  return lam_clo_t12;
}

tll_ptr notb_i25(tll_ptr b_v1593)
{
  tll_ptr false_t16; tll_ptr switch_ret_t15; tll_ptr true_t17;
  switch(((tll_node)b_v1593)->tag) {
    case 10:
      instr_struct(&false_t16, 11, 0);
      switch_ret_t15 = false_t16;
      break;
    case 11:
      instr_struct(&true_t17, 10, 0);
      switch_ret_t15 = true_t17;
      break;
  }
  return switch_ret_t15;
}

tll_ptr lam_fun_t19(tll_ptr b_v1594, tll_env env)
{
  tll_ptr call_ret_t18;
  call_ret_t18 = notb_i25(b_v1594);
  return call_ret_t18;
}

tll_ptr addn_i26(tll_ptr x_v1595, tll_ptr y_v1596)
{
  tll_ptr S_t23; tll_ptr call_ret_t22; tll_ptr switch_ret_t21;
  tll_ptr x_v1597;
  switch(((tll_node)x_v1595)->tag) {
    case 12:
      switch_ret_t21 = y_v1596;
      break;
    case 13:
      x_v1597 = ((tll_node)x_v1595)->data[0];
      call_ret_t22 = addn_i26(x_v1597, y_v1596);
      instr_struct(&S_t23, 13, 1, call_ret_t22);
      switch_ret_t21 = S_t23;
      break;
  }
  return switch_ret_t21;
}

tll_ptr lam_fun_t25(tll_ptr y_v1600, tll_env env)
{
  tll_ptr call_ret_t24;
  call_ret_t24 = addn_i26(env[0], y_v1600);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr x_v1598, tll_env env)
{
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, x_v1598);
  return lam_clo_t26;
}

tll_ptr muln_i27(tll_ptr x_v1601, tll_ptr y_v1602)
{
  tll_ptr call_ret_t30; tll_ptr call_ret_t31; tll_ptr switch_ret_t29;
  tll_ptr x_v1603;
  switch(((tll_node)x_v1601)->tag) {
    case 12:
      switch_ret_t29 = y_v1602;
      break;
    case 13:
      x_v1603 = ((tll_node)x_v1601)->data[0];
      call_ret_t31 = muln_i27(x_v1603, y_v1602);
      call_ret_t30 = addn_i26(y_v1602, call_ret_t31);
      switch_ret_t29 = call_ret_t30;
      break;
  }
  return switch_ret_t29;
}

tll_ptr lam_fun_t33(tll_ptr y_v1606, tll_env env)
{
  tll_ptr call_ret_t32;
  call_ret_t32 = muln_i27(env[0], y_v1606);
  return call_ret_t32;
}

tll_ptr lam_fun_t35(tll_ptr x_v1604, tll_env env)
{
  tll_ptr lam_clo_t34;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 1, x_v1604);
  return lam_clo_t34;
}

tll_ptr eqn_i28(tll_ptr x_v1607, tll_ptr y_v1608)
{
  tll_ptr __v1609; tll_ptr call_ret_t43; tll_ptr false_t40;
  tll_ptr false_t42; tll_ptr switch_ret_t37; tll_ptr switch_ret_t38;
  tll_ptr switch_ret_t41; tll_ptr true_t39; tll_ptr x_v1610; tll_ptr y_v1611;
  switch(((tll_node)x_v1607)->tag) {
    case 12:
      switch(((tll_node)y_v1608)->tag) {
        case 12:
          instr_struct(&true_t39, 10, 0);
          switch_ret_t38 = true_t39;
          break;
        case 13:
          __v1609 = ((tll_node)y_v1608)->data[0];
          instr_struct(&false_t40, 11, 0);
          switch_ret_t38 = false_t40;
          break;
      }
      switch_ret_t37 = switch_ret_t38;
      break;
    case 13:
      x_v1610 = ((tll_node)x_v1607)->data[0];
      switch(((tll_node)y_v1608)->tag) {
        case 12:
          instr_struct(&false_t42, 11, 0);
          switch_ret_t41 = false_t42;
          break;
        case 13:
          y_v1611 = ((tll_node)y_v1608)->data[0];
          call_ret_t43 = eqn_i28(x_v1610, y_v1611);
          switch_ret_t41 = call_ret_t43;
          break;
      }
      switch_ret_t37 = switch_ret_t41;
      break;
  }
  return switch_ret_t37;
}

tll_ptr lam_fun_t45(tll_ptr y_v1614, tll_env env)
{
  tll_ptr call_ret_t44;
  call_ret_t44 = eqn_i28(env[0], y_v1614);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v1612, tll_env env)
{
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v1612);
  return lam_clo_t46;
}

tll_ptr lten_i29(tll_ptr x_v1615, tll_ptr y_v1616)
{
  tll_ptr call_ret_t53; tll_ptr false_t52; tll_ptr switch_ret_t49;
  tll_ptr switch_ret_t51; tll_ptr true_t50; tll_ptr x_v1617; tll_ptr y_v1618;
  switch(((tll_node)x_v1615)->tag) {
    case 12:
      instr_struct(&true_t50, 10, 0);
      switch_ret_t49 = true_t50;
      break;
    case 13:
      x_v1617 = ((tll_node)x_v1615)->data[0];
      switch(((tll_node)y_v1616)->tag) {
        case 12:
          instr_struct(&false_t52, 11, 0);
          switch_ret_t51 = false_t52;
          break;
        case 13:
          y_v1618 = ((tll_node)y_v1616)->data[0];
          call_ret_t53 = lten_i29(x_v1617, y_v1618);
          switch_ret_t51 = call_ret_t53;
          break;
      }
      switch_ret_t49 = switch_ret_t51;
      break;
  }
  return switch_ret_t49;
}

tll_ptr lam_fun_t55(tll_ptr y_v1621, tll_env env)
{
  tll_ptr call_ret_t54;
  call_ret_t54 = lten_i29(env[0], y_v1621);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v1619, tll_env env)
{
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v1619);
  return lam_clo_t56;
}

tll_ptr gten_i30(tll_ptr x_v1622, tll_ptr y_v1623)
{
  tll_ptr __v1624; tll_ptr call_ret_t65; tll_ptr false_t62;
  tll_ptr switch_ret_t59; tll_ptr switch_ret_t60; tll_ptr switch_ret_t63;
  tll_ptr true_t61; tll_ptr true_t64; tll_ptr x_v1625; tll_ptr y_v1626;
  switch(((tll_node)x_v1622)->tag) {
    case 12:
      switch(((tll_node)y_v1623)->tag) {
        case 12:
          instr_struct(&true_t61, 10, 0);
          switch_ret_t60 = true_t61;
          break;
        case 13:
          __v1624 = ((tll_node)y_v1623)->data[0];
          instr_struct(&false_t62, 11, 0);
          switch_ret_t60 = false_t62;
          break;
      }
      switch_ret_t59 = switch_ret_t60;
      break;
    case 13:
      x_v1625 = ((tll_node)x_v1622)->data[0];
      switch(((tll_node)y_v1623)->tag) {
        case 12:
          instr_struct(&true_t64, 10, 0);
          switch_ret_t63 = true_t64;
          break;
        case 13:
          y_v1626 = ((tll_node)y_v1623)->data[0];
          call_ret_t65 = gten_i30(x_v1625, y_v1626);
          switch_ret_t63 = call_ret_t65;
          break;
      }
      switch_ret_t59 = switch_ret_t63;
      break;
  }
  return switch_ret_t59;
}

tll_ptr lam_fun_t67(tll_ptr y_v1629, tll_env env)
{
  tll_ptr call_ret_t66;
  call_ret_t66 = gten_i30(env[0], y_v1629);
  return call_ret_t66;
}

tll_ptr lam_fun_t69(tll_ptr x_v1627, tll_env env)
{
  tll_ptr lam_clo_t68;
  instr_clo(&lam_clo_t68, &lam_fun_t67, 1, x_v1627);
  return lam_clo_t68;
}

tll_ptr cats_i33(tll_ptr s1_v1630, tll_ptr s2_v1631)
{
  tll_ptr String_t73; tll_ptr c_v1632; tll_ptr call_ret_t72;
  tll_ptr s1_v1633; tll_ptr switch_ret_t71;
  switch(((tll_node)s1_v1630)->tag) {
    case 15:
      switch_ret_t71 = s2_v1631;
      break;
    case 16:
      c_v1632 = ((tll_node)s1_v1630)->data[0];
      s1_v1633 = ((tll_node)s1_v1630)->data[1];
      call_ret_t72 = cats_i33(s1_v1633, s2_v1631);
      instr_struct(&String_t73, 16, 2, c_v1632, call_ret_t72);
      switch_ret_t71 = String_t73;
      break;
  }
  return switch_ret_t71;
}

tll_ptr lam_fun_t75(tll_ptr s2_v1636, tll_env env)
{
  tll_ptr call_ret_t74;
  call_ret_t74 = cats_i33(env[0], s2_v1636);
  return call_ret_t74;
}

tll_ptr lam_fun_t77(tll_ptr s1_v1634, tll_env env)
{
  tll_ptr lam_clo_t76;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 1, s1_v1634);
  return lam_clo_t76;
}

tll_ptr strlen_i34(tll_ptr s_v1637)
{
  tll_ptr O_t80; tll_ptr S_t82; tll_ptr __v1638; tll_ptr call_ret_t81;
  tll_ptr s_v1639; tll_ptr switch_ret_t79;
  switch(((tll_node)s_v1637)->tag) {
    case 15:
      instr_struct(&O_t80, 12, 0);
      switch_ret_t79 = O_t80;
      break;
    case 16:
      __v1638 = ((tll_node)s_v1637)->data[0];
      s_v1639 = ((tll_node)s_v1637)->data[1];
      call_ret_t81 = strlen_i34(s_v1639);
      instr_struct(&S_t82, 13, 1, call_ret_t81);
      switch_ret_t79 = S_t82;
      break;
  }
  return switch_ret_t79;
}

tll_ptr lam_fun_t84(tll_ptr s_v1640, tll_env env)
{
  tll_ptr call_ret_t83;
  call_ret_t83 = strlen_i34(s_v1640);
  return call_ret_t83;
}

tll_ptr lam_fun_t94(tll_ptr __v1657, tll_env env)
{
  tll_ptr __v1662; tll_ptr __v1663; tll_ptr ch_v1661; tll_ptr false_t92;
  tll_ptr send_ch_t91; tll_ptr tt_t93;
  instr_struct(&false_t92, 11, 0);
  instr_send(&send_ch_t91, env[0], false_t92);
  ch_v1661 = send_ch_t91;
  __v1663 = ch_v1661;
  instr_struct(&tt_t93, 9, 0);
  __v1662 = tt_t93;
  return env[1];
}

tll_ptr lam_fun_t97(tll_ptr __v1642, tll_env env)
{
  tll_ptr __v1654; tll_ptr app_ret_t96; tll_ptr ch_v1652; tll_ptr ch_v1653;
  tll_ptr ch_v1656; tll_ptr lam_clo_t95; tll_ptr prim_ch_t86;
  tll_ptr recv_msg_t89; tll_ptr s_v1655; tll_ptr send_ch_t87;
  tll_ptr switch_ret_t90; tll_ptr true_t88;
  instr_open(&prim_ch_t86, &proc_stdin);
  ch_v1652 = prim_ch_t86;
  instr_struct(&true_t88, 10, 0);
  instr_send(&send_ch_t87, ch_v1652, true_t88);
  ch_v1653 = send_ch_t87;
  instr_recv(&recv_msg_t89, ch_v1653);
  __v1654 = recv_msg_t89;
  switch(((tll_node)__v1654)->tag) {
    case 0:
      s_v1655 = ((tll_node)__v1654)->data[0];
      ch_v1656 = ((tll_node)__v1654)->data[1];
      instr_free_struct(__v1654);
      instr_clo(&lam_clo_t95, &lam_fun_t94, 2, ch_v1656, s_v1655);
      switch_ret_t90 = lam_clo_t95;
      break;
  }
  instr_app(&app_ret_t96, switch_ret_t90, 0);
  instr_free_clo(switch_ret_t90);
  return app_ret_t96;
}

tll_ptr readline_i41(tll_ptr __v1641)
{
  tll_ptr lam_clo_t98;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  return lam_clo_t98;
}

tll_ptr lam_fun_t100(tll_ptr __v1664, tll_env env)
{
  tll_ptr call_ret_t99;
  call_ret_t99 = readline_i41(__v1664);
  return call_ret_t99;
}

tll_ptr lam_fun_t109(tll_ptr __v1666, tll_env env)
{
  tll_ptr __v1676; tll_ptr ch_v1672; tll_ptr ch_v1673; tll_ptr ch_v1674;
  tll_ptr ch_v1675; tll_ptr false_t107; tll_ptr prim_ch_t102;
  tll_ptr send_ch_t103; tll_ptr send_ch_t105; tll_ptr send_ch_t106;
  tll_ptr true_t104; tll_ptr tt_t108;
  instr_open(&prim_ch_t102, &proc_stdout);
  ch_v1672 = prim_ch_t102;
  instr_struct(&true_t104, 10, 0);
  instr_send(&send_ch_t103, ch_v1672, true_t104);
  ch_v1673 = send_ch_t103;
  instr_send(&send_ch_t105, ch_v1673, env[0]);
  ch_v1674 = send_ch_t105;
  instr_struct(&false_t107, 11, 0);
  instr_send(&send_ch_t106, ch_v1674, false_t107);
  ch_v1675 = send_ch_t106;
  __v1676 = ch_v1675;
  instr_struct(&tt_t108, 9, 0);
  return tt_t108;
}

tll_ptr print_i42(tll_ptr s_v1665)
{
  tll_ptr lam_clo_t110;
  instr_clo(&lam_clo_t110, &lam_fun_t109, 1, s_v1665);
  return lam_clo_t110;
}

tll_ptr lam_fun_t112(tll_ptr s_v1677, tll_env env)
{
  tll_ptr call_ret_t111;
  call_ret_t111 = print_i42(s_v1677);
  return call_ret_t111;
}

tll_ptr lam_fun_t121(tll_ptr __v1679, tll_env env)
{
  tll_ptr __v1689; tll_ptr ch_v1685; tll_ptr ch_v1686; tll_ptr ch_v1687;
  tll_ptr ch_v1688; tll_ptr false_t119; tll_ptr prim_ch_t114;
  tll_ptr send_ch_t115; tll_ptr send_ch_t117; tll_ptr send_ch_t118;
  tll_ptr true_t116; tll_ptr tt_t120;
  instr_open(&prim_ch_t114, &proc_stderr);
  ch_v1685 = prim_ch_t114;
  instr_struct(&true_t116, 10, 0);
  instr_send(&send_ch_t115, ch_v1685, true_t116);
  ch_v1686 = send_ch_t115;
  instr_send(&send_ch_t117, ch_v1686, env[0]);
  ch_v1687 = send_ch_t117;
  instr_struct(&false_t119, 11, 0);
  instr_send(&send_ch_t118, ch_v1687, false_t119);
  ch_v1688 = send_ch_t118;
  __v1689 = ch_v1688;
  instr_struct(&tt_t120, 9, 0);
  return tt_t120;
}

tll_ptr prerr_i43(tll_ptr s_v1678)
{
  tll_ptr lam_clo_t122;
  instr_clo(&lam_clo_t122, &lam_fun_t121, 1, s_v1678);
  return lam_clo_t122;
}

tll_ptr lam_fun_t124(tll_ptr s_v1690, tll_env env)
{
  tll_ptr call_ret_t123;
  call_ret_t123 = prerr_i43(s_v1690);
  return call_ret_t123;
}

tll_ptr lam_fun_t159(tll_ptr __v1693, tll_env env)
{
  tll_ptr __v1697; tll_ptr app_ret_t152; tll_ptr app_ret_t154;
  tll_ptr app_ret_t155; tll_ptr app_ret_t157; tll_ptr app_ret_t158;
  tll_ptr call_ret_t150; tll_ptr call_ret_t153; tll_ptr call_ret_t156;
  tll_ptr s_v1696; tll_ptr tt_t151;
  instr_struct(&tt_t151, 9, 0);
  call_ret_t150 = readline_i41(tt_t151);
  instr_app(&app_ret_t152, call_ret_t150, 0);
  instr_free_clo(call_ret_t150);
  s_v1696 = app_ret_t152;
  instr_app(&app_ret_t154, env[1], s_v1696);
  call_ret_t153 = print_i42(app_ret_t154);
  instr_app(&app_ret_t155, call_ret_t153, 0);
  instr_free_clo(call_ret_t153);
  __v1697 = app_ret_t155;
  instr_app(&app_ret_t157, env[0], s_v1696);
  call_ret_t156 = print_i42(app_ret_t157);
  instr_app(&app_ret_t158, call_ret_t156, 0);
  instr_free_clo(call_ret_t156);
  return app_ret_t158;
}

int main()
{
  instr_init();
  tll_ptr Ascii_t134; tll_ptr Ascii_t146; tll_ptr EmptyString_t135;
  tll_ptr EmptyString_t147; tll_ptr String_t136; tll_ptr String_t148;
  tll_ptr app_ret_t137; tll_ptr app_ret_t149; tll_ptr app_ret_t161;
  tll_ptr f_v1691; tll_ptr false_t126; tll_ptr false_t129;
  tll_ptr false_t130; tll_ptr false_t131; tll_ptr false_t132;
  tll_ptr false_t138; tll_ptr false_t141; tll_ptr false_t142;
  tll_ptr false_t143; tll_ptr false_t145; tll_ptr g_v1692;
  tll_ptr lam_clo_t101; tll_ptr lam_clo_t113; tll_ptr lam_clo_t125;
  tll_ptr lam_clo_t14; tll_ptr lam_clo_t160; tll_ptr lam_clo_t20;
  tll_ptr lam_clo_t28; tll_ptr lam_clo_t36; tll_ptr lam_clo_t48;
  tll_ptr lam_clo_t58; tll_ptr lam_clo_t7; tll_ptr lam_clo_t70;
  tll_ptr lam_clo_t78; tll_ptr lam_clo_t85; tll_ptr true_t127;
  tll_ptr true_t128; tll_ptr true_t133; tll_ptr true_t139; tll_ptr true_t140;
  tll_ptr true_t144;
  instr_clo(&lam_clo_t7, &lam_fun_t6, 0);
  andbclo_i44 = lam_clo_t7;
  instr_clo(&lam_clo_t14, &lam_fun_t13, 0);
  orbclo_i45 = lam_clo_t14;
  instr_clo(&lam_clo_t20, &lam_fun_t19, 0);
  notbclo_i46 = lam_clo_t20;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  addnclo_i47 = lam_clo_t28;
  instr_clo(&lam_clo_t36, &lam_fun_t35, 0);
  mulnclo_i48 = lam_clo_t36;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  eqnclo_i49 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  ltenclo_i50 = lam_clo_t58;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 0);
  gtenclo_i51 = lam_clo_t70;
  instr_clo(&lam_clo_t78, &lam_fun_t77, 0);
  catsclo_i52 = lam_clo_t78;
  instr_clo(&lam_clo_t85, &lam_fun_t84, 0);
  strlenclo_i53 = lam_clo_t85;
  instr_clo(&lam_clo_t101, &lam_fun_t100, 0);
  readlineclo_i54 = lam_clo_t101;
  instr_clo(&lam_clo_t113, &lam_fun_t112, 0);
  printclo_i55 = lam_clo_t113;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 0);
  prerrclo_i56 = lam_clo_t125;
  instr_struct(&false_t126, 11, 0);
  instr_struct(&true_t127, 10, 0);
  instr_struct(&true_t128, 10, 0);
  instr_struct(&false_t129, 11, 0);
  instr_struct(&false_t130, 11, 0);
  instr_struct(&false_t131, 11, 0);
  instr_struct(&false_t132, 11, 0);
  instr_struct(&true_t133, 10, 0);
  instr_struct(&Ascii_t134, 14, 8,
               false_t126, true_t127, true_t128, false_t129, false_t130,
               false_t131, false_t132, true_t133);
  instr_struct(&EmptyString_t135, 15, 0);
  instr_struct(&String_t136, 16, 2, Ascii_t134, EmptyString_t135);
  instr_app(&app_ret_t137, catsclo_i52, String_t136);
  f_v1691 = app_ret_t137;
  instr_struct(&false_t138, 11, 0);
  instr_struct(&true_t139, 10, 0);
  instr_struct(&true_t140, 10, 0);
  instr_struct(&false_t141, 11, 0);
  instr_struct(&false_t142, 11, 0);
  instr_struct(&false_t143, 11, 0);
  instr_struct(&true_t144, 10, 0);
  instr_struct(&false_t145, 11, 0);
  instr_struct(&Ascii_t146, 14, 8,
               false_t138, true_t139, true_t140, false_t141, false_t142,
               false_t143, true_t144, false_t145);
  instr_struct(&EmptyString_t147, 15, 0);
  instr_struct(&String_t148, 16, 2, Ascii_t146, EmptyString_t147);
  instr_app(&app_ret_t149, catsclo_i52, String_t148);
  g_v1692 = app_ret_t149;
  instr_clo(&lam_clo_t160, &lam_fun_t159, 2, g_v1692, f_v1691);
  instr_app(&app_ret_t161, lam_clo_t160, 0);
  instr_free_clo(lam_clo_t160);
  instr_free_struct(app_ret_t161);
  return 0;
}

