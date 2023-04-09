#include "runtime.h"

tll_ptr addnclo_i49;
tll_ptr andbclo_i46;
tll_ptr app_ret_t141;
tll_ptr catsclo_i54;
tll_ptr eqnclo_i51;
tll_ptr gtenclo_i53;
tll_ptr lam_clo_t101;
tll_ptr lam_clo_t113;
tll_ptr lam_clo_t125;
tll_ptr lam_clo_t134;
tll_ptr lam_clo_t137;
tll_ptr lam_clo_t14;
tll_ptr lam_clo_t140;
tll_ptr lam_clo_t20;
tll_ptr lam_clo_t28;
tll_ptr lam_clo_t36;
tll_ptr lam_clo_t48;
tll_ptr lam_clo_t58;
tll_ptr lam_clo_t7;
tll_ptr lam_clo_t70;
tll_ptr lam_clo_t78;
tll_ptr lam_clo_t85;
tll_ptr ltenclo_i52;
tll_ptr mulnclo_i50;
tll_ptr notbclo_i48;
tll_ptr orbclo_i47;
tll_ptr prerrclo_i58;
tll_ptr printclo_i57;
tll_ptr readlineclo_i56;
tll_ptr strlenclo_i55;
tll_ptr testclo_i59;
tll_ptr x_v1720;

tll_ptr andb_i24(tll_ptr b1_v1606, tll_ptr b2_v1607)
{
  tll_ptr false_t2; tll_ptr switch_ret_t1;
  switch(((tll_node)b1_v1606)->tag) {
    case 10:
      switch_ret_t1 = b2_v1607;
      break;
    case 11:
      instr_struct(&false_t2, 11, 0);
      switch_ret_t1 = false_t2;
      break;
  }
  return switch_ret_t1;
}

tll_ptr lam_fun_t4(tll_ptr b2_v1610, tll_env env)
{
  tll_ptr call_ret_t3;
  call_ret_t3 = andb_i24(env[0], b2_v1610);
  return call_ret_t3;
}

tll_ptr lam_fun_t6(tll_ptr b1_v1608, tll_env env)
{
  tll_ptr lam_clo_t5;
  instr_clo(&lam_clo_t5, &lam_fun_t4, 1, b1_v1608);
  return lam_clo_t5;
}

tll_ptr orb_i25(tll_ptr b1_v1611, tll_ptr b2_v1612)
{
  tll_ptr switch_ret_t8; tll_ptr true_t9;
  switch(((tll_node)b1_v1611)->tag) {
    case 10:
      instr_struct(&true_t9, 10, 0);
      switch_ret_t8 = true_t9;
      break;
    case 11:
      switch_ret_t8 = b2_v1612;
      break;
  }
  return switch_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b2_v1615, tll_env env)
{
  tll_ptr call_ret_t10;
  call_ret_t10 = orb_i25(env[0], b2_v1615);
  return call_ret_t10;
}

tll_ptr lam_fun_t13(tll_ptr b1_v1613, tll_env env)
{
  tll_ptr lam_clo_t12;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 1, b1_v1613);
  return lam_clo_t12;
}

tll_ptr notb_i26(tll_ptr b_v1616)
{
  tll_ptr false_t16; tll_ptr switch_ret_t15; tll_ptr true_t17;
  switch(((tll_node)b_v1616)->tag) {
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

tll_ptr lam_fun_t19(tll_ptr b_v1617, tll_env env)
{
  tll_ptr call_ret_t18;
  call_ret_t18 = notb_i26(b_v1617);
  return call_ret_t18;
}

tll_ptr addn_i27(tll_ptr x_v1618, tll_ptr y_v1619)
{
  tll_ptr S_t23; tll_ptr call_ret_t22; tll_ptr switch_ret_t21;
  tll_ptr x_v1620;
  switch(((tll_node)x_v1618)->tag) {
    case 12:
      switch_ret_t21 = y_v1619;
      break;
    case 13:
      x_v1620 = ((tll_node)x_v1618)->data[0];
      call_ret_t22 = addn_i27(x_v1620, y_v1619);
      instr_struct(&S_t23, 13, 1, call_ret_t22);
      switch_ret_t21 = S_t23;
      break;
  }
  return switch_ret_t21;
}

tll_ptr lam_fun_t25(tll_ptr y_v1623, tll_env env)
{
  tll_ptr call_ret_t24;
  call_ret_t24 = addn_i27(env[0], y_v1623);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr x_v1621, tll_env env)
{
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, x_v1621);
  return lam_clo_t26;
}

tll_ptr muln_i28(tll_ptr x_v1624, tll_ptr y_v1625)
{
  tll_ptr call_ret_t30; tll_ptr call_ret_t31; tll_ptr switch_ret_t29;
  tll_ptr x_v1626;
  switch(((tll_node)x_v1624)->tag) {
    case 12:
      switch_ret_t29 = y_v1625;
      break;
    case 13:
      x_v1626 = ((tll_node)x_v1624)->data[0];
      call_ret_t31 = muln_i28(x_v1626, y_v1625);
      call_ret_t30 = addn_i27(y_v1625, call_ret_t31);
      switch_ret_t29 = call_ret_t30;
      break;
  }
  return switch_ret_t29;
}

tll_ptr lam_fun_t33(tll_ptr y_v1629, tll_env env)
{
  tll_ptr call_ret_t32;
  call_ret_t32 = muln_i28(env[0], y_v1629);
  return call_ret_t32;
}

tll_ptr lam_fun_t35(tll_ptr x_v1627, tll_env env)
{
  tll_ptr lam_clo_t34;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 1, x_v1627);
  return lam_clo_t34;
}

tll_ptr eqn_i29(tll_ptr x_v1630, tll_ptr y_v1631)
{
  tll_ptr __v1632; tll_ptr call_ret_t43; tll_ptr false_t40;
  tll_ptr false_t42; tll_ptr switch_ret_t37; tll_ptr switch_ret_t38;
  tll_ptr switch_ret_t41; tll_ptr true_t39; tll_ptr x_v1633; tll_ptr y_v1634;
  switch(((tll_node)x_v1630)->tag) {
    case 12:
      switch(((tll_node)y_v1631)->tag) {
        case 12:
          instr_struct(&true_t39, 10, 0);
          switch_ret_t38 = true_t39;
          break;
        case 13:
          __v1632 = ((tll_node)y_v1631)->data[0];
          instr_struct(&false_t40, 11, 0);
          switch_ret_t38 = false_t40;
          break;
      }
      switch_ret_t37 = switch_ret_t38;
      break;
    case 13:
      x_v1633 = ((tll_node)x_v1630)->data[0];
      switch(((tll_node)y_v1631)->tag) {
        case 12:
          instr_struct(&false_t42, 11, 0);
          switch_ret_t41 = false_t42;
          break;
        case 13:
          y_v1634 = ((tll_node)y_v1631)->data[0];
          call_ret_t43 = eqn_i29(x_v1633, y_v1634);
          switch_ret_t41 = call_ret_t43;
          break;
      }
      switch_ret_t37 = switch_ret_t41;
      break;
  }
  return switch_ret_t37;
}

tll_ptr lam_fun_t45(tll_ptr y_v1637, tll_env env)
{
  tll_ptr call_ret_t44;
  call_ret_t44 = eqn_i29(env[0], y_v1637);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v1635, tll_env env)
{
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v1635);
  return lam_clo_t46;
}

tll_ptr lten_i30(tll_ptr x_v1638, tll_ptr y_v1639)
{
  tll_ptr call_ret_t53; tll_ptr false_t52; tll_ptr switch_ret_t49;
  tll_ptr switch_ret_t51; tll_ptr true_t50; tll_ptr x_v1640; tll_ptr y_v1641;
  switch(((tll_node)x_v1638)->tag) {
    case 12:
      instr_struct(&true_t50, 10, 0);
      switch_ret_t49 = true_t50;
      break;
    case 13:
      x_v1640 = ((tll_node)x_v1638)->data[0];
      switch(((tll_node)y_v1639)->tag) {
        case 12:
          instr_struct(&false_t52, 11, 0);
          switch_ret_t51 = false_t52;
          break;
        case 13:
          y_v1641 = ((tll_node)y_v1639)->data[0];
          call_ret_t53 = lten_i30(x_v1640, y_v1641);
          switch_ret_t51 = call_ret_t53;
          break;
      }
      switch_ret_t49 = switch_ret_t51;
      break;
  }
  return switch_ret_t49;
}

tll_ptr lam_fun_t55(tll_ptr y_v1644, tll_env env)
{
  tll_ptr call_ret_t54;
  call_ret_t54 = lten_i30(env[0], y_v1644);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v1642, tll_env env)
{
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v1642);
  return lam_clo_t56;
}

tll_ptr gten_i31(tll_ptr x_v1645, tll_ptr y_v1646)
{
  tll_ptr __v1647; tll_ptr call_ret_t65; tll_ptr false_t62;
  tll_ptr switch_ret_t59; tll_ptr switch_ret_t60; tll_ptr switch_ret_t63;
  tll_ptr true_t61; tll_ptr true_t64; tll_ptr x_v1648; tll_ptr y_v1649;
  switch(((tll_node)x_v1645)->tag) {
    case 12:
      switch(((tll_node)y_v1646)->tag) {
        case 12:
          instr_struct(&true_t61, 10, 0);
          switch_ret_t60 = true_t61;
          break;
        case 13:
          __v1647 = ((tll_node)y_v1646)->data[0];
          instr_struct(&false_t62, 11, 0);
          switch_ret_t60 = false_t62;
          break;
      }
      switch_ret_t59 = switch_ret_t60;
      break;
    case 13:
      x_v1648 = ((tll_node)x_v1645)->data[0];
      switch(((tll_node)y_v1646)->tag) {
        case 12:
          instr_struct(&true_t64, 10, 0);
          switch_ret_t63 = true_t64;
          break;
        case 13:
          y_v1649 = ((tll_node)y_v1646)->data[0];
          call_ret_t65 = gten_i31(x_v1648, y_v1649);
          switch_ret_t63 = call_ret_t65;
          break;
      }
      switch_ret_t59 = switch_ret_t63;
      break;
  }
  return switch_ret_t59;
}

tll_ptr lam_fun_t67(tll_ptr y_v1652, tll_env env)
{
  tll_ptr call_ret_t66;
  call_ret_t66 = gten_i31(env[0], y_v1652);
  return call_ret_t66;
}

tll_ptr lam_fun_t69(tll_ptr x_v1650, tll_env env)
{
  tll_ptr lam_clo_t68;
  instr_clo(&lam_clo_t68, &lam_fun_t67, 1, x_v1650);
  return lam_clo_t68;
}

tll_ptr cats_i34(tll_ptr s1_v1653, tll_ptr s2_v1654)
{
  tll_ptr String_t73; tll_ptr c_v1655; tll_ptr call_ret_t72;
  tll_ptr s1_v1656; tll_ptr switch_ret_t71;
  switch(((tll_node)s1_v1653)->tag) {
    case 15:
      switch_ret_t71 = s2_v1654;
      break;
    case 16:
      c_v1655 = ((tll_node)s1_v1653)->data[0];
      s1_v1656 = ((tll_node)s1_v1653)->data[1];
      call_ret_t72 = cats_i34(s1_v1656, s2_v1654);
      instr_struct(&String_t73, 16, 2, c_v1655, call_ret_t72);
      switch_ret_t71 = String_t73;
      break;
  }
  return switch_ret_t71;
}

tll_ptr lam_fun_t75(tll_ptr s2_v1659, tll_env env)
{
  tll_ptr call_ret_t74;
  call_ret_t74 = cats_i34(env[0], s2_v1659);
  return call_ret_t74;
}

tll_ptr lam_fun_t77(tll_ptr s1_v1657, tll_env env)
{
  tll_ptr lam_clo_t76;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 1, s1_v1657);
  return lam_clo_t76;
}

tll_ptr strlen_i35(tll_ptr s_v1660)
{
  tll_ptr O_t80; tll_ptr S_t82; tll_ptr __v1661; tll_ptr call_ret_t81;
  tll_ptr s_v1662; tll_ptr switch_ret_t79;
  switch(((tll_node)s_v1660)->tag) {
    case 15:
      instr_struct(&O_t80, 12, 0);
      switch_ret_t79 = O_t80;
      break;
    case 16:
      __v1661 = ((tll_node)s_v1660)->data[0];
      s_v1662 = ((tll_node)s_v1660)->data[1];
      call_ret_t81 = strlen_i35(s_v1662);
      instr_struct(&S_t82, 13, 1, call_ret_t81);
      switch_ret_t79 = S_t82;
      break;
  }
  return switch_ret_t79;
}

tll_ptr lam_fun_t84(tll_ptr s_v1663, tll_env env)
{
  tll_ptr call_ret_t83;
  call_ret_t83 = strlen_i35(s_v1663);
  return call_ret_t83;
}

tll_ptr lam_fun_t94(tll_ptr __v1680, tll_env env)
{
  tll_ptr __v1685; tll_ptr ch_v1684; tll_ptr false_t92; tll_ptr send_ch_t91;
  tll_ptr tt_t93; tll_ptr x_v1686;
  instr_struct(&false_t92, 11, 0);
  instr_send(&send_ch_t91, env[0], false_t92);
  ch_v1684 = send_ch_t91;
  x_v1686 = ch_v1684;
  instr_struct(&tt_t93, 9, 0);
  __v1685 = tt_t93;
  return env[1];
}

tll_ptr lam_fun_t97(tll_ptr __v1665, tll_env env)
{
  tll_ptr __v1677; tll_ptr app_ret_t96; tll_ptr ch_v1675; tll_ptr ch_v1676;
  tll_ptr ch_v1679; tll_ptr lam_clo_t95; tll_ptr prim_ch_t86;
  tll_ptr recv_msg_t89; tll_ptr s_v1678; tll_ptr send_ch_t87;
  tll_ptr switch_ret_t90; tll_ptr true_t88;
  instr_open(&prim_ch_t86, &proc_stdin);
  ch_v1675 = prim_ch_t86;
  instr_struct(&true_t88, 10, 0);
  instr_send(&send_ch_t87, ch_v1675, true_t88);
  ch_v1676 = send_ch_t87;
  instr_recv(&recv_msg_t89, ch_v1676);
  __v1677 = recv_msg_t89;
  switch(((tll_node)__v1677)->tag) {
    case 0:
      s_v1678 = ((tll_node)__v1677)->data[0];
      ch_v1679 = ((tll_node)__v1677)->data[1];
      instr_free_struct(__v1677);
      instr_clo(&lam_clo_t95, &lam_fun_t94, 2, ch_v1679, s_v1678);
      switch_ret_t90 = lam_clo_t95;
      break;
  }
  instr_app(&app_ret_t96, switch_ret_t90, 0);
  instr_free_clo(switch_ret_t90);
  return app_ret_t96;
}

tll_ptr readline_i42(tll_ptr __v1664)
{
  tll_ptr lam_clo_t98;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  return lam_clo_t98;
}

tll_ptr lam_fun_t100(tll_ptr __v1687, tll_env env)
{
  tll_ptr call_ret_t99;
  call_ret_t99 = readline_i42(__v1687);
  return call_ret_t99;
}

tll_ptr lam_fun_t109(tll_ptr __v1689, tll_env env)
{
  tll_ptr ch_v1695; tll_ptr ch_v1696; tll_ptr ch_v1697; tll_ptr ch_v1698;
  tll_ptr false_t107; tll_ptr prim_ch_t102; tll_ptr send_ch_t103;
  tll_ptr send_ch_t105; tll_ptr send_ch_t106; tll_ptr true_t104;
  tll_ptr tt_t108; tll_ptr x_v1699;
  instr_open(&prim_ch_t102, &proc_stdout);
  ch_v1695 = prim_ch_t102;
  instr_struct(&true_t104, 10, 0);
  instr_send(&send_ch_t103, ch_v1695, true_t104);
  ch_v1696 = send_ch_t103;
  instr_send(&send_ch_t105, ch_v1696, env[0]);
  ch_v1697 = send_ch_t105;
  instr_struct(&false_t107, 11, 0);
  instr_send(&send_ch_t106, ch_v1697, false_t107);
  ch_v1698 = send_ch_t106;
  x_v1699 = ch_v1698;
  instr_struct(&tt_t108, 9, 0);
  return tt_t108;
}

tll_ptr print_i43(tll_ptr s_v1688)
{
  tll_ptr lam_clo_t110;
  instr_clo(&lam_clo_t110, &lam_fun_t109, 1, s_v1688);
  return lam_clo_t110;
}

tll_ptr lam_fun_t112(tll_ptr s_v1700, tll_env env)
{
  tll_ptr call_ret_t111;
  call_ret_t111 = print_i43(s_v1700);
  return call_ret_t111;
}

tll_ptr lam_fun_t121(tll_ptr __v1702, tll_env env)
{
  tll_ptr ch_v1708; tll_ptr ch_v1709; tll_ptr ch_v1710; tll_ptr ch_v1711;
  tll_ptr false_t119; tll_ptr prim_ch_t114; tll_ptr send_ch_t115;
  tll_ptr send_ch_t117; tll_ptr send_ch_t118; tll_ptr true_t116;
  tll_ptr tt_t120; tll_ptr x_v1712;
  instr_open(&prim_ch_t114, &proc_stderr);
  ch_v1708 = prim_ch_t114;
  instr_struct(&true_t116, 10, 0);
  instr_send(&send_ch_t115, ch_v1708, true_t116);
  ch_v1709 = send_ch_t115;
  instr_send(&send_ch_t117, ch_v1709, env[0]);
  ch_v1710 = send_ch_t117;
  instr_struct(&false_t119, 11, 0);
  instr_send(&send_ch_t118, ch_v1710, false_t119);
  ch_v1711 = send_ch_t118;
  x_v1712 = ch_v1711;
  instr_struct(&tt_t120, 9, 0);
  return tt_t120;
}

tll_ptr prerr_i44(tll_ptr s_v1701)
{
  tll_ptr lam_clo_t122;
  instr_clo(&lam_clo_t122, &lam_fun_t121, 1, s_v1701);
  return lam_clo_t122;
}

tll_ptr lam_fun_t124(tll_ptr s_v1713, tll_env env)
{
  tll_ptr call_ret_t123;
  call_ret_t123 = prerr_i44(s_v1713);
  return call_ret_t123;
}

tll_ptr test_i45(tll_ptr x_v1714, tll_ptr y_v1715)
{
  tll_ptr app_ret_t127; tll_ptr app_ret_t129; tll_ptr test1_v1716;
  tll_ptr tt_t126; tll_ptr tt_t128;
  instr_struct(&tt_t126, 9, 0);
  instr_app(&app_ret_t127, testclo_i59, tt_t126);
  test1_v1716 = app_ret_t127;
  instr_struct(&tt_t128, 9, 0);
  instr_app(&app_ret_t129, test1_v1716, tt_t128);
  return app_ret_t129;
}

tll_ptr lam_fun_t131(tll_ptr y_v1719, tll_env env)
{
  tll_ptr call_ret_t130;
  call_ret_t130 = test_i45(env[0], y_v1719);
  return call_ret_t130;
}

tll_ptr lam_fun_t133(tll_ptr x_v1717, tll_env env)
{
  tll_ptr lam_clo_t132;
  instr_clo(&lam_clo_t132, &lam_fun_t131, 1, x_v1717);
  return lam_clo_t132;
}

tll_ptr lam_fun_t136(tll_ptr __v1721, tll_env env)
{
  tll_ptr tt_t135;
  instr_struct(&tt_t135, 9, 0);
  return tt_t135;
}

tll_ptr lam_fun_t139(tll_ptr __v1722, tll_env env)
{
  tll_ptr app_ret_t138; tll_ptr v_v1724;
  instr_app(&app_ret_t138, env[0], 0);
  instr_free_clo(env[0]);
  v_v1724 = app_ret_t138;
  return v_v1724;
}

int main()
{
  instr_init();
  instr_clo(&lam_clo_t7, &lam_fun_t6, 0);
  andbclo_i46 = lam_clo_t7;
  instr_clo(&lam_clo_t14, &lam_fun_t13, 0);
  orbclo_i47 = lam_clo_t14;
  instr_clo(&lam_clo_t20, &lam_fun_t19, 0);
  notbclo_i48 = lam_clo_t20;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  addnclo_i49 = lam_clo_t28;
  instr_clo(&lam_clo_t36, &lam_fun_t35, 0);
  mulnclo_i50 = lam_clo_t36;
  instr_clo(&lam_clo_t48, &lam_fun_t47, 0);
  eqnclo_i51 = lam_clo_t48;
  instr_clo(&lam_clo_t58, &lam_fun_t57, 0);
  ltenclo_i52 = lam_clo_t58;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 0);
  gtenclo_i53 = lam_clo_t70;
  instr_clo(&lam_clo_t78, &lam_fun_t77, 0);
  catsclo_i54 = lam_clo_t78;
  instr_clo(&lam_clo_t85, &lam_fun_t84, 0);
  strlenclo_i55 = lam_clo_t85;
  instr_clo(&lam_clo_t101, &lam_fun_t100, 0);
  readlineclo_i56 = lam_clo_t101;
  instr_clo(&lam_clo_t113, &lam_fun_t112, 0);
  printclo_i57 = lam_clo_t113;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 0);
  prerrclo_i58 = lam_clo_t125;
  instr_clo(&lam_clo_t134, &lam_fun_t133, 0);
  testclo_i59 = lam_clo_t134;
  instr_clo(&lam_clo_t137, &lam_fun_t136, 0);
  x_v1720 = lam_clo_t137;
  instr_clo(&lam_clo_t140, &lam_fun_t139, 1, x_v1720);
  instr_app(&app_ret_t141, lam_clo_t140, 0);
  instr_free_clo(lam_clo_t140);
  instr_free_struct(app_ret_t141);
  return 0;
}

