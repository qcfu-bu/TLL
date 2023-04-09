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

tll_ptr andb_i23(tll_ptr b1_v1666, tll_ptr b2_v1667)
{
  tll_ptr false_t2; tll_ptr switch_ret_t1;
  switch(((tll_node)b1_v1666)->tag) {
    case 10:
      switch_ret_t1 = b2_v1667;
      break;
    case 11:
      instr_struct(&false_t2, 11, 0);
      switch_ret_t1 = false_t2;
      break;
  }
  return switch_ret_t1;
}

tll_ptr lam_fun_t4(tll_ptr b2_v1670, tll_env env)
{
  tll_ptr call_ret_t3;
  call_ret_t3 = andb_i23(env[0], b2_v1670);
  return call_ret_t3;
}

tll_ptr lam_fun_t6(tll_ptr b1_v1668, tll_env env)
{
  tll_ptr lam_clo_t5;
  instr_clo(&lam_clo_t5, &lam_fun_t4, 1, b1_v1668);
  return lam_clo_t5;
}

tll_ptr orb_i24(tll_ptr b1_v1671, tll_ptr b2_v1672)
{
  tll_ptr switch_ret_t8; tll_ptr true_t9;
  switch(((tll_node)b1_v1671)->tag) {
    case 10:
      instr_struct(&true_t9, 10, 0);
      switch_ret_t8 = true_t9;
      break;
    case 11:
      switch_ret_t8 = b2_v1672;
      break;
  }
  return switch_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b2_v1675, tll_env env)
{
  tll_ptr call_ret_t10;
  call_ret_t10 = orb_i24(env[0], b2_v1675);
  return call_ret_t10;
}

tll_ptr lam_fun_t13(tll_ptr b1_v1673, tll_env env)
{
  tll_ptr lam_clo_t12;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 1, b1_v1673);
  return lam_clo_t12;
}

tll_ptr notb_i25(tll_ptr b_v1676)
{
  tll_ptr false_t16; tll_ptr switch_ret_t15; tll_ptr true_t17;
  switch(((tll_node)b_v1676)->tag) {
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

tll_ptr lam_fun_t19(tll_ptr b_v1677, tll_env env)
{
  tll_ptr call_ret_t18;
  call_ret_t18 = notb_i25(b_v1677);
  return call_ret_t18;
}

tll_ptr addn_i26(tll_ptr x_v1678, tll_ptr y_v1679)
{
  tll_ptr S_t23; tll_ptr call_ret_t22; tll_ptr switch_ret_t21;
  tll_ptr x_v1680;
  switch(((tll_node)x_v1678)->tag) {
    case 12:
      switch_ret_t21 = y_v1679;
      break;
    case 13:
      x_v1680 = ((tll_node)x_v1678)->data[0];
      call_ret_t22 = addn_i26(x_v1680, y_v1679);
      instr_struct(&S_t23, 13, 1, call_ret_t22);
      switch_ret_t21 = S_t23;
      break;
  }
  return switch_ret_t21;
}

tll_ptr lam_fun_t25(tll_ptr y_v1683, tll_env env)
{
  tll_ptr call_ret_t24;
  call_ret_t24 = addn_i26(env[0], y_v1683);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr x_v1681, tll_env env)
{
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, x_v1681);
  return lam_clo_t26;
}

tll_ptr muln_i27(tll_ptr x_v1684, tll_ptr y_v1685)
{
  tll_ptr call_ret_t30; tll_ptr call_ret_t31; tll_ptr switch_ret_t29;
  tll_ptr x_v1686;
  switch(((tll_node)x_v1684)->tag) {
    case 12:
      switch_ret_t29 = y_v1685;
      break;
    case 13:
      x_v1686 = ((tll_node)x_v1684)->data[0];
      call_ret_t31 = muln_i27(x_v1686, y_v1685);
      call_ret_t30 = addn_i26(y_v1685, call_ret_t31);
      switch_ret_t29 = call_ret_t30;
      break;
  }
  return switch_ret_t29;
}

tll_ptr lam_fun_t33(tll_ptr y_v1689, tll_env env)
{
  tll_ptr call_ret_t32;
  call_ret_t32 = muln_i27(env[0], y_v1689);
  return call_ret_t32;
}

tll_ptr lam_fun_t35(tll_ptr x_v1687, tll_env env)
{
  tll_ptr lam_clo_t34;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 1, x_v1687);
  return lam_clo_t34;
}

tll_ptr eqn_i28(tll_ptr x_v1690, tll_ptr y_v1691)
{
  tll_ptr __v1692; tll_ptr call_ret_t43; tll_ptr false_t40;
  tll_ptr false_t42; tll_ptr switch_ret_t37; tll_ptr switch_ret_t38;
  tll_ptr switch_ret_t41; tll_ptr true_t39; tll_ptr x_v1693; tll_ptr y_v1694;
  switch(((tll_node)x_v1690)->tag) {
    case 12:
      switch(((tll_node)y_v1691)->tag) {
        case 12:
          instr_struct(&true_t39, 10, 0);
          switch_ret_t38 = true_t39;
          break;
        case 13:
          __v1692 = ((tll_node)y_v1691)->data[0];
          instr_struct(&false_t40, 11, 0);
          switch_ret_t38 = false_t40;
          break;
      }
      switch_ret_t37 = switch_ret_t38;
      break;
    case 13:
      x_v1693 = ((tll_node)x_v1690)->data[0];
      switch(((tll_node)y_v1691)->tag) {
        case 12:
          instr_struct(&false_t42, 11, 0);
          switch_ret_t41 = false_t42;
          break;
        case 13:
          y_v1694 = ((tll_node)y_v1691)->data[0];
          call_ret_t43 = eqn_i28(x_v1693, y_v1694);
          switch_ret_t41 = call_ret_t43;
          break;
      }
      switch_ret_t37 = switch_ret_t41;
      break;
  }
  return switch_ret_t37;
}

tll_ptr lam_fun_t45(tll_ptr y_v1697, tll_env env)
{
  tll_ptr call_ret_t44;
  call_ret_t44 = eqn_i28(env[0], y_v1697);
  return call_ret_t44;
}

tll_ptr lam_fun_t47(tll_ptr x_v1695, tll_env env)
{
  tll_ptr lam_clo_t46;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 1, x_v1695);
  return lam_clo_t46;
}

tll_ptr lten_i29(tll_ptr x_v1698, tll_ptr y_v1699)
{
  tll_ptr call_ret_t53; tll_ptr false_t52; tll_ptr switch_ret_t49;
  tll_ptr switch_ret_t51; tll_ptr true_t50; tll_ptr x_v1700; tll_ptr y_v1701;
  switch(((tll_node)x_v1698)->tag) {
    case 12:
      instr_struct(&true_t50, 10, 0);
      switch_ret_t49 = true_t50;
      break;
    case 13:
      x_v1700 = ((tll_node)x_v1698)->data[0];
      switch(((tll_node)y_v1699)->tag) {
        case 12:
          instr_struct(&false_t52, 11, 0);
          switch_ret_t51 = false_t52;
          break;
        case 13:
          y_v1701 = ((tll_node)y_v1699)->data[0];
          call_ret_t53 = lten_i29(x_v1700, y_v1701);
          switch_ret_t51 = call_ret_t53;
          break;
      }
      switch_ret_t49 = switch_ret_t51;
      break;
  }
  return switch_ret_t49;
}

tll_ptr lam_fun_t55(tll_ptr y_v1704, tll_env env)
{
  tll_ptr call_ret_t54;
  call_ret_t54 = lten_i29(env[0], y_v1704);
  return call_ret_t54;
}

tll_ptr lam_fun_t57(tll_ptr x_v1702, tll_env env)
{
  tll_ptr lam_clo_t56;
  instr_clo(&lam_clo_t56, &lam_fun_t55, 1, x_v1702);
  return lam_clo_t56;
}

tll_ptr gten_i30(tll_ptr x_v1705, tll_ptr y_v1706)
{
  tll_ptr __v1707; tll_ptr call_ret_t65; tll_ptr false_t62;
  tll_ptr switch_ret_t59; tll_ptr switch_ret_t60; tll_ptr switch_ret_t63;
  tll_ptr true_t61; tll_ptr true_t64; tll_ptr x_v1708; tll_ptr y_v1709;
  switch(((tll_node)x_v1705)->tag) {
    case 12:
      switch(((tll_node)y_v1706)->tag) {
        case 12:
          instr_struct(&true_t61, 10, 0);
          switch_ret_t60 = true_t61;
          break;
        case 13:
          __v1707 = ((tll_node)y_v1706)->data[0];
          instr_struct(&false_t62, 11, 0);
          switch_ret_t60 = false_t62;
          break;
      }
      switch_ret_t59 = switch_ret_t60;
      break;
    case 13:
      x_v1708 = ((tll_node)x_v1705)->data[0];
      switch(((tll_node)y_v1706)->tag) {
        case 12:
          instr_struct(&true_t64, 10, 0);
          switch_ret_t63 = true_t64;
          break;
        case 13:
          y_v1709 = ((tll_node)y_v1706)->data[0];
          call_ret_t65 = gten_i30(x_v1708, y_v1709);
          switch_ret_t63 = call_ret_t65;
          break;
      }
      switch_ret_t59 = switch_ret_t63;
      break;
  }
  return switch_ret_t59;
}

tll_ptr lam_fun_t67(tll_ptr y_v1712, tll_env env)
{
  tll_ptr call_ret_t66;
  call_ret_t66 = gten_i30(env[0], y_v1712);
  return call_ret_t66;
}

tll_ptr lam_fun_t69(tll_ptr x_v1710, tll_env env)
{
  tll_ptr lam_clo_t68;
  instr_clo(&lam_clo_t68, &lam_fun_t67, 1, x_v1710);
  return lam_clo_t68;
}

tll_ptr cats_i33(tll_ptr s1_v1713, tll_ptr s2_v1714)
{
  tll_ptr String_t73; tll_ptr c_v1715; tll_ptr call_ret_t72;
  tll_ptr s1_v1716; tll_ptr switch_ret_t71;
  switch(((tll_node)s1_v1713)->tag) {
    case 15:
      switch_ret_t71 = s2_v1714;
      break;
    case 16:
      c_v1715 = ((tll_node)s1_v1713)->data[0];
      s1_v1716 = ((tll_node)s1_v1713)->data[1];
      call_ret_t72 = cats_i33(s1_v1716, s2_v1714);
      instr_struct(&String_t73, 16, 2, c_v1715, call_ret_t72);
      switch_ret_t71 = String_t73;
      break;
  }
  return switch_ret_t71;
}

tll_ptr lam_fun_t75(tll_ptr s2_v1719, tll_env env)
{
  tll_ptr call_ret_t74;
  call_ret_t74 = cats_i33(env[0], s2_v1719);
  return call_ret_t74;
}

tll_ptr lam_fun_t77(tll_ptr s1_v1717, tll_env env)
{
  tll_ptr lam_clo_t76;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 1, s1_v1717);
  return lam_clo_t76;
}

tll_ptr strlen_i34(tll_ptr s_v1720)
{
  tll_ptr O_t80; tll_ptr S_t82; tll_ptr __v1721; tll_ptr call_ret_t81;
  tll_ptr s_v1722; tll_ptr switch_ret_t79;
  switch(((tll_node)s_v1720)->tag) {
    case 15:
      instr_struct(&O_t80, 12, 0);
      switch_ret_t79 = O_t80;
      break;
    case 16:
      __v1721 = ((tll_node)s_v1720)->data[0];
      s_v1722 = ((tll_node)s_v1720)->data[1];
      call_ret_t81 = strlen_i34(s_v1722);
      instr_struct(&S_t82, 13, 1, call_ret_t81);
      switch_ret_t79 = S_t82;
      break;
  }
  return switch_ret_t79;
}

tll_ptr lam_fun_t84(tll_ptr s_v1723, tll_env env)
{
  tll_ptr call_ret_t83;
  call_ret_t83 = strlen_i34(s_v1723);
  return call_ret_t83;
}

tll_ptr lam_fun_t94(tll_ptr __v1740, tll_env env)
{
  tll_ptr __v1745; tll_ptr __v1746; tll_ptr ch_v1744; tll_ptr false_t92;
  tll_ptr send_ch_t91; tll_ptr tt_t93;
  instr_struct(&false_t92, 11, 0);
  instr_send(&send_ch_t91, env[0], false_t92);
  ch_v1744 = send_ch_t91;
  __v1746 = ch_v1744;
  instr_struct(&tt_t93, 9, 0);
  __v1745 = tt_t93;
  return env[1];
}

tll_ptr lam_fun_t97(tll_ptr __v1725, tll_env env)
{
  tll_ptr __v1737; tll_ptr app_ret_t96; tll_ptr ch_v1735; tll_ptr ch_v1736;
  tll_ptr ch_v1739; tll_ptr lam_clo_t95; tll_ptr prim_ch_t86;
  tll_ptr recv_msg_t89; tll_ptr s_v1738; tll_ptr send_ch_t87;
  tll_ptr switch_ret_t90; tll_ptr true_t88;
  instr_open(&prim_ch_t86, &proc_stdin);
  ch_v1735 = prim_ch_t86;
  instr_struct(&true_t88, 10, 0);
  instr_send(&send_ch_t87, ch_v1735, true_t88);
  ch_v1736 = send_ch_t87;
  instr_recv(&recv_msg_t89, ch_v1736);
  __v1737 = recv_msg_t89;
  switch(((tll_node)__v1737)->tag) {
    case 0:
      s_v1738 = ((tll_node)__v1737)->data[0];
      ch_v1739 = ((tll_node)__v1737)->data[1];
      instr_free_struct(__v1737);
      instr_clo(&lam_clo_t95, &lam_fun_t94, 2, ch_v1739, s_v1738);
      switch_ret_t90 = lam_clo_t95;
      break;
  }
  instr_app(&app_ret_t96, switch_ret_t90, 0);
  instr_free_clo(switch_ret_t90);
  return app_ret_t96;
}

tll_ptr readline_i41(tll_ptr __v1724)
{
  tll_ptr lam_clo_t98;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  return lam_clo_t98;
}

tll_ptr lam_fun_t100(tll_ptr __v1747, tll_env env)
{
  tll_ptr call_ret_t99;
  call_ret_t99 = readline_i41(__v1747);
  return call_ret_t99;
}

tll_ptr lam_fun_t109(tll_ptr __v1749, tll_env env)
{
  tll_ptr __v1759; tll_ptr ch_v1755; tll_ptr ch_v1756; tll_ptr ch_v1757;
  tll_ptr ch_v1758; tll_ptr false_t107; tll_ptr prim_ch_t102;
  tll_ptr send_ch_t103; tll_ptr send_ch_t105; tll_ptr send_ch_t106;
  tll_ptr true_t104; tll_ptr tt_t108;
  instr_open(&prim_ch_t102, &proc_stdout);
  ch_v1755 = prim_ch_t102;
  instr_struct(&true_t104, 10, 0);
  instr_send(&send_ch_t103, ch_v1755, true_t104);
  ch_v1756 = send_ch_t103;
  instr_send(&send_ch_t105, ch_v1756, env[0]);
  ch_v1757 = send_ch_t105;
  instr_struct(&false_t107, 11, 0);
  instr_send(&send_ch_t106, ch_v1757, false_t107);
  ch_v1758 = send_ch_t106;
  __v1759 = ch_v1758;
  instr_struct(&tt_t108, 9, 0);
  return tt_t108;
}

tll_ptr print_i42(tll_ptr s_v1748)
{
  tll_ptr lam_clo_t110;
  instr_clo(&lam_clo_t110, &lam_fun_t109, 1, s_v1748);
  return lam_clo_t110;
}

tll_ptr lam_fun_t112(tll_ptr s_v1760, tll_env env)
{
  tll_ptr call_ret_t111;
  call_ret_t111 = print_i42(s_v1760);
  return call_ret_t111;
}

tll_ptr lam_fun_t121(tll_ptr __v1762, tll_env env)
{
  tll_ptr __v1772; tll_ptr ch_v1768; tll_ptr ch_v1769; tll_ptr ch_v1770;
  tll_ptr ch_v1771; tll_ptr false_t119; tll_ptr prim_ch_t114;
  tll_ptr send_ch_t115; tll_ptr send_ch_t117; tll_ptr send_ch_t118;
  tll_ptr true_t116; tll_ptr tt_t120;
  instr_open(&prim_ch_t114, &proc_stderr);
  ch_v1768 = prim_ch_t114;
  instr_struct(&true_t116, 10, 0);
  instr_send(&send_ch_t115, ch_v1768, true_t116);
  ch_v1769 = send_ch_t115;
  instr_send(&send_ch_t117, ch_v1769, env[0]);
  ch_v1770 = send_ch_t117;
  instr_struct(&false_t119, 11, 0);
  instr_send(&send_ch_t118, ch_v1770, false_t119);
  ch_v1771 = send_ch_t118;
  __v1772 = ch_v1771;
  instr_struct(&tt_t120, 9, 0);
  return tt_t120;
}

tll_ptr prerr_i43(tll_ptr s_v1761)
{
  tll_ptr lam_clo_t122;
  instr_clo(&lam_clo_t122, &lam_fun_t121, 1, s_v1761);
  return lam_clo_t122;
}

tll_ptr lam_fun_t124(tll_ptr s_v1773, tll_env env)
{
  tll_ptr call_ret_t123;
  call_ret_t123 = prerr_i43(s_v1773);
  return call_ret_t123;
}

tll_ptr fork_fun_t131(tll_env env)
{
  tll_ptr __v1781; tll_ptr app_ret_t128; tll_ptr c_v1780;
  tll_ptr call_ret_t126; tll_ptr fork_ret_t133; tll_ptr s_v1779;
  tll_ptr send_ch_t129; tll_ptr tt_t127; tll_ptr tt_t130;
  instr_struct(&tt_t127, 9, 0);
  call_ret_t126 = readline_i41(tt_t127);
  instr_app(&app_ret_t128, call_ret_t126, 0);
  instr_free_clo(call_ret_t126);
  s_v1779 = app_ret_t128;
  instr_send(&send_ch_t129, env[0], s_v1779);
  c_v1780 = send_ch_t129;
  __v1781 = c_v1780;
  instr_struct(&tt_t130, 9, 0);
  fork_ret_t133 = tt_t130;
  instr_free_thread(env);
  return fork_ret_t133;
}

tll_ptr lam_fun_t139(tll_ptr __v1785, tll_env env)
{
  tll_ptr __v1787; tll_ptr app_ret_t138; tll_ptr call_ret_t137;
  tll_ptr close_tmp_t136;
  instr_close(&close_tmp_t136, env[0]);
  __v1787 = close_tmp_t136;
  call_ret_t137 = print_i42(env[1]);
  instr_app(&app_ret_t138, call_ret_t137, 0);
  instr_free_clo(call_ret_t137);
  return app_ret_t138;
}

int main()
{
  instr_init();
  tll_ptr __v1782; tll_ptr app_ret_t141; tll_ptr c_v1774; tll_ptr c_v1784;
  tll_ptr fork_ch_t132; tll_ptr lam_clo_t101; tll_ptr lam_clo_t113;
  tll_ptr lam_clo_t125; tll_ptr lam_clo_t14; tll_ptr lam_clo_t140;
  tll_ptr lam_clo_t20; tll_ptr lam_clo_t28; tll_ptr lam_clo_t36;
  tll_ptr lam_clo_t48; tll_ptr lam_clo_t58; tll_ptr lam_clo_t7;
  tll_ptr lam_clo_t70; tll_ptr lam_clo_t78; tll_ptr lam_clo_t85;
  tll_ptr msg_v1783; tll_ptr recv_msg_t134; tll_ptr switch_ret_t135;
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
  instr_fork(&fork_ch_t132, &fork_fun_t131, 0);
  c_v1774 = fork_ch_t132;
  instr_recv(&recv_msg_t134, c_v1774);
  __v1782 = recv_msg_t134;
  switch(((tll_node)__v1782)->tag) {
    case 0:
      msg_v1783 = ((tll_node)__v1782)->data[0];
      c_v1784 = ((tll_node)__v1782)->data[1];
      instr_free_struct(__v1782);
      instr_clo(&lam_clo_t140, &lam_fun_t139, 2, c_v1784, msg_v1783);
      switch_ret_t135 = lam_clo_t140;
      break;
  }
  instr_app(&app_ret_t141, switch_ret_t135, 0);
  instr_free_clo(switch_ret_t135);
  instr_free_struct(app_ret_t141);
  return 0;
}

