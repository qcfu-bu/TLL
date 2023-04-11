#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v140582, tll_ptr b2_v140583);
tll_ptr orb_i2(tll_ptr b1_v140587, tll_ptr b2_v140588);
tll_ptr notb_i3(tll_ptr b_v140592);
tll_ptr lten_i4(tll_ptr x_v140594, tll_ptr y_v140595);
tll_ptr gten_i5(tll_ptr x_v140601, tll_ptr y_v140602);
tll_ptr ltn_i6(tll_ptr x_v140609, tll_ptr y_v140610);
tll_ptr gtn_i7(tll_ptr x_v140617, tll_ptr y_v140618);
tll_ptr eqn_i8(tll_ptr x_v140624, tll_ptr y_v140625);
tll_ptr pred_i9(tll_ptr x_v140632);
tll_ptr addn_i10(tll_ptr x_v140635, tll_ptr y_v140636);
tll_ptr subn_i11(tll_ptr x_v140641, tll_ptr y_v140642);
tll_ptr muln_i12(tll_ptr x_v140647, tll_ptr y_v140648);
tll_ptr divn_i13(tll_ptr x_v140653, tll_ptr y_v140654);
tll_ptr modn_i14(tll_ptr x_v140658, tll_ptr y_v140659);
tll_ptr cats_i15(tll_ptr s1_v140663, tll_ptr s2_v140664);
tll_ptr strlen_i16(tll_ptr s_v140670);
tll_ptr lenUU_i43(tll_ptr A_v140674, tll_ptr xs_v140675);
tll_ptr lenUL_i42(tll_ptr A_v140683, tll_ptr xs_v140684);
tll_ptr lenLL_i40(tll_ptr A_v140692, tll_ptr xs_v140693);
tll_ptr appendUU_i47(tll_ptr A_v140701, tll_ptr xs_v140702, tll_ptr ys_v140703);
tll_ptr appendUL_i46(tll_ptr A_v140712, tll_ptr xs_v140713, tll_ptr ys_v140714);
tll_ptr appendLL_i44(tll_ptr A_v140723, tll_ptr xs_v140724, tll_ptr ys_v140725);
tll_ptr readline_i25(tll_ptr __v140734);
tll_ptr print_i26(tll_ptr s_v140753);
tll_ptr prerr_i27(tll_ptr s_v140766);
tll_ptr splitU_i49(tll_ptr zs_v140779);
tll_ptr splitL_i48(tll_ptr zs_v140788);
tll_ptr mergeU_i51(tll_ptr xs_v140797, tll_ptr ys_v140798);
tll_ptr mergeL_i50(tll_ptr xs_v140806, tll_ptr ys_v140807);
tll_ptr msortU_i53(tll_ptr zs_v140815);
tll_ptr msortL_i52(tll_ptr zs_v140824);
tll_ptr cmsort_workerU_i57(tll_ptr zs_v140833, tll_ptr c_v140834);
tll_ptr cmsort_workerL_i56(tll_ptr zs_v140893, tll_ptr c_v140894);
tll_ptr cmsortU_i59(tll_ptr zs_v140953);
tll_ptr cmsortL_i58(tll_ptr zs_v140968);
tll_ptr get_at_i35(tll_ptr A_v140983, tll_ptr n_v140984, tll_ptr xs_v140985, tll_ptr a_v140986);
tll_ptr string_of_digit_i36(tll_ptr n_v141002);
tll_ptr string_of_nat_i37(tll_ptr n_v141004);
tll_ptr string_of_listU_i61(tll_ptr xs_v141008);
tll_ptr string_of_listL_i60(tll_ptr xs_v141012);

tll_ptr addnclo_i71;
tll_ptr andbclo_i62;
tll_ptr appendLLclo_i83;
tll_ptr appendULclo_i82;
tll_ptr appendUUclo_i81;
tll_ptr catsclo_i76;
tll_ptr cmsortLclo_i96;
tll_ptr cmsortUclo_i95;
tll_ptr cmsort_workerLclo_i94;
tll_ptr cmsort_workerUclo_i93;
tll_ptr digits_i34;
tll_ptr divnclo_i74;
tll_ptr eqnclo_i69;
tll_ptr get_atclo_i97;
tll_ptr gtenclo_i66;
tll_ptr gtnclo_i68;
tll_ptr lenLLclo_i80;
tll_ptr lenULclo_i79;
tll_ptr lenUUclo_i78;
tll_ptr ltenclo_i65;
tll_ptr ltnclo_i67;
tll_ptr mergeLclo_i90;
tll_ptr mergeUclo_i89;
tll_ptr modnclo_i75;
tll_ptr msortLclo_i92;
tll_ptr msortUclo_i91;
tll_ptr mulnclo_i73;
tll_ptr notbclo_i64;
tll_ptr orbclo_i63;
tll_ptr predclo_i70;
tll_ptr prerrclo_i86;
tll_ptr printclo_i85;
tll_ptr readlineclo_i84;
tll_ptr splitLclo_i88;
tll_ptr splitUclo_i87;
tll_ptr string_of_digitclo_i98;
tll_ptr string_of_listLclo_i101;
tll_ptr string_of_listUclo_i100;
tll_ptr string_of_natclo_i99;
tll_ptr strlenclo_i77;
tll_ptr subnclo_i72;

tll_ptr andb_i1(tll_ptr b1_v140582, tll_ptr b2_v140583) {
  tll_ptr false_t2; tll_ptr switch_ret_t1;
  switch(((tll_node)b1_v140582)->tag) {
    case 2:
      switch_ret_t1 = b2_v140583;
      break;
    case 3:
      instr_struct(&false_t2, 3, 0);
      switch_ret_t1 = false_t2;
      break;
  }
  return switch_ret_t1;
}

tll_ptr lam_fun_t4(tll_ptr b2_v140586, tll_env env) {
  tll_ptr call_ret_t3;
  call_ret_t3 = andb_i1(env[0], b2_v140586);
  return call_ret_t3;
}

tll_ptr lam_fun_t6(tll_ptr b1_v140584, tll_env env) {
  tll_ptr lam_clo_t5;
  instr_clo(&lam_clo_t5, &lam_fun_t4, 1, b1_v140584);
  return lam_clo_t5;
}

tll_ptr orb_i2(tll_ptr b1_v140587, tll_ptr b2_v140588) {
  tll_ptr switch_ret_t8; tll_ptr true_t9;
  switch(((tll_node)b1_v140587)->tag) {
    case 2:
      instr_struct(&true_t9, 2, 0);
      switch_ret_t8 = true_t9;
      break;
    case 3:
      switch_ret_t8 = b2_v140588;
      break;
  }
  return switch_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b2_v140591, tll_env env) {
  tll_ptr call_ret_t10;
  call_ret_t10 = orb_i2(env[0], b2_v140591);
  return call_ret_t10;
}

tll_ptr lam_fun_t13(tll_ptr b1_v140589, tll_env env) {
  tll_ptr lam_clo_t12;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 1, b1_v140589);
  return lam_clo_t12;
}

tll_ptr notb_i3(tll_ptr b_v140592) {
  tll_ptr false_t16; tll_ptr switch_ret_t15; tll_ptr true_t17;
  switch(((tll_node)b_v140592)->tag) {
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

tll_ptr lam_fun_t19(tll_ptr b_v140593, tll_env env) {
  tll_ptr call_ret_t18;
  call_ret_t18 = notb_i3(b_v140593);
  return call_ret_t18;
}

tll_ptr lten_i4(tll_ptr x_v140594, tll_ptr y_v140595) {
  tll_ptr call_ret_t25; tll_ptr false_t24; tll_ptr switch_ret_t21;
  tll_ptr switch_ret_t23; tll_ptr true_t22; tll_ptr x_v140596;
  tll_ptr y_v140597;
  switch(((tll_node)x_v140594)->tag) {
    case 4:
      instr_struct(&true_t22, 2, 0);
      switch_ret_t21 = true_t22;
      break;
    case 5:
      x_v140596 = ((tll_node)x_v140594)->data[0];
      switch(((tll_node)y_v140595)->tag) {
        case 4:
          instr_struct(&false_t24, 3, 0);
          switch_ret_t23 = false_t24;
          break;
        case 5:
          y_v140597 = ((tll_node)y_v140595)->data[0];
          call_ret_t25 = lten_i4(x_v140596, y_v140597);
          switch_ret_t23 = call_ret_t25;
          break;
      }
      switch_ret_t21 = switch_ret_t23;
      break;
  }
  return switch_ret_t21;
}

tll_ptr lam_fun_t27(tll_ptr y_v140600, tll_env env) {
  tll_ptr call_ret_t26;
  call_ret_t26 = lten_i4(env[0], y_v140600);
  return call_ret_t26;
}

tll_ptr lam_fun_t29(tll_ptr x_v140598, tll_env env) {
  tll_ptr lam_clo_t28;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 1, x_v140598);
  return lam_clo_t28;
}

tll_ptr gten_i5(tll_ptr x_v140601, tll_ptr y_v140602) {
  tll_ptr __v140603; tll_ptr call_ret_t37; tll_ptr false_t34;
  tll_ptr switch_ret_t31; tll_ptr switch_ret_t32; tll_ptr switch_ret_t35;
  tll_ptr true_t33; tll_ptr true_t36; tll_ptr x_v140604; tll_ptr y_v140605;
  switch(((tll_node)x_v140601)->tag) {
    case 4:
      switch(((tll_node)y_v140602)->tag) {
        case 4:
          instr_struct(&true_t33, 2, 0);
          switch_ret_t32 = true_t33;
          break;
        case 5:
          __v140603 = ((tll_node)y_v140602)->data[0];
          instr_struct(&false_t34, 3, 0);
          switch_ret_t32 = false_t34;
          break;
      }
      switch_ret_t31 = switch_ret_t32;
      break;
    case 5:
      x_v140604 = ((tll_node)x_v140601)->data[0];
      switch(((tll_node)y_v140602)->tag) {
        case 4:
          instr_struct(&true_t36, 2, 0);
          switch_ret_t35 = true_t36;
          break;
        case 5:
          y_v140605 = ((tll_node)y_v140602)->data[0];
          call_ret_t37 = gten_i5(x_v140604, y_v140605);
          switch_ret_t35 = call_ret_t37;
          break;
      }
      switch_ret_t31 = switch_ret_t35;
      break;
  }
  return switch_ret_t31;
}

tll_ptr lam_fun_t39(tll_ptr y_v140608, tll_env env) {
  tll_ptr call_ret_t38;
  call_ret_t38 = gten_i5(env[0], y_v140608);
  return call_ret_t38;
}

tll_ptr lam_fun_t41(tll_ptr x_v140606, tll_env env) {
  tll_ptr lam_clo_t40;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 1, x_v140606);
  return lam_clo_t40;
}

tll_ptr ltn_i6(tll_ptr x_v140609, tll_ptr y_v140610) {
  tll_ptr call_ret_t49; tll_ptr false_t45; tll_ptr false_t48;
  tll_ptr switch_ret_t43; tll_ptr switch_ret_t44; tll_ptr switch_ret_t47;
  tll_ptr true_t46; tll_ptr x_v140612; tll_ptr y_v140611; tll_ptr y_v140613;
  switch(((tll_node)x_v140609)->tag) {
    case 4:
      switch(((tll_node)y_v140610)->tag) {
        case 4:
          instr_struct(&false_t45, 3, 0);
          switch_ret_t44 = false_t45;
          break;
        case 5:
          y_v140611 = ((tll_node)y_v140610)->data[0];
          instr_struct(&true_t46, 2, 0);
          switch_ret_t44 = true_t46;
          break;
      }
      switch_ret_t43 = switch_ret_t44;
      break;
    case 5:
      x_v140612 = ((tll_node)x_v140609)->data[0];
      switch(((tll_node)y_v140610)->tag) {
        case 4:
          instr_struct(&false_t48, 3, 0);
          switch_ret_t47 = false_t48;
          break;
        case 5:
          y_v140613 = ((tll_node)y_v140610)->data[0];
          call_ret_t49 = ltn_i6(x_v140612, y_v140613);
          switch_ret_t47 = call_ret_t49;
          break;
      }
      switch_ret_t43 = switch_ret_t47;
      break;
  }
  return switch_ret_t43;
}

tll_ptr lam_fun_t51(tll_ptr y_v140616, tll_env env) {
  tll_ptr call_ret_t50;
  call_ret_t50 = ltn_i6(env[0], y_v140616);
  return call_ret_t50;
}

tll_ptr lam_fun_t53(tll_ptr x_v140614, tll_env env) {
  tll_ptr lam_clo_t52;
  instr_clo(&lam_clo_t52, &lam_fun_t51, 1, x_v140614);
  return lam_clo_t52;
}

tll_ptr gtn_i7(tll_ptr x_v140617, tll_ptr y_v140618) {
  tll_ptr call_ret_t59; tll_ptr false_t56; tll_ptr switch_ret_t55;
  tll_ptr switch_ret_t57; tll_ptr true_t58; tll_ptr x_v140619;
  tll_ptr y_v140620;
  switch(((tll_node)x_v140617)->tag) {
    case 4:
      instr_struct(&false_t56, 3, 0);
      switch_ret_t55 = false_t56;
      break;
    case 5:
      x_v140619 = ((tll_node)x_v140617)->data[0];
      switch(((tll_node)y_v140618)->tag) {
        case 4:
          instr_struct(&true_t58, 2, 0);
          switch_ret_t57 = true_t58;
          break;
        case 5:
          y_v140620 = ((tll_node)y_v140618)->data[0];
          call_ret_t59 = gtn_i7(x_v140619, y_v140620);
          switch_ret_t57 = call_ret_t59;
          break;
      }
      switch_ret_t55 = switch_ret_t57;
      break;
  }
  return switch_ret_t55;
}

tll_ptr lam_fun_t61(tll_ptr y_v140623, tll_env env) {
  tll_ptr call_ret_t60;
  call_ret_t60 = gtn_i7(env[0], y_v140623);
  return call_ret_t60;
}

tll_ptr lam_fun_t63(tll_ptr x_v140621, tll_env env) {
  tll_ptr lam_clo_t62;
  instr_clo(&lam_clo_t62, &lam_fun_t61, 1, x_v140621);
  return lam_clo_t62;
}

tll_ptr eqn_i8(tll_ptr x_v140624, tll_ptr y_v140625) {
  tll_ptr __v140626; tll_ptr call_ret_t71; tll_ptr false_t68;
  tll_ptr false_t70; tll_ptr switch_ret_t65; tll_ptr switch_ret_t66;
  tll_ptr switch_ret_t69; tll_ptr true_t67; tll_ptr x_v140627;
  tll_ptr y_v140628;
  switch(((tll_node)x_v140624)->tag) {
    case 4:
      switch(((tll_node)y_v140625)->tag) {
        case 4:
          instr_struct(&true_t67, 2, 0);
          switch_ret_t66 = true_t67;
          break;
        case 5:
          __v140626 = ((tll_node)y_v140625)->data[0];
          instr_struct(&false_t68, 3, 0);
          switch_ret_t66 = false_t68;
          break;
      }
      switch_ret_t65 = switch_ret_t66;
      break;
    case 5:
      x_v140627 = ((tll_node)x_v140624)->data[0];
      switch(((tll_node)y_v140625)->tag) {
        case 4:
          instr_struct(&false_t70, 3, 0);
          switch_ret_t69 = false_t70;
          break;
        case 5:
          y_v140628 = ((tll_node)y_v140625)->data[0];
          call_ret_t71 = eqn_i8(x_v140627, y_v140628);
          switch_ret_t69 = call_ret_t71;
          break;
      }
      switch_ret_t65 = switch_ret_t69;
      break;
  }
  return switch_ret_t65;
}

tll_ptr lam_fun_t73(tll_ptr y_v140631, tll_env env) {
  tll_ptr call_ret_t72;
  call_ret_t72 = eqn_i8(env[0], y_v140631);
  return call_ret_t72;
}

tll_ptr lam_fun_t75(tll_ptr x_v140629, tll_env env) {
  tll_ptr lam_clo_t74;
  instr_clo(&lam_clo_t74, &lam_fun_t73, 1, x_v140629);
  return lam_clo_t74;
}

tll_ptr pred_i9(tll_ptr x_v140632) {
  tll_ptr O_t78; tll_ptr switch_ret_t77; tll_ptr x_v140633;
  switch(((tll_node)x_v140632)->tag) {
    case 4:
      instr_struct(&O_t78, 4, 0);
      switch_ret_t77 = O_t78;
      break;
    case 5:
      x_v140633 = ((tll_node)x_v140632)->data[0];
      switch_ret_t77 = x_v140633;
      break;
  }
  return switch_ret_t77;
}

tll_ptr lam_fun_t80(tll_ptr x_v140634, tll_env env) {
  tll_ptr call_ret_t79;
  call_ret_t79 = pred_i9(x_v140634);
  return call_ret_t79;
}

tll_ptr addn_i10(tll_ptr x_v140635, tll_ptr y_v140636) {
  tll_ptr S_t84; tll_ptr call_ret_t83; tll_ptr switch_ret_t82;
  tll_ptr x_v140637;
  switch(((tll_node)x_v140635)->tag) {
    case 4:
      switch_ret_t82 = y_v140636;
      break;
    case 5:
      x_v140637 = ((tll_node)x_v140635)->data[0];
      call_ret_t83 = addn_i10(x_v140637, y_v140636);
      instr_struct(&S_t84, 5, 1, call_ret_t83);
      switch_ret_t82 = S_t84;
      break;
  }
  return switch_ret_t82;
}

tll_ptr lam_fun_t86(tll_ptr y_v140640, tll_env env) {
  tll_ptr call_ret_t85;
  call_ret_t85 = addn_i10(env[0], y_v140640);
  return call_ret_t85;
}

tll_ptr lam_fun_t88(tll_ptr x_v140638, tll_env env) {
  tll_ptr lam_clo_t87;
  instr_clo(&lam_clo_t87, &lam_fun_t86, 1, x_v140638);
  return lam_clo_t87;
}

tll_ptr subn_i11(tll_ptr x_v140641, tll_ptr y_v140642) {
  tll_ptr call_ret_t91; tll_ptr call_ret_t92; tll_ptr switch_ret_t90;
  tll_ptr y_v140643;
  switch(((tll_node)y_v140642)->tag) {
    case 4:
      switch_ret_t90 = x_v140641;
      break;
    case 5:
      y_v140643 = ((tll_node)y_v140642)->data[0];
      call_ret_t92 = pred_i9(x_v140641);
      call_ret_t91 = subn_i11(call_ret_t92, y_v140643);
      switch_ret_t90 = call_ret_t91;
      break;
  }
  return switch_ret_t90;
}

tll_ptr lam_fun_t94(tll_ptr y_v140646, tll_env env) {
  tll_ptr call_ret_t93;
  call_ret_t93 = subn_i11(env[0], y_v140646);
  return call_ret_t93;
}

tll_ptr lam_fun_t96(tll_ptr x_v140644, tll_env env) {
  tll_ptr lam_clo_t95;
  instr_clo(&lam_clo_t95, &lam_fun_t94, 1, x_v140644);
  return lam_clo_t95;
}

tll_ptr muln_i12(tll_ptr x_v140647, tll_ptr y_v140648) {
  tll_ptr O_t99; tll_ptr call_ret_t100; tll_ptr call_ret_t101;
  tll_ptr switch_ret_t98; tll_ptr x_v140649;
  switch(((tll_node)x_v140647)->tag) {
    case 4:
      instr_struct(&O_t99, 4, 0);
      switch_ret_t98 = O_t99;
      break;
    case 5:
      x_v140649 = ((tll_node)x_v140647)->data[0];
      call_ret_t101 = muln_i12(x_v140649, y_v140648);
      call_ret_t100 = addn_i10(y_v140648, call_ret_t101);
      switch_ret_t98 = call_ret_t100;
      break;
  }
  return switch_ret_t98;
}

tll_ptr lam_fun_t103(tll_ptr y_v140652, tll_env env) {
  tll_ptr call_ret_t102;
  call_ret_t102 = muln_i12(env[0], y_v140652);
  return call_ret_t102;
}

tll_ptr lam_fun_t105(tll_ptr x_v140650, tll_env env) {
  tll_ptr lam_clo_t104;
  instr_clo(&lam_clo_t104, &lam_fun_t103, 1, x_v140650);
  return lam_clo_t104;
}

tll_ptr divn_i13(tll_ptr x_v140653, tll_ptr y_v140654) {
  tll_ptr O_t109; tll_ptr S_t112; tll_ptr call_ret_t107;
  tll_ptr call_ret_t110; tll_ptr call_ret_t111; tll_ptr switch_ret_t108;
  call_ret_t107 = ltn_i6(x_v140653, y_v140654);
  switch(((tll_node)call_ret_t107)->tag) {
    case 2:
      instr_struct(&O_t109, 4, 0);
      switch_ret_t108 = O_t109;
      break;
    case 3:
      call_ret_t111 = subn_i11(x_v140653, y_v140654);
      call_ret_t110 = divn_i13(call_ret_t111, y_v140654);
      instr_struct(&S_t112, 5, 1, call_ret_t110);
      switch_ret_t108 = S_t112;
      break;
  }
  return switch_ret_t108;
}

tll_ptr lam_fun_t114(tll_ptr y_v140657, tll_env env) {
  tll_ptr call_ret_t113;
  call_ret_t113 = divn_i13(env[0], y_v140657);
  return call_ret_t113;
}

tll_ptr lam_fun_t116(tll_ptr x_v140655, tll_env env) {
  tll_ptr lam_clo_t115;
  instr_clo(&lam_clo_t115, &lam_fun_t114, 1, x_v140655);
  return lam_clo_t115;
}

tll_ptr modn_i14(tll_ptr x_v140658, tll_ptr y_v140659) {
  tll_ptr call_ret_t118; tll_ptr call_ret_t119; tll_ptr call_ret_t120;
  call_ret_t120 = divn_i13(x_v140658, y_v140659);
  call_ret_t119 = muln_i12(call_ret_t120, y_v140659);
  call_ret_t118 = subn_i11(x_v140658, call_ret_t119);
  return call_ret_t118;
}

tll_ptr lam_fun_t122(tll_ptr y_v140662, tll_env env) {
  tll_ptr call_ret_t121;
  call_ret_t121 = modn_i14(env[0], y_v140662);
  return call_ret_t121;
}

tll_ptr lam_fun_t124(tll_ptr x_v140660, tll_env env) {
  tll_ptr lam_clo_t123;
  instr_clo(&lam_clo_t123, &lam_fun_t122, 1, x_v140660);
  return lam_clo_t123;
}

tll_ptr cats_i15(tll_ptr s1_v140663, tll_ptr s2_v140664) {
  tll_ptr String_t128; tll_ptr c_v140665; tll_ptr call_ret_t127;
  tll_ptr s1_v140666; tll_ptr switch_ret_t126;
  switch(((tll_node)s1_v140663)->tag) {
    case 7:
      switch_ret_t126 = s2_v140664;
      break;
    case 8:
      c_v140665 = ((tll_node)s1_v140663)->data[0];
      s1_v140666 = ((tll_node)s1_v140663)->data[1];
      call_ret_t127 = cats_i15(s1_v140666, s2_v140664);
      instr_struct(&String_t128, 8, 2, c_v140665, call_ret_t127);
      switch_ret_t126 = String_t128;
      break;
  }
  return switch_ret_t126;
}

tll_ptr lam_fun_t130(tll_ptr s2_v140669, tll_env env) {
  tll_ptr call_ret_t129;
  call_ret_t129 = cats_i15(env[0], s2_v140669);
  return call_ret_t129;
}

tll_ptr lam_fun_t132(tll_ptr s1_v140667, tll_env env) {
  tll_ptr lam_clo_t131;
  instr_clo(&lam_clo_t131, &lam_fun_t130, 1, s1_v140667);
  return lam_clo_t131;
}

tll_ptr strlen_i16(tll_ptr s_v140670) {
  tll_ptr O_t135; tll_ptr S_t137; tll_ptr __v140671; tll_ptr call_ret_t136;
  tll_ptr s_v140672; tll_ptr switch_ret_t134;
  switch(((tll_node)s_v140670)->tag) {
    case 7:
      instr_struct(&O_t135, 4, 0);
      switch_ret_t134 = O_t135;
      break;
    case 8:
      __v140671 = ((tll_node)s_v140670)->data[0];
      s_v140672 = ((tll_node)s_v140670)->data[1];
      call_ret_t136 = strlen_i16(s_v140672);
      instr_struct(&S_t137, 5, 1, call_ret_t136);
      switch_ret_t134 = S_t137;
      break;
  }
  return switch_ret_t134;
}

tll_ptr lam_fun_t139(tll_ptr s_v140673, tll_env env) {
  tll_ptr call_ret_t138;
  call_ret_t138 = strlen_i16(s_v140673);
  return call_ret_t138;
}

tll_ptr lenUU_i43(tll_ptr A_v140674, tll_ptr xs_v140675) {
  tll_ptr O_t142; tll_ptr S_t147; tll_ptr call_ret_t145; tll_ptr consUU_t148;
  tll_ptr n_v140678; tll_ptr nilUU_t143; tll_ptr pair_struct_t144;
  tll_ptr pair_struct_t149; tll_ptr switch_ret_t141; tll_ptr switch_ret_t146;
  tll_ptr x_v140676; tll_ptr xs_v140677; tll_ptr xs_v140679;
  switch(((tll_node)xs_v140675)->tag) {
    case 18:
      instr_struct(&O_t142, 4, 0);
      instr_struct(&nilUU_t143, 18, 0);
      instr_struct(&pair_struct_t144, 0, 2, O_t142, nilUU_t143);
      switch_ret_t141 = pair_struct_t144;
      break;
    case 19:
      x_v140676 = ((tll_node)xs_v140675)->data[0];
      xs_v140677 = ((tll_node)xs_v140675)->data[1];
      call_ret_t145 = lenUU_i43(0, xs_v140677);
      switch(((tll_node)call_ret_t145)->tag) {
        case 0:
          n_v140678 = ((tll_node)call_ret_t145)->data[0];
          xs_v140679 = ((tll_node)call_ret_t145)->data[1];
          instr_free_struct(call_ret_t145);
          instr_struct(&S_t147, 5, 1, n_v140678);
          instr_struct(&consUU_t148, 19, 2, x_v140676, xs_v140679);
          instr_struct(&pair_struct_t149, 0, 2, S_t147, consUU_t148);
          switch_ret_t146 = pair_struct_t149;
          break;
      }
      switch_ret_t141 = switch_ret_t146;
      break;
  }
  return switch_ret_t141;
}

tll_ptr lam_fun_t151(tll_ptr xs_v140682, tll_env env) {
  tll_ptr call_ret_t150;
  call_ret_t150 = lenUU_i43(env[0], xs_v140682);
  return call_ret_t150;
}

tll_ptr lam_fun_t153(tll_ptr A_v140680, tll_env env) {
  tll_ptr lam_clo_t152;
  instr_clo(&lam_clo_t152, &lam_fun_t151, 1, A_v140680);
  return lam_clo_t152;
}

tll_ptr lenUL_i42(tll_ptr A_v140683, tll_ptr xs_v140684) {
  tll_ptr O_t156; tll_ptr S_t161; tll_ptr call_ret_t159; tll_ptr consUL_t162;
  tll_ptr n_v140687; tll_ptr nilUL_t157; tll_ptr pair_struct_t158;
  tll_ptr pair_struct_t163; tll_ptr switch_ret_t155; tll_ptr switch_ret_t160;
  tll_ptr x_v140685; tll_ptr xs_v140686; tll_ptr xs_v140688;
  switch(((tll_node)xs_v140684)->tag) {
    case 16:
      instr_free_struct(xs_v140684);
      instr_struct(&O_t156, 4, 0);
      instr_struct(&nilUL_t157, 16, 0);
      instr_struct(&pair_struct_t158, 0, 2, O_t156, nilUL_t157);
      switch_ret_t155 = pair_struct_t158;
      break;
    case 17:
      x_v140685 = ((tll_node)xs_v140684)->data[0];
      xs_v140686 = ((tll_node)xs_v140684)->data[1];
      instr_free_struct(xs_v140684);
      call_ret_t159 = lenUL_i42(0, xs_v140686);
      switch(((tll_node)call_ret_t159)->tag) {
        case 0:
          n_v140687 = ((tll_node)call_ret_t159)->data[0];
          xs_v140688 = ((tll_node)call_ret_t159)->data[1];
          instr_free_struct(call_ret_t159);
          instr_struct(&S_t161, 5, 1, n_v140687);
          instr_struct(&consUL_t162, 17, 2, x_v140685, xs_v140688);
          instr_struct(&pair_struct_t163, 0, 2, S_t161, consUL_t162);
          switch_ret_t160 = pair_struct_t163;
          break;
      }
      switch_ret_t155 = switch_ret_t160;
      break;
  }
  return switch_ret_t155;
}

tll_ptr lam_fun_t165(tll_ptr xs_v140691, tll_env env) {
  tll_ptr call_ret_t164;
  call_ret_t164 = lenUL_i42(env[0], xs_v140691);
  return call_ret_t164;
}

tll_ptr lam_fun_t167(tll_ptr A_v140689, tll_env env) {
  tll_ptr lam_clo_t166;
  instr_clo(&lam_clo_t166, &lam_fun_t165, 1, A_v140689);
  return lam_clo_t166;
}

tll_ptr lenLL_i40(tll_ptr A_v140692, tll_ptr xs_v140693) {
  tll_ptr O_t170; tll_ptr S_t175; tll_ptr call_ret_t173; tll_ptr consLL_t176;
  tll_ptr n_v140696; tll_ptr nilLL_t171; tll_ptr pair_struct_t172;
  tll_ptr pair_struct_t177; tll_ptr switch_ret_t169; tll_ptr switch_ret_t174;
  tll_ptr x_v140694; tll_ptr xs_v140695; tll_ptr xs_v140697;
  switch(((tll_node)xs_v140693)->tag) {
    case 12:
      instr_free_struct(xs_v140693);
      instr_struct(&O_t170, 4, 0);
      instr_struct(&nilLL_t171, 12, 0);
      instr_struct(&pair_struct_t172, 0, 2, O_t170, nilLL_t171);
      switch_ret_t169 = pair_struct_t172;
      break;
    case 13:
      x_v140694 = ((tll_node)xs_v140693)->data[0];
      xs_v140695 = ((tll_node)xs_v140693)->data[1];
      instr_free_struct(xs_v140693);
      call_ret_t173 = lenLL_i40(0, xs_v140695);
      switch(((tll_node)call_ret_t173)->tag) {
        case 0:
          n_v140696 = ((tll_node)call_ret_t173)->data[0];
          xs_v140697 = ((tll_node)call_ret_t173)->data[1];
          instr_free_struct(call_ret_t173);
          instr_struct(&S_t175, 5, 1, n_v140696);
          instr_struct(&consLL_t176, 13, 2, x_v140694, xs_v140697);
          instr_struct(&pair_struct_t177, 0, 2, S_t175, consLL_t176);
          switch_ret_t174 = pair_struct_t177;
          break;
      }
      switch_ret_t169 = switch_ret_t174;
      break;
  }
  return switch_ret_t169;
}

tll_ptr lam_fun_t179(tll_ptr xs_v140700, tll_env env) {
  tll_ptr call_ret_t178;
  call_ret_t178 = lenLL_i40(env[0], xs_v140700);
  return call_ret_t178;
}

tll_ptr lam_fun_t181(tll_ptr A_v140698, tll_env env) {
  tll_ptr lam_clo_t180;
  instr_clo(&lam_clo_t180, &lam_fun_t179, 1, A_v140698);
  return lam_clo_t180;
}

tll_ptr appendUU_i47(tll_ptr A_v140701, tll_ptr xs_v140702, tll_ptr ys_v140703) {
  tll_ptr call_ret_t184; tll_ptr consUU_t185; tll_ptr switch_ret_t183;
  tll_ptr x_v140704; tll_ptr xs_v140705;
  switch(((tll_node)xs_v140702)->tag) {
    case 18:
      switch_ret_t183 = ys_v140703;
      break;
    case 19:
      x_v140704 = ((tll_node)xs_v140702)->data[0];
      xs_v140705 = ((tll_node)xs_v140702)->data[1];
      call_ret_t184 = appendUU_i47(0, xs_v140705, ys_v140703);
      instr_struct(&consUU_t185, 19, 2, x_v140704, call_ret_t184);
      switch_ret_t183 = consUU_t185;
      break;
  }
  return switch_ret_t183;
}

tll_ptr lam_fun_t187(tll_ptr ys_v140711, tll_env env) {
  tll_ptr call_ret_t186;
  call_ret_t186 = appendUU_i47(env[1], env[0], ys_v140711);
  return call_ret_t186;
}

tll_ptr lam_fun_t189(tll_ptr xs_v140709, tll_env env) {
  tll_ptr lam_clo_t188;
  instr_clo(&lam_clo_t188, &lam_fun_t187, 2, xs_v140709, env[0]);
  return lam_clo_t188;
}

tll_ptr lam_fun_t191(tll_ptr A_v140706, tll_env env) {
  tll_ptr lam_clo_t190;
  instr_clo(&lam_clo_t190, &lam_fun_t189, 1, A_v140706);
  return lam_clo_t190;
}

tll_ptr appendUL_i46(tll_ptr A_v140712, tll_ptr xs_v140713, tll_ptr ys_v140714) {
  tll_ptr call_ret_t194; tll_ptr consUL_t195; tll_ptr switch_ret_t193;
  tll_ptr x_v140715; tll_ptr xs_v140716;
  switch(((tll_node)xs_v140713)->tag) {
    case 16:
      instr_free_struct(xs_v140713);
      switch_ret_t193 = ys_v140714;
      break;
    case 17:
      x_v140715 = ((tll_node)xs_v140713)->data[0];
      xs_v140716 = ((tll_node)xs_v140713)->data[1];
      instr_free_struct(xs_v140713);
      call_ret_t194 = appendUL_i46(0, xs_v140716, ys_v140714);
      instr_struct(&consUL_t195, 17, 2, x_v140715, call_ret_t194);
      switch_ret_t193 = consUL_t195;
      break;
  }
  return switch_ret_t193;
}

tll_ptr lam_fun_t197(tll_ptr ys_v140722, tll_env env) {
  tll_ptr call_ret_t196;
  call_ret_t196 = appendUL_i46(env[1], env[0], ys_v140722);
  return call_ret_t196;
}

tll_ptr lam_fun_t199(tll_ptr xs_v140720, tll_env env) {
  tll_ptr lam_clo_t198;
  instr_clo(&lam_clo_t198, &lam_fun_t197, 2, xs_v140720, env[0]);
  return lam_clo_t198;
}

tll_ptr lam_fun_t201(tll_ptr A_v140717, tll_env env) {
  tll_ptr lam_clo_t200;
  instr_clo(&lam_clo_t200, &lam_fun_t199, 1, A_v140717);
  return lam_clo_t200;
}

tll_ptr appendLL_i44(tll_ptr A_v140723, tll_ptr xs_v140724, tll_ptr ys_v140725) {
  tll_ptr call_ret_t204; tll_ptr consLL_t205; tll_ptr switch_ret_t203;
  tll_ptr x_v140726; tll_ptr xs_v140727;
  switch(((tll_node)xs_v140724)->tag) {
    case 12:
      instr_free_struct(xs_v140724);
      switch_ret_t203 = ys_v140725;
      break;
    case 13:
      x_v140726 = ((tll_node)xs_v140724)->data[0];
      xs_v140727 = ((tll_node)xs_v140724)->data[1];
      instr_free_struct(xs_v140724);
      call_ret_t204 = appendLL_i44(0, xs_v140727, ys_v140725);
      instr_struct(&consLL_t205, 13, 2, x_v140726, call_ret_t204);
      switch_ret_t203 = consLL_t205;
      break;
  }
  return switch_ret_t203;
}

tll_ptr lam_fun_t207(tll_ptr ys_v140733, tll_env env) {
  tll_ptr call_ret_t206;
  call_ret_t206 = appendLL_i44(env[1], env[0], ys_v140733);
  return call_ret_t206;
}

tll_ptr lam_fun_t209(tll_ptr xs_v140731, tll_env env) {
  tll_ptr lam_clo_t208;
  instr_clo(&lam_clo_t208, &lam_fun_t207, 2, xs_v140731, env[0]);
  return lam_clo_t208;
}

tll_ptr lam_fun_t211(tll_ptr A_v140728, tll_env env) {
  tll_ptr lam_clo_t210;
  instr_clo(&lam_clo_t210, &lam_fun_t209, 1, A_v140728);
  return lam_clo_t210;
}

tll_ptr lam_fun_t221(tll_ptr __v140735, tll_env env) {
  tll_ptr __v140746; tll_ptr __v140750; tll_ptr __v140751;
  tll_ptr ch_v140744; tll_ptr ch_v140745; tll_ptr ch_v140748;
  tll_ptr ch_v140749; tll_ptr false_t219; tll_ptr prim_ch_t213;
  tll_ptr recv_msg_t216; tll_ptr s_v140747; tll_ptr send_ch_t214;
  tll_ptr send_ch_t218; tll_ptr switch_ret_t217; tll_ptr true_t215;
  tll_ptr tt_t220;
  instr_open(&prim_ch_t213, &proc_stdin);
  ch_v140744 = prim_ch_t213;
  instr_struct(&true_t215, 2, 0);
  instr_send(&send_ch_t214, ch_v140744, true_t215);
  ch_v140745 = send_ch_t214;
  instr_recv(&recv_msg_t216, ch_v140745);
  __v140746 = recv_msg_t216;
  switch(((tll_node)__v140746)->tag) {
    case 0:
      s_v140747 = ((tll_node)__v140746)->data[0];
      ch_v140748 = ((tll_node)__v140746)->data[1];
      instr_free_struct(__v140746);
      instr_struct(&false_t219, 3, 0);
      instr_send(&send_ch_t218, ch_v140748, false_t219);
      ch_v140749 = send_ch_t218;
      __v140751 = ch_v140749;
      instr_struct(&tt_t220, 1, 0);
      __v140750 = tt_t220;
      switch_ret_t217 = s_v140747;
      break;
  }
  return switch_ret_t217;
}

tll_ptr readline_i25(tll_ptr __v140734) {
  tll_ptr lam_clo_t222;
  instr_clo(&lam_clo_t222, &lam_fun_t221, 0);
  return lam_clo_t222;
}

tll_ptr lam_fun_t224(tll_ptr __v140752, tll_env env) {
  tll_ptr call_ret_t223;
  call_ret_t223 = readline_i25(__v140752);
  return call_ret_t223;
}

tll_ptr lam_fun_t233(tll_ptr __v140754, tll_env env) {
  tll_ptr __v140764; tll_ptr ch_v140760; tll_ptr ch_v140761;
  tll_ptr ch_v140762; tll_ptr ch_v140763; tll_ptr false_t231;
  tll_ptr prim_ch_t226; tll_ptr send_ch_t227; tll_ptr send_ch_t229;
  tll_ptr send_ch_t230; tll_ptr true_t228; tll_ptr tt_t232;
  instr_open(&prim_ch_t226, &proc_stdout);
  ch_v140760 = prim_ch_t226;
  instr_struct(&true_t228, 2, 0);
  instr_send(&send_ch_t227, ch_v140760, true_t228);
  ch_v140761 = send_ch_t227;
  instr_send(&send_ch_t229, ch_v140761, env[0]);
  ch_v140762 = send_ch_t229;
  instr_struct(&false_t231, 3, 0);
  instr_send(&send_ch_t230, ch_v140762, false_t231);
  ch_v140763 = send_ch_t230;
  __v140764 = ch_v140763;
  instr_struct(&tt_t232, 1, 0);
  return tt_t232;
}

tll_ptr print_i26(tll_ptr s_v140753) {
  tll_ptr lam_clo_t234;
  instr_clo(&lam_clo_t234, &lam_fun_t233, 1, s_v140753);
  return lam_clo_t234;
}

tll_ptr lam_fun_t236(tll_ptr s_v140765, tll_env env) {
  tll_ptr call_ret_t235;
  call_ret_t235 = print_i26(s_v140765);
  return call_ret_t235;
}

tll_ptr lam_fun_t245(tll_ptr __v140767, tll_env env) {
  tll_ptr __v140777; tll_ptr ch_v140773; tll_ptr ch_v140774;
  tll_ptr ch_v140775; tll_ptr ch_v140776; tll_ptr false_t243;
  tll_ptr prim_ch_t238; tll_ptr send_ch_t239; tll_ptr send_ch_t241;
  tll_ptr send_ch_t242; tll_ptr true_t240; tll_ptr tt_t244;
  instr_open(&prim_ch_t238, &proc_stderr);
  ch_v140773 = prim_ch_t238;
  instr_struct(&true_t240, 2, 0);
  instr_send(&send_ch_t239, ch_v140773, true_t240);
  ch_v140774 = send_ch_t239;
  instr_send(&send_ch_t241, ch_v140774, env[0]);
  ch_v140775 = send_ch_t241;
  instr_struct(&false_t243, 3, 0);
  instr_send(&send_ch_t242, ch_v140775, false_t243);
  ch_v140776 = send_ch_t242;
  __v140777 = ch_v140776;
  instr_struct(&tt_t244, 1, 0);
  return tt_t244;
}

tll_ptr prerr_i27(tll_ptr s_v140766) {
  tll_ptr lam_clo_t246;
  instr_clo(&lam_clo_t246, &lam_fun_t245, 1, s_v140766);
  return lam_clo_t246;
}

tll_ptr lam_fun_t248(tll_ptr s_v140778, tll_env env) {
  tll_ptr call_ret_t247;
  call_ret_t247 = prerr_i27(s_v140778);
  return call_ret_t247;
}

tll_ptr splitU_i49(tll_ptr zs_v140779) {
  tll_ptr __v140784; tll_ptr call_ret_t259; tll_ptr consUU_t256;
  tll_ptr consUU_t261; tll_ptr consUU_t262; tll_ptr nilUU_t251;
  tll_ptr nilUU_t252; tll_ptr nilUU_t255; tll_ptr nilUU_t257;
  tll_ptr pair_struct_t253; tll_ptr pair_struct_t258;
  tll_ptr pair_struct_t263; tll_ptr switch_ret_t250; tll_ptr switch_ret_t254;
  tll_ptr switch_ret_t260; tll_ptr x_v140780; tll_ptr xs_v140785;
  tll_ptr y_v140782; tll_ptr ys_v140786; tll_ptr zs_v140781;
  tll_ptr zs_v140783;
  switch(((tll_node)zs_v140779)->tag) {
    case 18:
      instr_struct(&nilUU_t251, 18, 0);
      instr_struct(&nilUU_t252, 18, 0);
      instr_struct(&pair_struct_t253, 0, 2, nilUU_t251, nilUU_t252);
      switch_ret_t250 = pair_struct_t253;
      break;
    case 19:
      x_v140780 = ((tll_node)zs_v140779)->data[0];
      zs_v140781 = ((tll_node)zs_v140779)->data[1];
      switch(((tll_node)zs_v140781)->tag) {
        case 18:
          instr_struct(&nilUU_t255, 18, 0);
          instr_struct(&consUU_t256, 19, 2, x_v140780, nilUU_t255);
          instr_struct(&nilUU_t257, 18, 0);
          instr_struct(&pair_struct_t258, 0, 2, consUU_t256, nilUU_t257);
          switch_ret_t254 = pair_struct_t258;
          break;
        case 19:
          y_v140782 = ((tll_node)zs_v140781)->data[0];
          zs_v140783 = ((tll_node)zs_v140781)->data[1];
          call_ret_t259 = splitU_i49(zs_v140783);
          __v140784 = call_ret_t259;
          switch(((tll_node)__v140784)->tag) {
            case 0:
              xs_v140785 = ((tll_node)__v140784)->data[0];
              ys_v140786 = ((tll_node)__v140784)->data[1];
              instr_free_struct(__v140784);
              instr_struct(&consUU_t261, 19, 2, x_v140780, xs_v140785);
              instr_struct(&consUU_t262, 19, 2, y_v140782, ys_v140786);
              instr_struct(&pair_struct_t263, 0, 2, consUU_t261, consUU_t262);
              switch_ret_t260 = pair_struct_t263;
              break;
          }
          switch_ret_t254 = switch_ret_t260;
          break;
      }
      switch_ret_t250 = switch_ret_t254;
      break;
  }
  return switch_ret_t250;
}

tll_ptr lam_fun_t265(tll_ptr zs_v140787, tll_env env) {
  tll_ptr call_ret_t264;
  call_ret_t264 = splitU_i49(zs_v140787);
  return call_ret_t264;
}

tll_ptr splitL_i48(tll_ptr zs_v140788) {
  tll_ptr __v140793; tll_ptr call_ret_t276; tll_ptr consUL_t273;
  tll_ptr consUL_t278; tll_ptr consUL_t279; tll_ptr nilUL_t268;
  tll_ptr nilUL_t269; tll_ptr nilUL_t272; tll_ptr nilUL_t274;
  tll_ptr pair_struct_t270; tll_ptr pair_struct_t275;
  tll_ptr pair_struct_t280; tll_ptr switch_ret_t267; tll_ptr switch_ret_t271;
  tll_ptr switch_ret_t277; tll_ptr x_v140789; tll_ptr xs_v140794;
  tll_ptr y_v140791; tll_ptr ys_v140795; tll_ptr zs_v140790;
  tll_ptr zs_v140792;
  switch(((tll_node)zs_v140788)->tag) {
    case 16:
      instr_free_struct(zs_v140788);
      instr_struct(&nilUL_t268, 16, 0);
      instr_struct(&nilUL_t269, 16, 0);
      instr_struct(&pair_struct_t270, 0, 2, nilUL_t268, nilUL_t269);
      switch_ret_t267 = pair_struct_t270;
      break;
    case 17:
      x_v140789 = ((tll_node)zs_v140788)->data[0];
      zs_v140790 = ((tll_node)zs_v140788)->data[1];
      instr_free_struct(zs_v140788);
      switch(((tll_node)zs_v140790)->tag) {
        case 16:
          instr_free_struct(zs_v140790);
          instr_struct(&nilUL_t272, 16, 0);
          instr_struct(&consUL_t273, 17, 2, x_v140789, nilUL_t272);
          instr_struct(&nilUL_t274, 16, 0);
          instr_struct(&pair_struct_t275, 0, 2, consUL_t273, nilUL_t274);
          switch_ret_t271 = pair_struct_t275;
          break;
        case 17:
          y_v140791 = ((tll_node)zs_v140790)->data[0];
          zs_v140792 = ((tll_node)zs_v140790)->data[1];
          instr_free_struct(zs_v140790);
          call_ret_t276 = splitL_i48(zs_v140792);
          __v140793 = call_ret_t276;
          switch(((tll_node)__v140793)->tag) {
            case 0:
              xs_v140794 = ((tll_node)__v140793)->data[0];
              ys_v140795 = ((tll_node)__v140793)->data[1];
              instr_free_struct(__v140793);
              instr_struct(&consUL_t278, 17, 2, x_v140789, xs_v140794);
              instr_struct(&consUL_t279, 17, 2, y_v140791, ys_v140795);
              instr_struct(&pair_struct_t280, 0, 2, consUL_t278, consUL_t279);
              switch_ret_t277 = pair_struct_t280;
              break;
          }
          switch_ret_t271 = switch_ret_t277;
          break;
      }
      switch_ret_t267 = switch_ret_t271;
      break;
  }
  return switch_ret_t267;
}

tll_ptr lam_fun_t282(tll_ptr zs_v140796, tll_env env) {
  tll_ptr call_ret_t281;
  call_ret_t281 = splitL_i48(zs_v140796);
  return call_ret_t281;
}

tll_ptr mergeU_i51(tll_ptr xs_v140797, tll_ptr ys_v140798) {
  tll_ptr call_ret_t287; tll_ptr call_ret_t289; tll_ptr call_ret_t292;
  tll_ptr consUU_t286; tll_ptr consUU_t290; tll_ptr consUU_t291;
  tll_ptr consUU_t293; tll_ptr consUU_t294; tll_ptr switch_ret_t284;
  tll_ptr switch_ret_t285; tll_ptr switch_ret_t288; tll_ptr x_v140799;
  tll_ptr xs0_v140800; tll_ptr y_v140801; tll_ptr ys0_v140802;
  switch(((tll_node)xs_v140797)->tag) {
    case 18:
      switch_ret_t284 = ys_v140798;
      break;
    case 19:
      x_v140799 = ((tll_node)xs_v140797)->data[0];
      xs0_v140800 = ((tll_node)xs_v140797)->data[1];
      switch(((tll_node)ys_v140798)->tag) {
        case 18:
          instr_struct(&consUU_t286, 19, 2, x_v140799, xs0_v140800);
          switch_ret_t285 = consUU_t286;
          break;
        case 19:
          y_v140801 = ((tll_node)ys_v140798)->data[0];
          ys0_v140802 = ((tll_node)ys_v140798)->data[1];
          call_ret_t287 = lten_i4(x_v140799, y_v140801);
          switch(((tll_node)call_ret_t287)->tag) {
            case 2:
              instr_struct(&consUU_t290, 19, 2, y_v140801, ys0_v140802);
              call_ret_t289 = mergeU_i51(xs0_v140800, consUU_t290);
              instr_struct(&consUU_t291, 19, 2, x_v140799, call_ret_t289);
              switch_ret_t288 = consUU_t291;
              break;
            case 3:
              instr_struct(&consUU_t293, 19, 2, x_v140799, xs0_v140800);
              call_ret_t292 = mergeU_i51(consUU_t293, ys0_v140802);
              instr_struct(&consUU_t294, 19, 2, y_v140801, call_ret_t292);
              switch_ret_t288 = consUU_t294;
              break;
          }
          switch_ret_t285 = switch_ret_t288;
          break;
      }
      switch_ret_t284 = switch_ret_t285;
      break;
  }
  return switch_ret_t284;
}

tll_ptr lam_fun_t296(tll_ptr ys_v140805, tll_env env) {
  tll_ptr call_ret_t295;
  call_ret_t295 = mergeU_i51(env[0], ys_v140805);
  return call_ret_t295;
}

tll_ptr lam_fun_t298(tll_ptr xs_v140803, tll_env env) {
  tll_ptr lam_clo_t297;
  instr_clo(&lam_clo_t297, &lam_fun_t296, 1, xs_v140803);
  return lam_clo_t297;
}

tll_ptr mergeL_i50(tll_ptr xs_v140806, tll_ptr ys_v140807) {
  tll_ptr call_ret_t303; tll_ptr call_ret_t305; tll_ptr call_ret_t308;
  tll_ptr consUL_t302; tll_ptr consUL_t306; tll_ptr consUL_t307;
  tll_ptr consUL_t309; tll_ptr consUL_t310; tll_ptr switch_ret_t300;
  tll_ptr switch_ret_t301; tll_ptr switch_ret_t304; tll_ptr x_v140808;
  tll_ptr xs0_v140809; tll_ptr y_v140810; tll_ptr ys0_v140811;
  switch(((tll_node)xs_v140806)->tag) {
    case 16:
      instr_free_struct(xs_v140806);
      switch_ret_t300 = ys_v140807;
      break;
    case 17:
      x_v140808 = ((tll_node)xs_v140806)->data[0];
      xs0_v140809 = ((tll_node)xs_v140806)->data[1];
      instr_free_struct(xs_v140806);
      switch(((tll_node)ys_v140807)->tag) {
        case 16:
          instr_free_struct(ys_v140807);
          instr_struct(&consUL_t302, 17, 2, x_v140808, xs0_v140809);
          switch_ret_t301 = consUL_t302;
          break;
        case 17:
          y_v140810 = ((tll_node)ys_v140807)->data[0];
          ys0_v140811 = ((tll_node)ys_v140807)->data[1];
          instr_free_struct(ys_v140807);
          call_ret_t303 = lten_i4(x_v140808, y_v140810);
          switch(((tll_node)call_ret_t303)->tag) {
            case 2:
              instr_struct(&consUL_t306, 17, 2, y_v140810, ys0_v140811);
              call_ret_t305 = mergeL_i50(xs0_v140809, consUL_t306);
              instr_struct(&consUL_t307, 17, 2, x_v140808, call_ret_t305);
              switch_ret_t304 = consUL_t307;
              break;
            case 3:
              instr_struct(&consUL_t309, 17, 2, x_v140808, xs0_v140809);
              call_ret_t308 = mergeL_i50(consUL_t309, ys0_v140811);
              instr_struct(&consUL_t310, 17, 2, y_v140810, call_ret_t308);
              switch_ret_t304 = consUL_t310;
              break;
          }
          switch_ret_t301 = switch_ret_t304;
          break;
      }
      switch_ret_t300 = switch_ret_t301;
      break;
  }
  return switch_ret_t300;
}

tll_ptr lam_fun_t312(tll_ptr ys_v140814, tll_env env) {
  tll_ptr call_ret_t311;
  call_ret_t311 = mergeL_i50(env[0], ys_v140814);
  return call_ret_t311;
}

tll_ptr lam_fun_t314(tll_ptr xs_v140812, tll_env env) {
  tll_ptr lam_clo_t313;
  instr_clo(&lam_clo_t313, &lam_fun_t312, 1, xs_v140812);
  return lam_clo_t313;
}

tll_ptr msortU_i53(tll_ptr zs_v140815) {
  tll_ptr __v140820; tll_ptr call_ret_t321; tll_ptr call_ret_t325;
  tll_ptr call_ret_t326; tll_ptr call_ret_t327; tll_ptr consUU_t320;
  tll_ptr consUU_t322; tll_ptr consUU_t323; tll_ptr nilUU_t317;
  tll_ptr nilUU_t319; tll_ptr switch_ret_t316; tll_ptr switch_ret_t318;
  tll_ptr switch_ret_t324; tll_ptr x_v140816; tll_ptr xs_v140821;
  tll_ptr y_v140818; tll_ptr ys_v140822; tll_ptr zs_v140817;
  tll_ptr zs_v140819;
  switch(((tll_node)zs_v140815)->tag) {
    case 18:
      instr_struct(&nilUU_t317, 18, 0);
      switch_ret_t316 = nilUU_t317;
      break;
    case 19:
      x_v140816 = ((tll_node)zs_v140815)->data[0];
      zs_v140817 = ((tll_node)zs_v140815)->data[1];
      switch(((tll_node)zs_v140817)->tag) {
        case 18:
          instr_struct(&nilUU_t319, 18, 0);
          instr_struct(&consUU_t320, 19, 2, x_v140816, nilUU_t319);
          switch_ret_t318 = consUU_t320;
          break;
        case 19:
          y_v140818 = ((tll_node)zs_v140817)->data[0];
          zs_v140819 = ((tll_node)zs_v140817)->data[1];
          instr_struct(&consUU_t322, 19, 2, y_v140818, zs_v140819);
          instr_struct(&consUU_t323, 19, 2, x_v140816, consUU_t322);
          call_ret_t321 = splitU_i49(consUU_t323);
          __v140820 = call_ret_t321;
          switch(((tll_node)__v140820)->tag) {
            case 0:
              xs_v140821 = ((tll_node)__v140820)->data[0];
              ys_v140822 = ((tll_node)__v140820)->data[1];
              instr_free_struct(__v140820);
              call_ret_t326 = msortU_i53(xs_v140821);
              call_ret_t327 = msortU_i53(ys_v140822);
              call_ret_t325 = mergeU_i51(call_ret_t326, call_ret_t327);
              switch_ret_t324 = call_ret_t325;
              break;
          }
          switch_ret_t318 = switch_ret_t324;
          break;
      }
      switch_ret_t316 = switch_ret_t318;
      break;
  }
  return switch_ret_t316;
}

tll_ptr lam_fun_t329(tll_ptr zs_v140823, tll_env env) {
  tll_ptr call_ret_t328;
  call_ret_t328 = msortU_i53(zs_v140823);
  return call_ret_t328;
}

tll_ptr msortL_i52(tll_ptr zs_v140824) {
  tll_ptr __v140829; tll_ptr call_ret_t336; tll_ptr call_ret_t340;
  tll_ptr call_ret_t341; tll_ptr call_ret_t342; tll_ptr consUL_t335;
  tll_ptr consUL_t337; tll_ptr consUL_t338; tll_ptr nilUL_t332;
  tll_ptr nilUL_t334; tll_ptr switch_ret_t331; tll_ptr switch_ret_t333;
  tll_ptr switch_ret_t339; tll_ptr x_v140825; tll_ptr xs_v140830;
  tll_ptr y_v140827; tll_ptr ys_v140831; tll_ptr zs_v140826;
  tll_ptr zs_v140828;
  switch(((tll_node)zs_v140824)->tag) {
    case 16:
      instr_free_struct(zs_v140824);
      instr_struct(&nilUL_t332, 16, 0);
      switch_ret_t331 = nilUL_t332;
      break;
    case 17:
      x_v140825 = ((tll_node)zs_v140824)->data[0];
      zs_v140826 = ((tll_node)zs_v140824)->data[1];
      instr_free_struct(zs_v140824);
      switch(((tll_node)zs_v140826)->tag) {
        case 16:
          instr_free_struct(zs_v140826);
          instr_struct(&nilUL_t334, 16, 0);
          instr_struct(&consUL_t335, 17, 2, x_v140825, nilUL_t334);
          switch_ret_t333 = consUL_t335;
          break;
        case 17:
          y_v140827 = ((tll_node)zs_v140826)->data[0];
          zs_v140828 = ((tll_node)zs_v140826)->data[1];
          instr_free_struct(zs_v140826);
          instr_struct(&consUL_t337, 17, 2, y_v140827, zs_v140828);
          instr_struct(&consUL_t338, 17, 2, x_v140825, consUL_t337);
          call_ret_t336 = splitL_i48(consUL_t338);
          __v140829 = call_ret_t336;
          switch(((tll_node)__v140829)->tag) {
            case 0:
              xs_v140830 = ((tll_node)__v140829)->data[0];
              ys_v140831 = ((tll_node)__v140829)->data[1];
              instr_free_struct(__v140829);
              call_ret_t341 = msortL_i52(xs_v140830);
              call_ret_t342 = msortL_i52(ys_v140831);
              call_ret_t340 = mergeL_i50(call_ret_t341, call_ret_t342);
              switch_ret_t339 = call_ret_t340;
              break;
          }
          switch_ret_t333 = switch_ret_t339;
          break;
      }
      switch_ret_t331 = switch_ret_t333;
      break;
  }
  return switch_ret_t331;
}

tll_ptr lam_fun_t344(tll_ptr zs_v140832, tll_env env) {
  tll_ptr call_ret_t343;
  call_ret_t343 = msortL_i52(zs_v140832);
  return call_ret_t343;
}

tll_ptr lam_fun_t351(tll_ptr __v140835, tll_env env) {
  tll_ptr UniqU_t349; tll_ptr __v140839; tll_ptr c_v140838;
  tll_ptr nilUU_t348; tll_ptr send_ch_t347; tll_ptr tt_t350;
  instr_struct(&nilUU_t348, 18, 0);
  instr_struct(&UniqU_t349, 21, 2, nilUU_t348, 0);
  instr_send(&send_ch_t347, env[0], UniqU_t349);
  c_v140838 = send_ch_t347;
  __v140839 = c_v140838;
  instr_struct(&tt_t350, 1, 0);
  return tt_t350;
}

tll_ptr lam_fun_t359(tll_ptr __v140842, tll_env env) {
  tll_ptr UniqU_t357; tll_ptr __v140846; tll_ptr c_v140845;
  tll_ptr consUU_t356; tll_ptr nilUU_t355; tll_ptr send_ch_t354;
  tll_ptr tt_t358;
  instr_struct(&nilUU_t355, 18, 0);
  instr_struct(&consUU_t356, 19, 2, env[0], nilUU_t355);
  instr_struct(&UniqU_t357, 21, 2, consUU_t356, 0);
  instr_send(&send_ch_t354, env[1], UniqU_t357);
  c_v140845 = send_ch_t354;
  __v140846 = c_v140845;
  instr_struct(&tt_t358, 1, 0);
  return tt_t358;
}

tll_ptr fork_fun_t367(tll_env env) {
  tll_ptr app_ret_t366; tll_ptr call_ret_t365; tll_ptr fork_ret_t369;
  call_ret_t365 = cmsort_workerU_i57(env[1], env[0]);
  instr_app(&app_ret_t366, call_ret_t365, 0);
  instr_free_clo(call_ret_t365);
  fork_ret_t369 = app_ret_t366;
  instr_free_thread(env);
  return fork_ret_t369;
}

tll_ptr fork_fun_t372(tll_env env) {
  tll_ptr app_ret_t371; tll_ptr call_ret_t370; tll_ptr fork_ret_t374;
  call_ret_t370 = cmsort_workerU_i57(env[1], env[0]);
  instr_app(&app_ret_t371, call_ret_t370, 0);
  instr_free_clo(call_ret_t370);
  fork_ret_t374 = app_ret_t371;
  instr_free_thread(env);
  return fork_ret_t374;
}

tll_ptr lam_fun_t387(tll_ptr __v140851, tll_env env) {
  tll_ptr UniqU_t383; tll_ptr __v140875; tll_ptr __v140878;
  tll_ptr __v140887; tll_ptr __v140888; tll_ptr __v140889; tll_ptr c_v140886;
  tll_ptr call_ret_t381; tll_ptr close_tmp_t384; tll_ptr close_tmp_t385;
  tll_ptr fork_ch_t368; tll_ptr fork_ch_t373; tll_ptr msg1_v140876;
  tll_ptr msg2_v140879; tll_ptr pf1_v140882; tll_ptr pf2_v140884;
  tll_ptr r1_v140871; tll_ptr r1_v140877; tll_ptr r2_v140873;
  tll_ptr r2_v140880; tll_ptr recv_msg_t375; tll_ptr recv_msg_t377;
  tll_ptr send_ch_t382; tll_ptr switch_ret_t376; tll_ptr switch_ret_t378;
  tll_ptr switch_ret_t379; tll_ptr switch_ret_t380; tll_ptr tt_t386;
  tll_ptr xs1_v140881; tll_ptr xs2_v140883; tll_ptr zs_v140885;
  instr_fork(&fork_ch_t368, &fork_fun_t367, 1, env[1]);
  r1_v140871 = fork_ch_t368;
  instr_fork(&fork_ch_t373, &fork_fun_t372, 1, env[0]);
  r2_v140873 = fork_ch_t373;
  instr_recv(&recv_msg_t375, r1_v140871);
  __v140875 = recv_msg_t375;
  switch(((tll_node)__v140875)->tag) {
    case 0:
      msg1_v140876 = ((tll_node)__v140875)->data[0];
      r1_v140877 = ((tll_node)__v140875)->data[1];
      instr_free_struct(__v140875);
      instr_recv(&recv_msg_t377, r2_v140873);
      __v140878 = recv_msg_t377;
      switch(((tll_node)__v140878)->tag) {
        case 0:
          msg2_v140879 = ((tll_node)__v140878)->data[0];
          r2_v140880 = ((tll_node)__v140878)->data[1];
          instr_free_struct(__v140878);
          switch(((tll_node)msg1_v140876)->tag) {
            case 21:
              xs1_v140881 = ((tll_node)msg1_v140876)->data[0];
              pf1_v140882 = ((tll_node)msg1_v140876)->data[1];
              switch(((tll_node)msg2_v140879)->tag) {
                case 21:
                  xs2_v140883 = ((tll_node)msg2_v140879)->data[0];
                  pf2_v140884 = ((tll_node)msg2_v140879)->data[1];
                  call_ret_t381 = mergeU_i51(xs1_v140881, xs2_v140883);
                  zs_v140885 = call_ret_t381;
                  instr_struct(&UniqU_t383, 21, 2, zs_v140885, 0);
                  instr_send(&send_ch_t382, env[2], UniqU_t383);
                  c_v140886 = send_ch_t382;
                  instr_close(&close_tmp_t384, r1_v140877);
                  __v140887 = close_tmp_t384;
                  instr_close(&close_tmp_t385, r2_v140880);
                  __v140888 = close_tmp_t385;
                  __v140889 = c_v140886;
                  instr_struct(&tt_t386, 1, 0);
                  switch_ret_t380 = tt_t386;
                  break;
              }
              switch_ret_t379 = switch_ret_t380;
              break;
          }
          switch_ret_t378 = switch_ret_t379;
          break;
      }
      switch_ret_t376 = switch_ret_t378;
      break;
  }
  return switch_ret_t376;
}

tll_ptr cmsort_workerU_i57(tll_ptr zs_v140833, tll_ptr c_v140834) {
  tll_ptr call_ret_t361; tll_ptr consUU_t362; tll_ptr consUU_t363;
  tll_ptr lam_clo_t352; tll_ptr lam_clo_t360; tll_ptr lam_clo_t388;
  tll_ptr switch_ret_t346; tll_ptr switch_ret_t353; tll_ptr switch_ret_t364;
  tll_ptr xs0_v140849; tll_ptr ys0_v140850; tll_ptr z0_v140840;
  tll_ptr z1_v140847; tll_ptr zs0_v140841; tll_ptr zs1_v140848;
  switch(((tll_node)zs_v140833)->tag) {
    case 18:
      instr_clo(&lam_clo_t352, &lam_fun_t351, 1, c_v140834);
      switch_ret_t346 = lam_clo_t352;
      break;
    case 19:
      z0_v140840 = ((tll_node)zs_v140833)->data[0];
      zs0_v140841 = ((tll_node)zs_v140833)->data[1];
      switch(((tll_node)zs0_v140841)->tag) {
        case 18:
          instr_clo(&lam_clo_t360, &lam_fun_t359, 2, z0_v140840, c_v140834);
          switch_ret_t353 = lam_clo_t360;
          break;
        case 19:
          z1_v140847 = ((tll_node)zs0_v140841)->data[0];
          zs1_v140848 = ((tll_node)zs0_v140841)->data[1];
          instr_struct(&consUU_t362, 19, 2, z1_v140847, zs1_v140848);
          instr_struct(&consUU_t363, 19, 2, z0_v140840, consUU_t362);
          call_ret_t361 = splitU_i49(consUU_t363);
          switch(((tll_node)call_ret_t361)->tag) {
            case 0:
              xs0_v140849 = ((tll_node)call_ret_t361)->data[0];
              ys0_v140850 = ((tll_node)call_ret_t361)->data[1];
              instr_free_struct(call_ret_t361);
              instr_clo(&lam_clo_t388, &lam_fun_t387, 3,
                        ys0_v140850, xs0_v140849, c_v140834);
              switch_ret_t364 = lam_clo_t388;
              break;
          }
          switch_ret_t353 = switch_ret_t364;
          break;
      }
      switch_ret_t346 = switch_ret_t353;
      break;
  }
  return switch_ret_t346;
}

tll_ptr lam_fun_t390(tll_ptr c_v140892, tll_env env) {
  tll_ptr call_ret_t389;
  call_ret_t389 = cmsort_workerU_i57(env[0], c_v140892);
  return call_ret_t389;
}

tll_ptr lam_fun_t392(tll_ptr zs_v140890, tll_env env) {
  tll_ptr lam_clo_t391;
  instr_clo(&lam_clo_t391, &lam_fun_t390, 1, zs_v140890);
  return lam_clo_t391;
}

tll_ptr lam_fun_t399(tll_ptr __v140895, tll_env env) {
  tll_ptr UniqL_t397; tll_ptr __v140899; tll_ptr c_v140898;
  tll_ptr nilUL_t396; tll_ptr send_ch_t395; tll_ptr tt_t398;
  instr_struct(&nilUL_t396, 16, 0);
  instr_struct(&UniqL_t397, 20, 2, nilUL_t396, 0);
  instr_send(&send_ch_t395, env[0], UniqL_t397);
  c_v140898 = send_ch_t395;
  __v140899 = c_v140898;
  instr_struct(&tt_t398, 1, 0);
  return tt_t398;
}

tll_ptr lam_fun_t407(tll_ptr __v140902, tll_env env) {
  tll_ptr UniqL_t405; tll_ptr __v140906; tll_ptr c_v140905;
  tll_ptr consUL_t404; tll_ptr nilUL_t403; tll_ptr send_ch_t402;
  tll_ptr tt_t406;
  instr_struct(&nilUL_t403, 16, 0);
  instr_struct(&consUL_t404, 17, 2, env[0], nilUL_t403);
  instr_struct(&UniqL_t405, 20, 2, consUL_t404, 0);
  instr_send(&send_ch_t402, env[1], UniqL_t405);
  c_v140905 = send_ch_t402;
  __v140906 = c_v140905;
  instr_struct(&tt_t406, 1, 0);
  return tt_t406;
}

tll_ptr fork_fun_t415(tll_env env) {
  tll_ptr app_ret_t414; tll_ptr call_ret_t413; tll_ptr fork_ret_t417;
  call_ret_t413 = cmsort_workerL_i56(env[1], env[0]);
  instr_app(&app_ret_t414, call_ret_t413, 0);
  instr_free_clo(call_ret_t413);
  fork_ret_t417 = app_ret_t414;
  instr_free_thread(env);
  return fork_ret_t417;
}

tll_ptr fork_fun_t420(tll_env env) {
  tll_ptr app_ret_t419; tll_ptr call_ret_t418; tll_ptr fork_ret_t422;
  call_ret_t418 = cmsort_workerL_i56(env[1], env[0]);
  instr_app(&app_ret_t419, call_ret_t418, 0);
  instr_free_clo(call_ret_t418);
  fork_ret_t422 = app_ret_t419;
  instr_free_thread(env);
  return fork_ret_t422;
}

tll_ptr lam_fun_t435(tll_ptr __v140911, tll_env env) {
  tll_ptr UniqL_t431; tll_ptr __v140935; tll_ptr __v140938;
  tll_ptr __v140947; tll_ptr __v140948; tll_ptr __v140949; tll_ptr c_v140946;
  tll_ptr call_ret_t429; tll_ptr close_tmp_t432; tll_ptr close_tmp_t433;
  tll_ptr fork_ch_t416; tll_ptr fork_ch_t421; tll_ptr msg1_v140936;
  tll_ptr msg2_v140939; tll_ptr pf1_v140942; tll_ptr pf2_v140944;
  tll_ptr r1_v140931; tll_ptr r1_v140937; tll_ptr r2_v140933;
  tll_ptr r2_v140940; tll_ptr recv_msg_t423; tll_ptr recv_msg_t425;
  tll_ptr send_ch_t430; tll_ptr switch_ret_t424; tll_ptr switch_ret_t426;
  tll_ptr switch_ret_t427; tll_ptr switch_ret_t428; tll_ptr tt_t434;
  tll_ptr xs1_v140941; tll_ptr xs2_v140943; tll_ptr zs_v140945;
  instr_fork(&fork_ch_t416, &fork_fun_t415, 1, env[1]);
  r1_v140931 = fork_ch_t416;
  instr_fork(&fork_ch_t421, &fork_fun_t420, 1, env[0]);
  r2_v140933 = fork_ch_t421;
  instr_recv(&recv_msg_t423, r1_v140931);
  __v140935 = recv_msg_t423;
  switch(((tll_node)__v140935)->tag) {
    case 0:
      msg1_v140936 = ((tll_node)__v140935)->data[0];
      r1_v140937 = ((tll_node)__v140935)->data[1];
      instr_free_struct(__v140935);
      instr_recv(&recv_msg_t425, r2_v140933);
      __v140938 = recv_msg_t425;
      switch(((tll_node)__v140938)->tag) {
        case 0:
          msg2_v140939 = ((tll_node)__v140938)->data[0];
          r2_v140940 = ((tll_node)__v140938)->data[1];
          instr_free_struct(__v140938);
          switch(((tll_node)msg1_v140936)->tag) {
            case 20:
              xs1_v140941 = ((tll_node)msg1_v140936)->data[0];
              pf1_v140942 = ((tll_node)msg1_v140936)->data[1];
              instr_free_struct(msg1_v140936);
              switch(((tll_node)msg2_v140939)->tag) {
                case 20:
                  xs2_v140943 = ((tll_node)msg2_v140939)->data[0];
                  pf2_v140944 = ((tll_node)msg2_v140939)->data[1];
                  instr_free_struct(msg2_v140939);
                  call_ret_t429 = mergeL_i50(xs1_v140941, xs2_v140943);
                  zs_v140945 = call_ret_t429;
                  instr_struct(&UniqL_t431, 20, 2, zs_v140945, 0);
                  instr_send(&send_ch_t430, env[2], UniqL_t431);
                  c_v140946 = send_ch_t430;
                  instr_close(&close_tmp_t432, r1_v140937);
                  __v140947 = close_tmp_t432;
                  instr_close(&close_tmp_t433, r2_v140940);
                  __v140948 = close_tmp_t433;
                  __v140949 = c_v140946;
                  instr_struct(&tt_t434, 1, 0);
                  switch_ret_t428 = tt_t434;
                  break;
              }
              switch_ret_t427 = switch_ret_t428;
              break;
          }
          switch_ret_t426 = switch_ret_t427;
          break;
      }
      switch_ret_t424 = switch_ret_t426;
      break;
  }
  return switch_ret_t424;
}

tll_ptr cmsort_workerL_i56(tll_ptr zs_v140893, tll_ptr c_v140894) {
  tll_ptr call_ret_t409; tll_ptr consUL_t410; tll_ptr consUL_t411;
  tll_ptr lam_clo_t400; tll_ptr lam_clo_t408; tll_ptr lam_clo_t436;
  tll_ptr switch_ret_t394; tll_ptr switch_ret_t401; tll_ptr switch_ret_t412;
  tll_ptr xs0_v140909; tll_ptr ys0_v140910; tll_ptr z0_v140900;
  tll_ptr z1_v140907; tll_ptr zs0_v140901; tll_ptr zs1_v140908;
  switch(((tll_node)zs_v140893)->tag) {
    case 16:
      instr_free_struct(zs_v140893);
      instr_clo(&lam_clo_t400, &lam_fun_t399, 1, c_v140894);
      switch_ret_t394 = lam_clo_t400;
      break;
    case 17:
      z0_v140900 = ((tll_node)zs_v140893)->data[0];
      zs0_v140901 = ((tll_node)zs_v140893)->data[1];
      instr_free_struct(zs_v140893);
      switch(((tll_node)zs0_v140901)->tag) {
        case 16:
          instr_free_struct(zs0_v140901);
          instr_clo(&lam_clo_t408, &lam_fun_t407, 2, z0_v140900, c_v140894);
          switch_ret_t401 = lam_clo_t408;
          break;
        case 17:
          z1_v140907 = ((tll_node)zs0_v140901)->data[0];
          zs1_v140908 = ((tll_node)zs0_v140901)->data[1];
          instr_free_struct(zs0_v140901);
          instr_struct(&consUL_t410, 17, 2, z1_v140907, zs1_v140908);
          instr_struct(&consUL_t411, 17, 2, z0_v140900, consUL_t410);
          call_ret_t409 = splitL_i48(consUL_t411);
          switch(((tll_node)call_ret_t409)->tag) {
            case 0:
              xs0_v140909 = ((tll_node)call_ret_t409)->data[0];
              ys0_v140910 = ((tll_node)call_ret_t409)->data[1];
              instr_free_struct(call_ret_t409);
              instr_clo(&lam_clo_t436, &lam_fun_t435, 3,
                        ys0_v140910, xs0_v140909, c_v140894);
              switch_ret_t412 = lam_clo_t436;
              break;
          }
          switch_ret_t401 = switch_ret_t412;
          break;
      }
      switch_ret_t394 = switch_ret_t401;
      break;
  }
  return switch_ret_t394;
}

tll_ptr lam_fun_t438(tll_ptr c_v140952, tll_env env) {
  tll_ptr call_ret_t437;
  call_ret_t437 = cmsort_workerL_i56(env[0], c_v140952);
  return call_ret_t437;
}

tll_ptr lam_fun_t440(tll_ptr zs_v140950, tll_env env) {
  tll_ptr lam_clo_t439;
  instr_clo(&lam_clo_t439, &lam_fun_t438, 1, zs_v140950);
  return lam_clo_t439;
}

tll_ptr fork_fun_t444(tll_env env) {
  tll_ptr app_ret_t443; tll_ptr call_ret_t442; tll_ptr fork_ret_t446;
  call_ret_t442 = cmsort_workerU_i57(env[1], env[0]);
  instr_app(&app_ret_t443, call_ret_t442, 0);
  instr_free_clo(call_ret_t442);
  fork_ret_t446 = app_ret_t443;
  instr_free_thread(env);
  return fork_ret_t446;
}

tll_ptr lam_fun_t450(tll_ptr __v140954, tll_env env) {
  tll_ptr __v140963; tll_ptr __v140966; tll_ptr c_v140961; tll_ptr c_v140965;
  tll_ptr close_tmp_t449; tll_ptr fork_ch_t445; tll_ptr msg_v140964;
  tll_ptr recv_msg_t447; tll_ptr switch_ret_t448;
  instr_fork(&fork_ch_t445, &fork_fun_t444, 1, env[0]);
  c_v140961 = fork_ch_t445;
  instr_recv(&recv_msg_t447, c_v140961);
  __v140963 = recv_msg_t447;
  switch(((tll_node)__v140963)->tag) {
    case 0:
      msg_v140964 = ((tll_node)__v140963)->data[0];
      c_v140965 = ((tll_node)__v140963)->data[1];
      instr_free_struct(__v140963);
      instr_close(&close_tmp_t449, c_v140965);
      __v140966 = close_tmp_t449;
      switch_ret_t448 = msg_v140964;
      break;
  }
  return switch_ret_t448;
}

tll_ptr cmsortU_i59(tll_ptr zs_v140953) {
  tll_ptr lam_clo_t451;
  instr_clo(&lam_clo_t451, &lam_fun_t450, 1, zs_v140953);
  return lam_clo_t451;
}

tll_ptr lam_fun_t453(tll_ptr zs_v140967, tll_env env) {
  tll_ptr call_ret_t452;
  call_ret_t452 = cmsortU_i59(zs_v140967);
  return call_ret_t452;
}

tll_ptr fork_fun_t457(tll_env env) {
  tll_ptr app_ret_t456; tll_ptr call_ret_t455; tll_ptr fork_ret_t459;
  call_ret_t455 = cmsort_workerL_i56(env[1], env[0]);
  instr_app(&app_ret_t456, call_ret_t455, 0);
  instr_free_clo(call_ret_t455);
  fork_ret_t459 = app_ret_t456;
  instr_free_thread(env);
  return fork_ret_t459;
}

tll_ptr lam_fun_t463(tll_ptr __v140969, tll_env env) {
  tll_ptr __v140978; tll_ptr __v140981; tll_ptr c_v140976; tll_ptr c_v140980;
  tll_ptr close_tmp_t462; tll_ptr fork_ch_t458; tll_ptr msg_v140979;
  tll_ptr recv_msg_t460; tll_ptr switch_ret_t461;
  instr_fork(&fork_ch_t458, &fork_fun_t457, 1, env[0]);
  c_v140976 = fork_ch_t458;
  instr_recv(&recv_msg_t460, c_v140976);
  __v140978 = recv_msg_t460;
  switch(((tll_node)__v140978)->tag) {
    case 0:
      msg_v140979 = ((tll_node)__v140978)->data[0];
      c_v140980 = ((tll_node)__v140978)->data[1];
      instr_free_struct(__v140978);
      instr_close(&close_tmp_t462, c_v140980);
      __v140981 = close_tmp_t462;
      switch_ret_t461 = msg_v140979;
      break;
  }
  return switch_ret_t461;
}

tll_ptr cmsortL_i58(tll_ptr zs_v140968) {
  tll_ptr lam_clo_t464;
  instr_clo(&lam_clo_t464, &lam_fun_t463, 1, zs_v140968);
  return lam_clo_t464;
}

tll_ptr lam_fun_t466(tll_ptr zs_v140982, tll_env env) {
  tll_ptr call_ret_t465;
  call_ret_t465 = cmsortL_i58(zs_v140982);
  return call_ret_t465;
}

tll_ptr get_at_i35(tll_ptr A_v140983, tll_ptr n_v140984, tll_ptr xs_v140985, tll_ptr a_v140986) {
  tll_ptr __v140988; tll_ptr __v140990; tll_ptr call_ret_t592;
  tll_ptr n_v140989; tll_ptr switch_ret_t589; tll_ptr switch_ret_t590;
  tll_ptr switch_ret_t591; tll_ptr x_v140987; tll_ptr xs_v140991;
  switch(((tll_node)n_v140984)->tag) {
    case 4:
      switch(((tll_node)xs_v140985)->tag) {
        case 18:
          switch_ret_t590 = a_v140986;
          break;
        case 19:
          x_v140987 = ((tll_node)xs_v140985)->data[0];
          __v140988 = ((tll_node)xs_v140985)->data[1];
          switch_ret_t590 = x_v140987;
          break;
      }
      switch_ret_t589 = switch_ret_t590;
      break;
    case 5:
      n_v140989 = ((tll_node)n_v140984)->data[0];
      switch(((tll_node)xs_v140985)->tag) {
        case 18:
          switch_ret_t591 = a_v140986;
          break;
        case 19:
          __v140990 = ((tll_node)xs_v140985)->data[0];
          xs_v140991 = ((tll_node)xs_v140985)->data[1];
          call_ret_t592 = get_at_i35(0, n_v140989, xs_v140991, a_v140986);
          switch_ret_t591 = call_ret_t592;
          break;
      }
      switch_ret_t589 = switch_ret_t591;
      break;
  }
  return switch_ret_t589;
}

tll_ptr lam_fun_t594(tll_ptr a_v141001, tll_env env) {
  tll_ptr call_ret_t593;
  call_ret_t593 = get_at_i35(env[2], env[1], env[0], a_v141001);
  return call_ret_t593;
}

tll_ptr lam_fun_t596(tll_ptr xs_v140999, tll_env env) {
  tll_ptr lam_clo_t595;
  instr_clo(&lam_clo_t595, &lam_fun_t594, 3, xs_v140999, env[0], env[1]);
  return lam_clo_t595;
}

tll_ptr lam_fun_t598(tll_ptr n_v140996, tll_env env) {
  tll_ptr lam_clo_t597;
  instr_clo(&lam_clo_t597, &lam_fun_t596, 2, n_v140996, env[0]);
  return lam_clo_t597;
}

tll_ptr lam_fun_t600(tll_ptr A_v140992, tll_env env) {
  tll_ptr lam_clo_t599;
  instr_clo(&lam_clo_t599, &lam_fun_t598, 1, A_v140992);
  return lam_clo_t599;
}

tll_ptr string_of_digit_i36(tll_ptr n_v141002) {
  tll_ptr EmptyString_t603; tll_ptr call_ret_t602;
  instr_struct(&EmptyString_t603, 7, 0);
  call_ret_t602 = get_at_i35(0, n_v141002, digits_i34, EmptyString_t603);
  return call_ret_t602;
}

tll_ptr lam_fun_t605(tll_ptr n_v141003, tll_env env) {
  tll_ptr call_ret_t604;
  call_ret_t604 = string_of_digit_i36(n_v141003);
  return call_ret_t604;
}

tll_ptr string_of_nat_i37(tll_ptr n_v141004) {
  tll_ptr O_t609; tll_ptr O_t621; tll_ptr O_t633; tll_ptr S_t610;
  tll_ptr S_t611; tll_ptr S_t612; tll_ptr S_t613; tll_ptr S_t614;
  tll_ptr S_t615; tll_ptr S_t616; tll_ptr S_t617; tll_ptr S_t618;
  tll_ptr S_t619; tll_ptr S_t622; tll_ptr S_t623; tll_ptr S_t624;
  tll_ptr S_t625; tll_ptr S_t626; tll_ptr S_t627; tll_ptr S_t628;
  tll_ptr S_t629; tll_ptr S_t630; tll_ptr S_t631; tll_ptr call_ret_t607;
  tll_ptr call_ret_t608; tll_ptr call_ret_t620; tll_ptr call_ret_t632;
  tll_ptr call_ret_t635; tll_ptr call_ret_t636; tll_ptr n_v141006;
  tll_ptr s_v141005; tll_ptr switch_ret_t634;
  instr_struct(&O_t609, 4, 0);
  instr_struct(&S_t610, 5, 1, O_t609);
  instr_struct(&S_t611, 5, 1, S_t610);
  instr_struct(&S_t612, 5, 1, S_t611);
  instr_struct(&S_t613, 5, 1, S_t612);
  instr_struct(&S_t614, 5, 1, S_t613);
  instr_struct(&S_t615, 5, 1, S_t614);
  instr_struct(&S_t616, 5, 1, S_t615);
  instr_struct(&S_t617, 5, 1, S_t616);
  instr_struct(&S_t618, 5, 1, S_t617);
  instr_struct(&S_t619, 5, 1, S_t618);
  call_ret_t608 = modn_i14(n_v141004, S_t619);
  call_ret_t607 = string_of_digit_i36(call_ret_t608);
  s_v141005 = call_ret_t607;
  instr_struct(&O_t621, 4, 0);
  instr_struct(&S_t622, 5, 1, O_t621);
  instr_struct(&S_t623, 5, 1, S_t622);
  instr_struct(&S_t624, 5, 1, S_t623);
  instr_struct(&S_t625, 5, 1, S_t624);
  instr_struct(&S_t626, 5, 1, S_t625);
  instr_struct(&S_t627, 5, 1, S_t626);
  instr_struct(&S_t628, 5, 1, S_t627);
  instr_struct(&S_t629, 5, 1, S_t628);
  instr_struct(&S_t630, 5, 1, S_t629);
  instr_struct(&S_t631, 5, 1, S_t630);
  call_ret_t620 = divn_i13(n_v141004, S_t631);
  n_v141006 = call_ret_t620;
  instr_struct(&O_t633, 4, 0);
  call_ret_t632 = ltn_i6(O_t633, n_v141006);
  switch(((tll_node)call_ret_t632)->tag) {
    case 2:
      call_ret_t636 = string_of_nat_i37(n_v141006);
      call_ret_t635 = cats_i15(call_ret_t636, s_v141005);
      switch_ret_t634 = call_ret_t635;
      break;
    case 3:
      switch_ret_t634 = s_v141005;
      break;
  }
  return switch_ret_t634;
}

tll_ptr lam_fun_t638(tll_ptr n_v141007, tll_env env) {
  tll_ptr call_ret_t637;
  call_ret_t637 = string_of_nat_i37(n_v141007);
  return call_ret_t637;
}

tll_ptr string_of_listU_i61(tll_ptr xs_v141008) {
  tll_ptr Ascii_t649; tll_ptr Ascii_t658; tll_ptr Ascii_t667;
  tll_ptr Ascii_t683; tll_ptr Ascii_t692; tll_ptr Ascii_t701;
  tll_ptr Ascii_t710; tll_ptr EmptyString_t668; tll_ptr EmptyString_t711;
  tll_ptr String_t669; tll_ptr String_t670; tll_ptr String_t671;
  tll_ptr String_t712; tll_ptr String_t713; tll_ptr String_t714;
  tll_ptr String_t715; tll_ptr call_ret_t672; tll_ptr call_ret_t673;
  tll_ptr call_ret_t674; tll_ptr call_ret_t716; tll_ptr false_t641;
  tll_ptr false_t644; tll_ptr false_t648; tll_ptr false_t650;
  tll_ptr false_t653; tll_ptr false_t655; tll_ptr false_t656;
  tll_ptr false_t659; tll_ptr false_t662; tll_ptr false_t665;
  tll_ptr false_t666; tll_ptr false_t675; tll_ptr false_t676;
  tll_ptr false_t678; tll_ptr false_t679; tll_ptr false_t680;
  tll_ptr false_t681; tll_ptr false_t682; tll_ptr false_t684;
  tll_ptr false_t685; tll_ptr false_t689; tll_ptr false_t691;
  tll_ptr false_t693; tll_ptr false_t694; tll_ptr false_t698;
  tll_ptr false_t700; tll_ptr false_t702; tll_ptr false_t703;
  tll_ptr false_t705; tll_ptr false_t706; tll_ptr false_t707;
  tll_ptr false_t708; tll_ptr false_t709; tll_ptr switch_ret_t640;
  tll_ptr true_t642; tll_ptr true_t643; tll_ptr true_t645; tll_ptr true_t646;
  tll_ptr true_t647; tll_ptr true_t651; tll_ptr true_t652; tll_ptr true_t654;
  tll_ptr true_t657; tll_ptr true_t660; tll_ptr true_t661; tll_ptr true_t663;
  tll_ptr true_t664; tll_ptr true_t677; tll_ptr true_t686; tll_ptr true_t687;
  tll_ptr true_t688; tll_ptr true_t690; tll_ptr true_t695; tll_ptr true_t696;
  tll_ptr true_t697; tll_ptr true_t699; tll_ptr true_t704; tll_ptr x_v141009;
  tll_ptr xs_v141010;
  switch(((tll_node)xs_v141008)->tag) {
    case 18:
      instr_struct(&false_t641, 3, 0);
      instr_struct(&true_t642, 2, 0);
      instr_struct(&true_t643, 2, 0);
      instr_struct(&false_t644, 3, 0);
      instr_struct(&true_t645, 2, 0);
      instr_struct(&true_t646, 2, 0);
      instr_struct(&true_t647, 2, 0);
      instr_struct(&false_t648, 3, 0);
      instr_struct(&Ascii_t649, 6, 8,
                   false_t641, true_t642, true_t643, false_t644, true_t645,
                   true_t646, true_t647, false_t648);
      instr_struct(&false_t650, 3, 0);
      instr_struct(&true_t651, 2, 0);
      instr_struct(&true_t652, 2, 0);
      instr_struct(&false_t653, 3, 0);
      instr_struct(&true_t654, 2, 0);
      instr_struct(&false_t655, 3, 0);
      instr_struct(&false_t656, 3, 0);
      instr_struct(&true_t657, 2, 0);
      instr_struct(&Ascii_t658, 6, 8,
                   false_t650, true_t651, true_t652, false_t653, true_t654,
                   false_t655, false_t656, true_t657);
      instr_struct(&false_t659, 3, 0);
      instr_struct(&true_t660, 2, 0);
      instr_struct(&true_t661, 2, 0);
      instr_struct(&false_t662, 3, 0);
      instr_struct(&true_t663, 2, 0);
      instr_struct(&true_t664, 2, 0);
      instr_struct(&false_t665, 3, 0);
      instr_struct(&false_t666, 3, 0);
      instr_struct(&Ascii_t667, 6, 8,
                   false_t659, true_t660, true_t661, false_t662, true_t663,
                   true_t664, false_t665, false_t666);
      instr_struct(&EmptyString_t668, 7, 0);
      instr_struct(&String_t669, 8, 2, Ascii_t667, EmptyString_t668);
      instr_struct(&String_t670, 8, 2, Ascii_t658, String_t669);
      instr_struct(&String_t671, 8, 2, Ascii_t649, String_t670);
      switch_ret_t640 = String_t671;
      break;
    case 19:
      x_v141009 = ((tll_node)xs_v141008)->data[0];
      xs_v141010 = ((tll_node)xs_v141008)->data[1];
      call_ret_t674 = string_of_nat_i37(x_v141009);
      instr_struct(&false_t675, 3, 0);
      instr_struct(&false_t676, 3, 0);
      instr_struct(&true_t677, 2, 0);
      instr_struct(&false_t678, 3, 0);
      instr_struct(&false_t679, 3, 0);
      instr_struct(&false_t680, 3, 0);
      instr_struct(&false_t681, 3, 0);
      instr_struct(&false_t682, 3, 0);
      instr_struct(&Ascii_t683, 6, 8,
                   false_t675, false_t676, true_t677, false_t678, false_t679,
                   false_t680, false_t681, false_t682);
      instr_struct(&false_t684, 3, 0);
      instr_struct(&false_t685, 3, 0);
      instr_struct(&true_t686, 2, 0);
      instr_struct(&true_t687, 2, 0);
      instr_struct(&true_t688, 2, 0);
      instr_struct(&false_t689, 3, 0);
      instr_struct(&true_t690, 2, 0);
      instr_struct(&false_t691, 3, 0);
      instr_struct(&Ascii_t692, 6, 8,
                   false_t684, false_t685, true_t686, true_t687, true_t688,
                   false_t689, true_t690, false_t691);
      instr_struct(&false_t693, 3, 0);
      instr_struct(&false_t694, 3, 0);
      instr_struct(&true_t695, 2, 0);
      instr_struct(&true_t696, 2, 0);
      instr_struct(&true_t697, 2, 0);
      instr_struct(&false_t698, 3, 0);
      instr_struct(&true_t699, 2, 0);
      instr_struct(&false_t700, 3, 0);
      instr_struct(&Ascii_t701, 6, 8,
                   false_t693, false_t694, true_t695, true_t696, true_t697,
                   false_t698, true_t699, false_t700);
      instr_struct(&false_t702, 3, 0);
      instr_struct(&false_t703, 3, 0);
      instr_struct(&true_t704, 2, 0);
      instr_struct(&false_t705, 3, 0);
      instr_struct(&false_t706, 3, 0);
      instr_struct(&false_t707, 3, 0);
      instr_struct(&false_t708, 3, 0);
      instr_struct(&false_t709, 3, 0);
      instr_struct(&Ascii_t710, 6, 8,
                   false_t702, false_t703, true_t704, false_t705, false_t706,
                   false_t707, false_t708, false_t709);
      instr_struct(&EmptyString_t711, 7, 0);
      instr_struct(&String_t712, 8, 2, Ascii_t710, EmptyString_t711);
      instr_struct(&String_t713, 8, 2, Ascii_t701, String_t712);
      instr_struct(&String_t714, 8, 2, Ascii_t692, String_t713);
      instr_struct(&String_t715, 8, 2, Ascii_t683, String_t714);
      call_ret_t673 = cats_i15(call_ret_t674, String_t715);
      call_ret_t716 = string_of_listU_i61(xs_v141010);
      call_ret_t672 = cats_i15(call_ret_t673, call_ret_t716);
      switch_ret_t640 = call_ret_t672;
      break;
  }
  return switch_ret_t640;
}

tll_ptr lam_fun_t718(tll_ptr xs_v141011, tll_env env) {
  tll_ptr call_ret_t717;
  call_ret_t717 = string_of_listU_i61(xs_v141011);
  return call_ret_t717;
}

tll_ptr string_of_listL_i60(tll_ptr xs_v141012) {
  tll_ptr Ascii_t729; tll_ptr Ascii_t738; tll_ptr Ascii_t747;
  tll_ptr Ascii_t763; tll_ptr Ascii_t772; tll_ptr Ascii_t781;
  tll_ptr Ascii_t790; tll_ptr EmptyString_t748; tll_ptr EmptyString_t791;
  tll_ptr String_t749; tll_ptr String_t750; tll_ptr String_t751;
  tll_ptr String_t792; tll_ptr String_t793; tll_ptr String_t794;
  tll_ptr String_t795; tll_ptr call_ret_t752; tll_ptr call_ret_t753;
  tll_ptr call_ret_t754; tll_ptr call_ret_t796; tll_ptr false_t721;
  tll_ptr false_t724; tll_ptr false_t728; tll_ptr false_t730;
  tll_ptr false_t733; tll_ptr false_t735; tll_ptr false_t736;
  tll_ptr false_t739; tll_ptr false_t742; tll_ptr false_t745;
  tll_ptr false_t746; tll_ptr false_t755; tll_ptr false_t756;
  tll_ptr false_t758; tll_ptr false_t759; tll_ptr false_t760;
  tll_ptr false_t761; tll_ptr false_t762; tll_ptr false_t764;
  tll_ptr false_t765; tll_ptr false_t769; tll_ptr false_t771;
  tll_ptr false_t773; tll_ptr false_t774; tll_ptr false_t778;
  tll_ptr false_t780; tll_ptr false_t782; tll_ptr false_t783;
  tll_ptr false_t785; tll_ptr false_t786; tll_ptr false_t787;
  tll_ptr false_t788; tll_ptr false_t789; tll_ptr switch_ret_t720;
  tll_ptr true_t722; tll_ptr true_t723; tll_ptr true_t725; tll_ptr true_t726;
  tll_ptr true_t727; tll_ptr true_t731; tll_ptr true_t732; tll_ptr true_t734;
  tll_ptr true_t737; tll_ptr true_t740; tll_ptr true_t741; tll_ptr true_t743;
  tll_ptr true_t744; tll_ptr true_t757; tll_ptr true_t766; tll_ptr true_t767;
  tll_ptr true_t768; tll_ptr true_t770; tll_ptr true_t775; tll_ptr true_t776;
  tll_ptr true_t777; tll_ptr true_t779; tll_ptr true_t784; tll_ptr x_v141013;
  tll_ptr xs_v141014;
  switch(((tll_node)xs_v141012)->tag) {
    case 16:
      instr_free_struct(xs_v141012);
      instr_struct(&false_t721, 3, 0);
      instr_struct(&true_t722, 2, 0);
      instr_struct(&true_t723, 2, 0);
      instr_struct(&false_t724, 3, 0);
      instr_struct(&true_t725, 2, 0);
      instr_struct(&true_t726, 2, 0);
      instr_struct(&true_t727, 2, 0);
      instr_struct(&false_t728, 3, 0);
      instr_struct(&Ascii_t729, 6, 8,
                   false_t721, true_t722, true_t723, false_t724, true_t725,
                   true_t726, true_t727, false_t728);
      instr_struct(&false_t730, 3, 0);
      instr_struct(&true_t731, 2, 0);
      instr_struct(&true_t732, 2, 0);
      instr_struct(&false_t733, 3, 0);
      instr_struct(&true_t734, 2, 0);
      instr_struct(&false_t735, 3, 0);
      instr_struct(&false_t736, 3, 0);
      instr_struct(&true_t737, 2, 0);
      instr_struct(&Ascii_t738, 6, 8,
                   false_t730, true_t731, true_t732, false_t733, true_t734,
                   false_t735, false_t736, true_t737);
      instr_struct(&false_t739, 3, 0);
      instr_struct(&true_t740, 2, 0);
      instr_struct(&true_t741, 2, 0);
      instr_struct(&false_t742, 3, 0);
      instr_struct(&true_t743, 2, 0);
      instr_struct(&true_t744, 2, 0);
      instr_struct(&false_t745, 3, 0);
      instr_struct(&false_t746, 3, 0);
      instr_struct(&Ascii_t747, 6, 8,
                   false_t739, true_t740, true_t741, false_t742, true_t743,
                   true_t744, false_t745, false_t746);
      instr_struct(&EmptyString_t748, 7, 0);
      instr_struct(&String_t749, 8, 2, Ascii_t747, EmptyString_t748);
      instr_struct(&String_t750, 8, 2, Ascii_t738, String_t749);
      instr_struct(&String_t751, 8, 2, Ascii_t729, String_t750);
      switch_ret_t720 = String_t751;
      break;
    case 17:
      x_v141013 = ((tll_node)xs_v141012)->data[0];
      xs_v141014 = ((tll_node)xs_v141012)->data[1];
      instr_free_struct(xs_v141012);
      call_ret_t754 = string_of_nat_i37(x_v141013);
      instr_struct(&false_t755, 3, 0);
      instr_struct(&false_t756, 3, 0);
      instr_struct(&true_t757, 2, 0);
      instr_struct(&false_t758, 3, 0);
      instr_struct(&false_t759, 3, 0);
      instr_struct(&false_t760, 3, 0);
      instr_struct(&false_t761, 3, 0);
      instr_struct(&false_t762, 3, 0);
      instr_struct(&Ascii_t763, 6, 8,
                   false_t755, false_t756, true_t757, false_t758, false_t759,
                   false_t760, false_t761, false_t762);
      instr_struct(&false_t764, 3, 0);
      instr_struct(&false_t765, 3, 0);
      instr_struct(&true_t766, 2, 0);
      instr_struct(&true_t767, 2, 0);
      instr_struct(&true_t768, 2, 0);
      instr_struct(&false_t769, 3, 0);
      instr_struct(&true_t770, 2, 0);
      instr_struct(&false_t771, 3, 0);
      instr_struct(&Ascii_t772, 6, 8,
                   false_t764, false_t765, true_t766, true_t767, true_t768,
                   false_t769, true_t770, false_t771);
      instr_struct(&false_t773, 3, 0);
      instr_struct(&false_t774, 3, 0);
      instr_struct(&true_t775, 2, 0);
      instr_struct(&true_t776, 2, 0);
      instr_struct(&true_t777, 2, 0);
      instr_struct(&false_t778, 3, 0);
      instr_struct(&true_t779, 2, 0);
      instr_struct(&false_t780, 3, 0);
      instr_struct(&Ascii_t781, 6, 8,
                   false_t773, false_t774, true_t775, true_t776, true_t777,
                   false_t778, true_t779, false_t780);
      instr_struct(&false_t782, 3, 0);
      instr_struct(&false_t783, 3, 0);
      instr_struct(&true_t784, 2, 0);
      instr_struct(&false_t785, 3, 0);
      instr_struct(&false_t786, 3, 0);
      instr_struct(&false_t787, 3, 0);
      instr_struct(&false_t788, 3, 0);
      instr_struct(&false_t789, 3, 0);
      instr_struct(&Ascii_t790, 6, 8,
                   false_t782, false_t783, true_t784, false_t785, false_t786,
                   false_t787, false_t788, false_t789);
      instr_struct(&EmptyString_t791, 7, 0);
      instr_struct(&String_t792, 8, 2, Ascii_t790, EmptyString_t791);
      instr_struct(&String_t793, 8, 2, Ascii_t781, String_t792);
      instr_struct(&String_t794, 8, 2, Ascii_t772, String_t793);
      instr_struct(&String_t795, 8, 2, Ascii_t763, String_t794);
      call_ret_t753 = cats_i15(call_ret_t754, String_t795);
      call_ret_t796 = string_of_listL_i60(xs_v141014);
      call_ret_t752 = cats_i15(call_ret_t753, call_ret_t796);
      switch_ret_t720 = call_ret_t752;
      break;
  }
  return switch_ret_t720;
}

tll_ptr lam_fun_t798(tll_ptr xs_v141015, tll_env env) {
  tll_ptr call_ret_t797;
  call_ret_t797 = string_of_listL_i60(xs_v141015);
  return call_ret_t797;
}

int main() {
  instr_init();
  tll_ptr Ascii_t476; tll_ptr Ascii_t487; tll_ptr Ascii_t498;
  tll_ptr Ascii_t509; tll_ptr Ascii_t520; tll_ptr Ascii_t531;
  tll_ptr Ascii_t542; tll_ptr Ascii_t553; tll_ptr Ascii_t564;
  tll_ptr Ascii_t575; tll_ptr Ascii_t889; tll_ptr Ascii_t904;
  tll_ptr EmptyString_t477; tll_ptr EmptyString_t488;
  tll_ptr EmptyString_t499; tll_ptr EmptyString_t510;
  tll_ptr EmptyString_t521; tll_ptr EmptyString_t532;
  tll_ptr EmptyString_t543; tll_ptr EmptyString_t554;
  tll_ptr EmptyString_t565; tll_ptr EmptyString_t576;
  tll_ptr EmptyString_t890; tll_ptr EmptyString_t905; tll_ptr O_t800;
  tll_ptr O_t806; tll_ptr O_t809; tll_ptr O_t811; tll_ptr O_t818;
  tll_ptr O_t823; tll_ptr O_t824; tll_ptr O_t836; tll_ptr O_t840;
  tll_ptr O_t841; tll_ptr O_t848; tll_ptr O_t850; tll_ptr O_t855;
  tll_ptr O_t858; tll_ptr S_t801; tll_ptr S_t802; tll_ptr S_t803;
  tll_ptr S_t804; tll_ptr S_t805; tll_ptr S_t807; tll_ptr S_t808;
  tll_ptr S_t810; tll_ptr S_t812; tll_ptr S_t813; tll_ptr S_t814;
  tll_ptr S_t815; tll_ptr S_t816; tll_ptr S_t817; tll_ptr S_t819;
  tll_ptr S_t820; tll_ptr S_t821; tll_ptr S_t822; tll_ptr S_t825;
  tll_ptr S_t826; tll_ptr S_t827; tll_ptr S_t837; tll_ptr S_t838;
  tll_ptr S_t839; tll_ptr S_t842; tll_ptr S_t843; tll_ptr S_t844;
  tll_ptr S_t845; tll_ptr S_t846; tll_ptr S_t847; tll_ptr S_t849;
  tll_ptr S_t851; tll_ptr S_t852; tll_ptr S_t853; tll_ptr S_t854;
  tll_ptr S_t856; tll_ptr S_t857; tll_ptr S_t859; tll_ptr S_t860;
  tll_ptr S_t861; tll_ptr S_t862; tll_ptr S_t863; tll_ptr String_t478;
  tll_ptr String_t489; tll_ptr String_t500; tll_ptr String_t511;
  tll_ptr String_t522; tll_ptr String_t533; tll_ptr String_t544;
  tll_ptr String_t555; tll_ptr String_t566; tll_ptr String_t577;
  tll_ptr String_t891; tll_ptr String_t906; tll_ptr __v141021;
  tll_ptr __v141023; tll_ptr __v141024; tll_ptr app_ret_t873;
  tll_ptr app_ret_t875; tll_ptr app_ret_t892; tll_ptr app_ret_t907;
  tll_ptr call_ret_t872; tll_ptr call_ret_t874; tll_ptr call_ret_t878;
  tll_ptr call_ret_t879; tll_ptr call_ret_t880; tll_ptr call_ret_t893;
  tll_ptr call_ret_t894; tll_ptr call_ret_t895; tll_ptr consUL_t865;
  tll_ptr consUL_t866; tll_ptr consUL_t867; tll_ptr consUL_t868;
  tll_ptr consUL_t869; tll_ptr consUL_t870; tll_ptr consUL_t871;
  tll_ptr consUU_t579; tll_ptr consUU_t580; tll_ptr consUU_t581;
  tll_ptr consUU_t582; tll_ptr consUU_t583; tll_ptr consUU_t584;
  tll_ptr consUU_t585; tll_ptr consUU_t586; tll_ptr consUU_t587;
  tll_ptr consUU_t588; tll_ptr consUU_t829; tll_ptr consUU_t830;
  tll_ptr consUU_t831; tll_ptr consUU_t832; tll_ptr consUU_t833;
  tll_ptr consUU_t834; tll_ptr consUU_t835; tll_ptr false_t468;
  tll_ptr false_t469; tll_ptr false_t472; tll_ptr false_t473;
  tll_ptr false_t474; tll_ptr false_t475; tll_ptr false_t479;
  tll_ptr false_t480; tll_ptr false_t483; tll_ptr false_t484;
  tll_ptr false_t485; tll_ptr false_t490; tll_ptr false_t491;
  tll_ptr false_t494; tll_ptr false_t495; tll_ptr false_t497;
  tll_ptr false_t501; tll_ptr false_t502; tll_ptr false_t505;
  tll_ptr false_t506; tll_ptr false_t512; tll_ptr false_t513;
  tll_ptr false_t516; tll_ptr false_t518; tll_ptr false_t519;
  tll_ptr false_t523; tll_ptr false_t524; tll_ptr false_t527;
  tll_ptr false_t529; tll_ptr false_t534; tll_ptr false_t535;
  tll_ptr false_t538; tll_ptr false_t541; tll_ptr false_t545;
  tll_ptr false_t546; tll_ptr false_t549; tll_ptr false_t556;
  tll_ptr false_t557; tll_ptr false_t561; tll_ptr false_t562;
  tll_ptr false_t563; tll_ptr false_t567; tll_ptr false_t568;
  tll_ptr false_t572; tll_ptr false_t573; tll_ptr false_t881;
  tll_ptr false_t882; tll_ptr false_t883; tll_ptr false_t884;
  tll_ptr false_t886; tll_ptr false_t888; tll_ptr false_t896;
  tll_ptr false_t897; tll_ptr false_t898; tll_ptr false_t899;
  tll_ptr false_t901; tll_ptr false_t903; tll_ptr lam_clo_t106;
  tll_ptr lam_clo_t117; tll_ptr lam_clo_t125; tll_ptr lam_clo_t133;
  tll_ptr lam_clo_t14; tll_ptr lam_clo_t140; tll_ptr lam_clo_t154;
  tll_ptr lam_clo_t168; tll_ptr lam_clo_t182; tll_ptr lam_clo_t192;
  tll_ptr lam_clo_t20; tll_ptr lam_clo_t202; tll_ptr lam_clo_t212;
  tll_ptr lam_clo_t225; tll_ptr lam_clo_t237; tll_ptr lam_clo_t249;
  tll_ptr lam_clo_t266; tll_ptr lam_clo_t283; tll_ptr lam_clo_t299;
  tll_ptr lam_clo_t30; tll_ptr lam_clo_t315; tll_ptr lam_clo_t330;
  tll_ptr lam_clo_t345; tll_ptr lam_clo_t393; tll_ptr lam_clo_t42;
  tll_ptr lam_clo_t441; tll_ptr lam_clo_t454; tll_ptr lam_clo_t467;
  tll_ptr lam_clo_t54; tll_ptr lam_clo_t601; tll_ptr lam_clo_t606;
  tll_ptr lam_clo_t639; tll_ptr lam_clo_t64; tll_ptr lam_clo_t7;
  tll_ptr lam_clo_t719; tll_ptr lam_clo_t76; tll_ptr lam_clo_t799;
  tll_ptr lam_clo_t81; tll_ptr lam_clo_t89; tll_ptr lam_clo_t97;
  tll_ptr msg1_v141018; tll_ptr msg2_v141019; tll_ptr nilUL_t864;
  tll_ptr nilUU_t578; tll_ptr nilUU_t828; tll_ptr sorted1_v141020;
  tll_ptr sorted2_v141022; tll_ptr switch_ret_t876; tll_ptr switch_ret_t877;
  tll_ptr test1_v141016; tll_ptr test2_v141017; tll_ptr true_t470;
  tll_ptr true_t471; tll_ptr true_t481; tll_ptr true_t482; tll_ptr true_t486;
  tll_ptr true_t492; tll_ptr true_t493; tll_ptr true_t496; tll_ptr true_t503;
  tll_ptr true_t504; tll_ptr true_t507; tll_ptr true_t508; tll_ptr true_t514;
  tll_ptr true_t515; tll_ptr true_t517; tll_ptr true_t525; tll_ptr true_t526;
  tll_ptr true_t528; tll_ptr true_t530; tll_ptr true_t536; tll_ptr true_t537;
  tll_ptr true_t539; tll_ptr true_t540; tll_ptr true_t547; tll_ptr true_t548;
  tll_ptr true_t550; tll_ptr true_t551; tll_ptr true_t552; tll_ptr true_t558;
  tll_ptr true_t559; tll_ptr true_t560; tll_ptr true_t569; tll_ptr true_t570;
  tll_ptr true_t571; tll_ptr true_t574; tll_ptr true_t885; tll_ptr true_t887;
  tll_ptr true_t900; tll_ptr true_t902;
  instr_clo(&lam_clo_t7, &lam_fun_t6, 0);
  andbclo_i62 = lam_clo_t7;
  instr_clo(&lam_clo_t14, &lam_fun_t13, 0);
  orbclo_i63 = lam_clo_t14;
  instr_clo(&lam_clo_t20, &lam_fun_t19, 0);
  notbclo_i64 = lam_clo_t20;
  instr_clo(&lam_clo_t30, &lam_fun_t29, 0);
  ltenclo_i65 = lam_clo_t30;
  instr_clo(&lam_clo_t42, &lam_fun_t41, 0);
  gtenclo_i66 = lam_clo_t42;
  instr_clo(&lam_clo_t54, &lam_fun_t53, 0);
  ltnclo_i67 = lam_clo_t54;
  instr_clo(&lam_clo_t64, &lam_fun_t63, 0);
  gtnclo_i68 = lam_clo_t64;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 0);
  eqnclo_i69 = lam_clo_t76;
  instr_clo(&lam_clo_t81, &lam_fun_t80, 0);
  predclo_i70 = lam_clo_t81;
  instr_clo(&lam_clo_t89, &lam_fun_t88, 0);
  addnclo_i71 = lam_clo_t89;
  instr_clo(&lam_clo_t97, &lam_fun_t96, 0);
  subnclo_i72 = lam_clo_t97;
  instr_clo(&lam_clo_t106, &lam_fun_t105, 0);
  mulnclo_i73 = lam_clo_t106;
  instr_clo(&lam_clo_t117, &lam_fun_t116, 0);
  divnclo_i74 = lam_clo_t117;
  instr_clo(&lam_clo_t125, &lam_fun_t124, 0);
  modnclo_i75 = lam_clo_t125;
  instr_clo(&lam_clo_t133, &lam_fun_t132, 0);
  catsclo_i76 = lam_clo_t133;
  instr_clo(&lam_clo_t140, &lam_fun_t139, 0);
  strlenclo_i77 = lam_clo_t140;
  instr_clo(&lam_clo_t154, &lam_fun_t153, 0);
  lenUUclo_i78 = lam_clo_t154;
  instr_clo(&lam_clo_t168, &lam_fun_t167, 0);
  lenULclo_i79 = lam_clo_t168;
  instr_clo(&lam_clo_t182, &lam_fun_t181, 0);
  lenLLclo_i80 = lam_clo_t182;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 0);
  appendUUclo_i81 = lam_clo_t192;
  instr_clo(&lam_clo_t202, &lam_fun_t201, 0);
  appendULclo_i82 = lam_clo_t202;
  instr_clo(&lam_clo_t212, &lam_fun_t211, 0);
  appendLLclo_i83 = lam_clo_t212;
  instr_clo(&lam_clo_t225, &lam_fun_t224, 0);
  readlineclo_i84 = lam_clo_t225;
  instr_clo(&lam_clo_t237, &lam_fun_t236, 0);
  printclo_i85 = lam_clo_t237;
  instr_clo(&lam_clo_t249, &lam_fun_t248, 0);
  prerrclo_i86 = lam_clo_t249;
  instr_clo(&lam_clo_t266, &lam_fun_t265, 0);
  splitUclo_i87 = lam_clo_t266;
  instr_clo(&lam_clo_t283, &lam_fun_t282, 0);
  splitLclo_i88 = lam_clo_t283;
  instr_clo(&lam_clo_t299, &lam_fun_t298, 0);
  mergeUclo_i89 = lam_clo_t299;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 0);
  mergeLclo_i90 = lam_clo_t315;
  instr_clo(&lam_clo_t330, &lam_fun_t329, 0);
  msortUclo_i91 = lam_clo_t330;
  instr_clo(&lam_clo_t345, &lam_fun_t344, 0);
  msortLclo_i92 = lam_clo_t345;
  instr_clo(&lam_clo_t393, &lam_fun_t392, 0);
  cmsort_workerUclo_i93 = lam_clo_t393;
  instr_clo(&lam_clo_t441, &lam_fun_t440, 0);
  cmsort_workerLclo_i94 = lam_clo_t441;
  instr_clo(&lam_clo_t454, &lam_fun_t453, 0);
  cmsortUclo_i95 = lam_clo_t454;
  instr_clo(&lam_clo_t467, &lam_fun_t466, 0);
  cmsortLclo_i96 = lam_clo_t467;
  instr_struct(&false_t468, 3, 0);
  instr_struct(&false_t469, 3, 0);
  instr_struct(&true_t470, 2, 0);
  instr_struct(&true_t471, 2, 0);
  instr_struct(&false_t472, 3, 0);
  instr_struct(&false_t473, 3, 0);
  instr_struct(&false_t474, 3, 0);
  instr_struct(&false_t475, 3, 0);
  instr_struct(&Ascii_t476, 6, 8,
               false_t468, false_t469, true_t470, true_t471, false_t472,
               false_t473, false_t474, false_t475);
  instr_struct(&EmptyString_t477, 7, 0);
  instr_struct(&String_t478, 8, 2, Ascii_t476, EmptyString_t477);
  instr_struct(&false_t479, 3, 0);
  instr_struct(&false_t480, 3, 0);
  instr_struct(&true_t481, 2, 0);
  instr_struct(&true_t482, 2, 0);
  instr_struct(&false_t483, 3, 0);
  instr_struct(&false_t484, 3, 0);
  instr_struct(&false_t485, 3, 0);
  instr_struct(&true_t486, 2, 0);
  instr_struct(&Ascii_t487, 6, 8,
               false_t479, false_t480, true_t481, true_t482, false_t483,
               false_t484, false_t485, true_t486);
  instr_struct(&EmptyString_t488, 7, 0);
  instr_struct(&String_t489, 8, 2, Ascii_t487, EmptyString_t488);
  instr_struct(&false_t490, 3, 0);
  instr_struct(&false_t491, 3, 0);
  instr_struct(&true_t492, 2, 0);
  instr_struct(&true_t493, 2, 0);
  instr_struct(&false_t494, 3, 0);
  instr_struct(&false_t495, 3, 0);
  instr_struct(&true_t496, 2, 0);
  instr_struct(&false_t497, 3, 0);
  instr_struct(&Ascii_t498, 6, 8,
               false_t490, false_t491, true_t492, true_t493, false_t494,
               false_t495, true_t496, false_t497);
  instr_struct(&EmptyString_t499, 7, 0);
  instr_struct(&String_t500, 8, 2, Ascii_t498, EmptyString_t499);
  instr_struct(&false_t501, 3, 0);
  instr_struct(&false_t502, 3, 0);
  instr_struct(&true_t503, 2, 0);
  instr_struct(&true_t504, 2, 0);
  instr_struct(&false_t505, 3, 0);
  instr_struct(&false_t506, 3, 0);
  instr_struct(&true_t507, 2, 0);
  instr_struct(&true_t508, 2, 0);
  instr_struct(&Ascii_t509, 6, 8,
               false_t501, false_t502, true_t503, true_t504, false_t505,
               false_t506, true_t507, true_t508);
  instr_struct(&EmptyString_t510, 7, 0);
  instr_struct(&String_t511, 8, 2, Ascii_t509, EmptyString_t510);
  instr_struct(&false_t512, 3, 0);
  instr_struct(&false_t513, 3, 0);
  instr_struct(&true_t514, 2, 0);
  instr_struct(&true_t515, 2, 0);
  instr_struct(&false_t516, 3, 0);
  instr_struct(&true_t517, 2, 0);
  instr_struct(&false_t518, 3, 0);
  instr_struct(&false_t519, 3, 0);
  instr_struct(&Ascii_t520, 6, 8,
               false_t512, false_t513, true_t514, true_t515, false_t516,
               true_t517, false_t518, false_t519);
  instr_struct(&EmptyString_t521, 7, 0);
  instr_struct(&String_t522, 8, 2, Ascii_t520, EmptyString_t521);
  instr_struct(&false_t523, 3, 0);
  instr_struct(&false_t524, 3, 0);
  instr_struct(&true_t525, 2, 0);
  instr_struct(&true_t526, 2, 0);
  instr_struct(&false_t527, 3, 0);
  instr_struct(&true_t528, 2, 0);
  instr_struct(&false_t529, 3, 0);
  instr_struct(&true_t530, 2, 0);
  instr_struct(&Ascii_t531, 6, 8,
               false_t523, false_t524, true_t525, true_t526, false_t527,
               true_t528, false_t529, true_t530);
  instr_struct(&EmptyString_t532, 7, 0);
  instr_struct(&String_t533, 8, 2, Ascii_t531, EmptyString_t532);
  instr_struct(&false_t534, 3, 0);
  instr_struct(&false_t535, 3, 0);
  instr_struct(&true_t536, 2, 0);
  instr_struct(&true_t537, 2, 0);
  instr_struct(&false_t538, 3, 0);
  instr_struct(&true_t539, 2, 0);
  instr_struct(&true_t540, 2, 0);
  instr_struct(&false_t541, 3, 0);
  instr_struct(&Ascii_t542, 6, 8,
               false_t534, false_t535, true_t536, true_t537, false_t538,
               true_t539, true_t540, false_t541);
  instr_struct(&EmptyString_t543, 7, 0);
  instr_struct(&String_t544, 8, 2, Ascii_t542, EmptyString_t543);
  instr_struct(&false_t545, 3, 0);
  instr_struct(&false_t546, 3, 0);
  instr_struct(&true_t547, 2, 0);
  instr_struct(&true_t548, 2, 0);
  instr_struct(&false_t549, 3, 0);
  instr_struct(&true_t550, 2, 0);
  instr_struct(&true_t551, 2, 0);
  instr_struct(&true_t552, 2, 0);
  instr_struct(&Ascii_t553, 6, 8,
               false_t545, false_t546, true_t547, true_t548, false_t549,
               true_t550, true_t551, true_t552);
  instr_struct(&EmptyString_t554, 7, 0);
  instr_struct(&String_t555, 8, 2, Ascii_t553, EmptyString_t554);
  instr_struct(&false_t556, 3, 0);
  instr_struct(&false_t557, 3, 0);
  instr_struct(&true_t558, 2, 0);
  instr_struct(&true_t559, 2, 0);
  instr_struct(&true_t560, 2, 0);
  instr_struct(&false_t561, 3, 0);
  instr_struct(&false_t562, 3, 0);
  instr_struct(&false_t563, 3, 0);
  instr_struct(&Ascii_t564, 6, 8,
               false_t556, false_t557, true_t558, true_t559, true_t560,
               false_t561, false_t562, false_t563);
  instr_struct(&EmptyString_t565, 7, 0);
  instr_struct(&String_t566, 8, 2, Ascii_t564, EmptyString_t565);
  instr_struct(&false_t567, 3, 0);
  instr_struct(&false_t568, 3, 0);
  instr_struct(&true_t569, 2, 0);
  instr_struct(&true_t570, 2, 0);
  instr_struct(&true_t571, 2, 0);
  instr_struct(&false_t572, 3, 0);
  instr_struct(&false_t573, 3, 0);
  instr_struct(&true_t574, 2, 0);
  instr_struct(&Ascii_t575, 6, 8,
               false_t567, false_t568, true_t569, true_t570, true_t571,
               false_t572, false_t573, true_t574);
  instr_struct(&EmptyString_t576, 7, 0);
  instr_struct(&String_t577, 8, 2, Ascii_t575, EmptyString_t576);
  instr_struct(&nilUU_t578, 18, 0);
  instr_struct(&consUU_t579, 19, 2, String_t577, nilUU_t578);
  instr_struct(&consUU_t580, 19, 2, String_t566, consUU_t579);
  instr_struct(&consUU_t581, 19, 2, String_t555, consUU_t580);
  instr_struct(&consUU_t582, 19, 2, String_t544, consUU_t581);
  instr_struct(&consUU_t583, 19, 2, String_t533, consUU_t582);
  instr_struct(&consUU_t584, 19, 2, String_t522, consUU_t583);
  instr_struct(&consUU_t585, 19, 2, String_t511, consUU_t584);
  instr_struct(&consUU_t586, 19, 2, String_t500, consUU_t585);
  instr_struct(&consUU_t587, 19, 2, String_t489, consUU_t586);
  instr_struct(&consUU_t588, 19, 2, String_t478, consUU_t587);
  digits_i34 = consUU_t588;
  instr_clo(&lam_clo_t601, &lam_fun_t600, 0);
  get_atclo_i97 = lam_clo_t601;
  instr_clo(&lam_clo_t606, &lam_fun_t605, 0);
  string_of_digitclo_i98 = lam_clo_t606;
  instr_clo(&lam_clo_t639, &lam_fun_t638, 0);
  string_of_natclo_i99 = lam_clo_t639;
  instr_clo(&lam_clo_t719, &lam_fun_t718, 0);
  string_of_listUclo_i100 = lam_clo_t719;
  instr_clo(&lam_clo_t799, &lam_fun_t798, 0);
  string_of_listLclo_i101 = lam_clo_t799;
  instr_struct(&O_t800, 4, 0);
  instr_struct(&S_t801, 5, 1, O_t800);
  instr_struct(&S_t802, 5, 1, S_t801);
  instr_struct(&S_t803, 5, 1, S_t802);
  instr_struct(&S_t804, 5, 1, S_t803);
  instr_struct(&S_t805, 5, 1, S_t804);
  instr_struct(&O_t806, 4, 0);
  instr_struct(&S_t807, 5, 1, O_t806);
  instr_struct(&S_t808, 5, 1, S_t807);
  instr_struct(&O_t809, 4, 0);
  instr_struct(&S_t810, 5, 1, O_t809);
  instr_struct(&O_t811, 4, 0);
  instr_struct(&S_t812, 5, 1, O_t811);
  instr_struct(&S_t813, 5, 1, S_t812);
  instr_struct(&S_t814, 5, 1, S_t813);
  instr_struct(&S_t815, 5, 1, S_t814);
  instr_struct(&S_t816, 5, 1, S_t815);
  instr_struct(&S_t817, 5, 1, S_t816);
  instr_struct(&O_t818, 4, 0);
  instr_struct(&S_t819, 5, 1, O_t818);
  instr_struct(&S_t820, 5, 1, S_t819);
  instr_struct(&S_t821, 5, 1, S_t820);
  instr_struct(&S_t822, 5, 1, S_t821);
  instr_struct(&O_t823, 4, 0);
  instr_struct(&O_t824, 4, 0);
  instr_struct(&S_t825, 5, 1, O_t824);
  instr_struct(&S_t826, 5, 1, S_t825);
  instr_struct(&S_t827, 5, 1, S_t826);
  instr_struct(&nilUU_t828, 18, 0);
  instr_struct(&consUU_t829, 19, 2, S_t827, nilUU_t828);
  instr_struct(&consUU_t830, 19, 2, O_t823, consUU_t829);
  instr_struct(&consUU_t831, 19, 2, S_t822, consUU_t830);
  instr_struct(&consUU_t832, 19, 2, S_t817, consUU_t831);
  instr_struct(&consUU_t833, 19, 2, S_t810, consUU_t832);
  instr_struct(&consUU_t834, 19, 2, S_t808, consUU_t833);
  instr_struct(&consUU_t835, 19, 2, S_t805, consUU_t834);
  test1_v141016 = consUU_t835;
  instr_struct(&O_t836, 4, 0);
  instr_struct(&S_t837, 5, 1, O_t836);
  instr_struct(&S_t838, 5, 1, S_t837);
  instr_struct(&S_t839, 5, 1, S_t838);
  instr_struct(&O_t840, 4, 0);
  instr_struct(&O_t841, 4, 0);
  instr_struct(&S_t842, 5, 1, O_t841);
  instr_struct(&S_t843, 5, 1, S_t842);
  instr_struct(&S_t844, 5, 1, S_t843);
  instr_struct(&S_t845, 5, 1, S_t844);
  instr_struct(&S_t846, 5, 1, S_t845);
  instr_struct(&S_t847, 5, 1, S_t846);
  instr_struct(&O_t848, 4, 0);
  instr_struct(&S_t849, 5, 1, O_t848);
  instr_struct(&O_t850, 4, 0);
  instr_struct(&S_t851, 5, 1, O_t850);
  instr_struct(&S_t852, 5, 1, S_t851);
  instr_struct(&S_t853, 5, 1, S_t852);
  instr_struct(&S_t854, 5, 1, S_t853);
  instr_struct(&O_t855, 4, 0);
  instr_struct(&S_t856, 5, 1, O_t855);
  instr_struct(&S_t857, 5, 1, S_t856);
  instr_struct(&O_t858, 4, 0);
  instr_struct(&S_t859, 5, 1, O_t858);
  instr_struct(&S_t860, 5, 1, S_t859);
  instr_struct(&S_t861, 5, 1, S_t860);
  instr_struct(&S_t862, 5, 1, S_t861);
  instr_struct(&S_t863, 5, 1, S_t862);
  instr_struct(&nilUL_t864, 16, 0);
  instr_struct(&consUL_t865, 17, 2, S_t863, nilUL_t864);
  instr_struct(&consUL_t866, 17, 2, S_t857, consUL_t865);
  instr_struct(&consUL_t867, 17, 2, S_t854, consUL_t866);
  instr_struct(&consUL_t868, 17, 2, S_t849, consUL_t867);
  instr_struct(&consUL_t869, 17, 2, S_t847, consUL_t868);
  instr_struct(&consUL_t870, 17, 2, O_t840, consUL_t869);
  instr_struct(&consUL_t871, 17, 2, S_t839, consUL_t870);
  test2_v141017 = consUL_t871;
  call_ret_t872 = cmsortU_i59(test1_v141016);
  instr_app(&app_ret_t873, call_ret_t872, 0);
  instr_free_clo(call_ret_t872);
  msg1_v141018 = app_ret_t873;
  call_ret_t874 = cmsortL_i58(test2_v141017);
  instr_app(&app_ret_t875, call_ret_t874, 0);
  instr_free_clo(call_ret_t874);
  msg2_v141019 = app_ret_t875;
  switch(((tll_node)msg1_v141018)->tag) {
    case 21:
      sorted1_v141020 = ((tll_node)msg1_v141018)->data[0];
      __v141021 = ((tll_node)msg1_v141018)->data[1];
      switch(((tll_node)msg2_v141019)->tag) {
        case 20:
          sorted2_v141022 = ((tll_node)msg2_v141019)->data[0];
          __v141023 = ((tll_node)msg2_v141019)->data[1];
          instr_free_struct(msg2_v141019);
          call_ret_t880 = string_of_listU_i61(sorted1_v141020);
          instr_struct(&false_t881, 3, 0);
          instr_struct(&false_t882, 3, 0);
          instr_struct(&false_t883, 3, 0);
          instr_struct(&false_t884, 3, 0);
          instr_struct(&true_t885, 2, 0);
          instr_struct(&false_t886, 3, 0);
          instr_struct(&true_t887, 2, 0);
          instr_struct(&false_t888, 3, 0);
          instr_struct(&Ascii_t889, 6, 8,
                       false_t881, false_t882, false_t883, false_t884,
                       true_t885, false_t886, true_t887, false_t888);
          instr_struct(&EmptyString_t890, 7, 0);
          instr_struct(&String_t891, 8, 2, Ascii_t889, EmptyString_t890);
          call_ret_t879 = cats_i15(call_ret_t880, String_t891);
          call_ret_t878 = print_i26(call_ret_t879);
          instr_app(&app_ret_t892, call_ret_t878, 0);
          instr_free_clo(call_ret_t878);
          __v141024 = app_ret_t892;
          call_ret_t895 = string_of_listL_i60(sorted2_v141022);
          instr_struct(&false_t896, 3, 0);
          instr_struct(&false_t897, 3, 0);
          instr_struct(&false_t898, 3, 0);
          instr_struct(&false_t899, 3, 0);
          instr_struct(&true_t900, 2, 0);
          instr_struct(&false_t901, 3, 0);
          instr_struct(&true_t902, 2, 0);
          instr_struct(&false_t903, 3, 0);
          instr_struct(&Ascii_t904, 6, 8,
                       false_t896, false_t897, false_t898, false_t899,
                       true_t900, false_t901, true_t902, false_t903);
          instr_struct(&EmptyString_t905, 7, 0);
          instr_struct(&String_t906, 8, 2, Ascii_t904, EmptyString_t905);
          call_ret_t894 = cats_i15(call_ret_t895, String_t906);
          call_ret_t893 = print_i26(call_ret_t894);
          instr_app(&app_ret_t907, call_ret_t893, 0);
          instr_free_clo(call_ret_t893);
          switch_ret_t877 = app_ret_t907;
          break;
      }
      switch_ret_t876 = switch_ret_t877;
      break;
  }
  instr_free_struct(switch_ret_t876);
  return 0;
}

