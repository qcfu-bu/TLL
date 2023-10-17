#include "main.h"

intptr_t idU_1; intptr_t idL_4; intptr_t rwlUU_7; intptr_t rwlUL_14;
intptr_t rwlLU_21; intptr_t rwlLL_28; intptr_t rwrUU_35; intptr_t rwrUL_42;
intptr_t rwrLU_49; intptr_t rwrLL_56; intptr_t sing_elimUU_63;
intptr_t sing_elimUL_67; intptr_t sing_elimLU_71; intptr_t sing_elimLL_75;
intptr_t not_79; intptr_t and_82; intptr_t or_87; intptr_t xor_92;
intptr_t lte_98; intptr_t lt_108; intptr_t pred_113; intptr_t add_118;
intptr_t sub_126; intptr_t mul_134; intptr_t div_142; intptr_t rem_162;
intptr_t free_listUU_168; intptr_t free_listUL_179; intptr_t free_listLL_190;
intptr_t pow_201; intptr_t powm_215; intptr_t ord_231; intptr_t chr_234;
intptr_t str_237; intptr_t strlen_241; intptr_t string_of_int_244;
intptr_t lookup_272; intptr_t leaf_worker_285; intptr_t node_worker_301;
intptr_t cleaf_353; intptr_t cnode_361; intptr_t cfree_377;
intptr_t clookup_386; intptr_t mytree1_403; intptr_t mytree2_408;
intptr_t mytree3_413; intptr_t mytree4_418; intptr_t mytree5_423;
intptr_t mytree6_428;

intptr_t fn0_idU_450(intptr_t A_2, intptr_t m_3) {
  
  
  return m_3;
}

intptr_t fn1_idU_451(intptr_t* env) {
  intptr_t A_2; intptr_t m_3; intptr_t x_452;
  A_2 = env[1];
  m_3 = env[2];
  x_452 = fn0_idU_450(A_2, m_3);
  return x_452;
}

intptr_t fn0_idL_453(intptr_t A_5, intptr_t m_6) {
  
  
  return m_6;
}

intptr_t fn1_idL_454(intptr_t* env) {
  intptr_t A_5; intptr_t m_6; intptr_t x_455;
  A_5 = env[1];
  m_6 = env[2];
  x_455 = fn0_idL_453(A_5, m_6);
  return x_455;
}

intptr_t fn0_rwlUU_456(intptr_t A_8, intptr_t m_9, intptr_t n_10, intptr_t B_11, intptr_t __12, intptr_t __13) {
  
  
  return __13;
}

intptr_t fn1_rwlUU_457(intptr_t* env) {
  intptr_t A_8; intptr_t m_9; intptr_t n_10; intptr_t B_11; intptr_t __12;
  intptr_t __13; intptr_t x_458;
  A_8 = env[1];
  m_9 = env[2];
  n_10 = env[3];
  B_11 = env[4];
  __12 = env[5];
  __13 = env[6];
  x_458 = fn0_rwlUU_456(A_8, m_9, n_10, B_11, __12, __13);
  return x_458;
}

intptr_t fn0_rwlUL_459(intptr_t A_15, intptr_t m_16, intptr_t n_17, intptr_t B_18, intptr_t __19, intptr_t __20) {
  
  
  return __20;
}

intptr_t fn1_rwlUL_460(intptr_t* env) {
  intptr_t A_15; intptr_t m_16; intptr_t n_17; intptr_t B_18; intptr_t __19;
  intptr_t __20; intptr_t x_461;
  A_15 = env[1];
  m_16 = env[2];
  n_17 = env[3];
  B_18 = env[4];
  __19 = env[5];
  __20 = env[6];
  x_461 = fn0_rwlUL_459(A_15, m_16, n_17, B_18, __19, __20);
  return x_461;
}

intptr_t fn0_rwlLU_462(intptr_t A_22, intptr_t m_23, intptr_t n_24, intptr_t B_25, intptr_t __26, intptr_t __27) {
  
  
  return __27;
}

intptr_t fn1_rwlLU_463(intptr_t* env) {
  intptr_t A_22; intptr_t m_23; intptr_t n_24; intptr_t B_25; intptr_t __26;
  intptr_t __27; intptr_t x_464;
  A_22 = env[1];
  m_23 = env[2];
  n_24 = env[3];
  B_25 = env[4];
  __26 = env[5];
  __27 = env[6];
  x_464 = fn0_rwlLU_462(A_22, m_23, n_24, B_25, __26, __27);
  return x_464;
}

intptr_t fn0_rwlLL_465(intptr_t A_29, intptr_t m_30, intptr_t n_31, intptr_t B_32, intptr_t __33, intptr_t __34) {
  
  
  return __34;
}

intptr_t fn1_rwlLL_466(intptr_t* env) {
  intptr_t A_29; intptr_t m_30; intptr_t n_31; intptr_t B_32; intptr_t __33;
  intptr_t __34; intptr_t x_467;
  A_29 = env[1];
  m_30 = env[2];
  n_31 = env[3];
  B_32 = env[4];
  __33 = env[5];
  __34 = env[6];
  x_467 = fn0_rwlLL_465(A_29, m_30, n_31, B_32, __33, __34);
  return x_467;
}

intptr_t fn0_rwrUU_468(intptr_t A_36, intptr_t m_37, intptr_t n_38, intptr_t B_39, intptr_t __40, intptr_t __41) {
  
  
  return __41;
}

intptr_t fn1_rwrUU_469(intptr_t* env) {
  intptr_t A_36; intptr_t m_37; intptr_t n_38; intptr_t B_39; intptr_t __40;
  intptr_t __41; intptr_t x_470;
  A_36 = env[1];
  m_37 = env[2];
  n_38 = env[3];
  B_39 = env[4];
  __40 = env[5];
  __41 = env[6];
  x_470 = fn0_rwrUU_468(A_36, m_37, n_38, B_39, __40, __41);
  return x_470;
}

intptr_t fn0_rwrUL_471(intptr_t A_43, intptr_t m_44, intptr_t n_45, intptr_t B_46, intptr_t __47, intptr_t __48) {
  
  
  return __48;
}

intptr_t fn1_rwrUL_472(intptr_t* env) {
  intptr_t A_43; intptr_t m_44; intptr_t n_45; intptr_t B_46; intptr_t __47;
  intptr_t __48; intptr_t x_473;
  A_43 = env[1];
  m_44 = env[2];
  n_45 = env[3];
  B_46 = env[4];
  __47 = env[5];
  __48 = env[6];
  x_473 = fn0_rwrUL_471(A_43, m_44, n_45, B_46, __47, __48);
  return x_473;
}

intptr_t fn0_rwrLU_474(intptr_t A_50, intptr_t m_51, intptr_t n_52, intptr_t B_53, intptr_t __54, intptr_t __55) {
  
  
  return __55;
}

intptr_t fn1_rwrLU_475(intptr_t* env) {
  intptr_t A_50; intptr_t m_51; intptr_t n_52; intptr_t B_53; intptr_t __54;
  intptr_t __55; intptr_t x_476;
  A_50 = env[1];
  m_51 = env[2];
  n_52 = env[3];
  B_53 = env[4];
  __54 = env[5];
  __55 = env[6];
  x_476 = fn0_rwrLU_474(A_50, m_51, n_52, B_53, __54, __55);
  return x_476;
}

intptr_t fn0_rwrLL_477(intptr_t A_57, intptr_t m_58, intptr_t n_59, intptr_t B_60, intptr_t __61, intptr_t __62) {
  
  
  return __62;
}

intptr_t fn1_rwrLL_478(intptr_t* env) {
  intptr_t A_57; intptr_t m_58; intptr_t n_59; intptr_t B_60; intptr_t __61;
  intptr_t __62; intptr_t x_479;
  A_57 = env[1];
  m_58 = env[2];
  n_59 = env[3];
  B_60 = env[4];
  __61 = env[5];
  __62 = env[6];
  x_479 = fn0_rwrLL_477(A_57, m_58, n_59, B_60, __61, __62);
  return x_479;
}

intptr_t fn0_sing_elimUU_480(intptr_t A_64, intptr_t x_65, intptr_t __66) {
  
  
  return __66;
}

intptr_t fn1_sing_elimUU_481(intptr_t* env) {
  intptr_t A_64; intptr_t x_65; intptr_t __66; intptr_t x_482;
  A_64 = env[1];
  x_65 = env[2];
  __66 = env[3];
  x_482 = fn0_sing_elimUU_480(A_64, x_65, __66);
  return x_482;
}

intptr_t fn0_sing_elimUL_483(intptr_t A_68, intptr_t x_69, intptr_t __70) {
  
  
  return __70;
}

intptr_t fn1_sing_elimUL_484(intptr_t* env) {
  intptr_t A_68; intptr_t x_69; intptr_t __70; intptr_t x_485;
  A_68 = env[1];
  x_69 = env[2];
  __70 = env[3];
  x_485 = fn0_sing_elimUL_483(A_68, x_69, __70);
  return x_485;
}

intptr_t fn0_sing_elimLU_486(intptr_t A_72, intptr_t x_73, intptr_t __74) {
  
  absurd();
  return nothing;
}

intptr_t fn1_sing_elimLU_487(intptr_t* env) {
  intptr_t A_72; intptr_t x_73; intptr_t __74; intptr_t x_488;
  A_72 = env[1];
  x_73 = env[2];
  __74 = env[3];
  x_488 = fn0_sing_elimLU_486(A_72, x_73, __74);
  return x_488;
}

intptr_t fn0_sing_elimLL_489(intptr_t A_76, intptr_t x_77, intptr_t __78) {
  
  
  return __78;
}

intptr_t fn1_sing_elimLL_490(intptr_t* env) {
  intptr_t A_76; intptr_t x_77; intptr_t __78; intptr_t x_491;
  A_76 = env[1];
  x_77 = env[2];
  __78 = env[3];
  x_491 = fn0_sing_elimLL_489(A_76, x_77, __78);
  return x_491;
}

intptr_t fn0_not_492(intptr_t __80) {
  intptr_t x_81;
  switch(__80){
    case 4: //true_4
      x_81 = 5;
      break;
    case 5: //false_5
      x_81 = 4;
      break;
  }
  return x_81;
}

intptr_t fn1_not_493(intptr_t* env) {
  intptr_t __80; intptr_t x_494;
  __80 = env[1];
  x_494 = fn0_not_492(__80);
  return x_494;
}

intptr_t fn0_and_495(intptr_t __83, intptr_t __84) {
  intptr_t x_85; intptr_t x_86;
  switch(__83){
    case 4: //true_4
      switch(__84){
        case 4: //true_4
          x_86 = 4;
          break;
        case 5: //false_5
          x_86 = 5;
          break;
      }
      x_85 = x_86;
      break;
    case 5: //false_5
      x_85 = 5;
      break;
  }
  return x_85;
}

intptr_t fn1_and_496(intptr_t* env) {
  intptr_t __83; intptr_t __84; intptr_t x_497;
  __83 = env[1];
  __84 = env[2];
  x_497 = fn0_and_495(__83, __84);
  return x_497;
}

intptr_t fn0_or_498(intptr_t __88, intptr_t __89) {
  intptr_t x_90; intptr_t x_91;
  switch(__88){
    case 4: //true_4
      x_90 = 4;
      break;
    case 5: //false_5
      switch(__89){
        case 4: //true_4
          x_91 = 4;
          break;
        case 5: //false_5
          x_91 = 5;
          break;
      }
      x_90 = x_91;
      break;
  }
  return x_90;
}

intptr_t fn1_or_499(intptr_t* env) {
  intptr_t __88; intptr_t __89; intptr_t x_500;
  __88 = env[1];
  __89 = env[2];
  x_500 = fn0_or_498(__88, __89);
  return x_500;
}

intptr_t fn0_xor_501(intptr_t __93, intptr_t __94) {
  intptr_t x_95; intptr_t x_96; intptr_t x_97;
  switch(__93){
    case 4: //true_4
      switch(__94){
        case 4: //true_4
          x_96 = 5;
          break;
        case 5: //false_5
          x_96 = 4;
          break;
      }
      x_95 = x_96;
      break;
    case 5: //false_5
      switch(__94){
        case 4: //true_4
          x_97 = 4;
          break;
        case 5: //false_5
          x_97 = 5;
          break;
      }
      x_95 = x_97;
      break;
  }
  return x_95;
}

intptr_t fn1_xor_502(intptr_t* env) {
  intptr_t __93; intptr_t __94; intptr_t x_503;
  __93 = env[1];
  __94 = env[2];
  x_503 = fn0_xor_501(__93, __94);
  return x_503;
}

intptr_t fn0_lte_504(intptr_t __99, intptr_t __100) {
  intptr_t x_101; intptr_t x_102; intptr_t n_103; intptr_t x_104;
  intptr_t x_105; intptr_t n_106; intptr_t x_107;
  switch(__99){
    case 6: //zero_6
      x_101 = 4;
      break;
    default:
      n_103 = getbox(__99, 0);
      switch(__100){
        case 6: //zero_6
          x_104 = 5;
          break;
        default:
          n_106 = getbox(__100, 0);
          x_107 = fn0_lte_504(n_103, n_106);
          x_105 = x_107;
          x_104 = x_105;
          break;
      }
      x_102 = x_104;
      x_101 = x_102;
      break;
  }
  return x_101;
}

intptr_t fn1_lte_505(intptr_t* env) {
  intptr_t __99; intptr_t __100; intptr_t x_506;
  __99 = env[1];
  __100 = env[2];
  x_506 = fn0_lte_504(__99, __100);
  return x_506;
}

intptr_t fn0_lt_507(intptr_t x_109, intptr_t y_110) {
  intptr_t x_111; intptr_t x_112;
  x_112 = mkbox(7, 1); //succ_7
  setbox(x_112, x_109, 0);
  x_111 = fn0_lte_504(x_112, y_110);
  return x_111;
}

intptr_t fn1_lt_508(intptr_t* env) {
  intptr_t x_109; intptr_t y_110; intptr_t x_509;
  x_109 = env[1];
  y_110 = env[2];
  x_509 = fn0_lt_507(x_109, y_110);
  return x_509;
}

intptr_t fn0_pred_510(intptr_t __114) {
  intptr_t x_115; intptr_t x_116; intptr_t n_117;
  switch(__114){
    case 6: //zero_6
      x_115 = 6;
      break;
    default:
      n_117 = getbox(__114, 0);
      x_116 = n_117;
      x_115 = x_116;
      break;
  }
  return x_115;
}

intptr_t fn1_pred_511(intptr_t* env) {
  intptr_t __114; intptr_t x_512;
  __114 = env[1];
  x_512 = fn0_pred_510(__114);
  return x_512;
}

intptr_t fn0_add_513(intptr_t __119, intptr_t __120) {
  intptr_t x_121; intptr_t x_122; intptr_t n_123; intptr_t x_124;
  intptr_t x_125;
  switch(__119){
    case 6: //zero_6
      x_121 = __120;
      break;
    default:
      n_123 = getbox(__119, 0);
      x_124 = fn0_add_513(n_123, __120);
      x_125 = mkbox(7, 1); //succ_7
      setbox(x_125, x_124, 0);
      x_122 = x_125;
      x_121 = x_122;
      break;
  }
  return x_121;
}

intptr_t fn1_add_514(intptr_t* env) {
  intptr_t __119; intptr_t __120; intptr_t x_515;
  __119 = env[1];
  __120 = env[2];
  x_515 = fn0_add_513(__119, __120);
  return x_515;
}

intptr_t fn0_sub_516(intptr_t __127, intptr_t __128) {
  intptr_t x_129; intptr_t x_130; intptr_t n_131; intptr_t x_132;
  intptr_t x_133;
  switch(__128){
    case 6: //zero_6
      x_129 = __127;
      break;
    default:
      n_131 = getbox(__128, 0);
      x_133 = fn0_pred_510(__127);
      x_132 = fn0_sub_516(x_133, n_131);
      x_130 = x_132;
      x_129 = x_130;
      break;
  }
  return x_129;
}

intptr_t fn1_sub_517(intptr_t* env) {
  intptr_t __127; intptr_t __128; intptr_t x_518;
  __127 = env[1];
  __128 = env[2];
  x_518 = fn0_sub_516(__127, __128);
  return x_518;
}

intptr_t fn0_mul_519(intptr_t __135, intptr_t __136) {
  intptr_t x_137; intptr_t x_138; intptr_t n_139; intptr_t x_140;
  intptr_t x_141;
  switch(__135){
    case 6: //zero_6
      x_137 = 6;
      break;
    default:
      n_139 = getbox(__135, 0);
      x_141 = fn0_mul_519(n_139, __136);
      x_140 = fn0_add_513(__136, x_141);
      x_138 = x_140;
      x_137 = x_138;
      break;
  }
  return x_137;
}

intptr_t fn1_mul_520(intptr_t* env) {
  intptr_t __135; intptr_t __136; intptr_t x_521;
  __135 = env[1];
  __136 = env[2];
  x_521 = fn0_mul_519(__135, __136);
  return x_521;
}

intptr_t fn0_div_522(intptr_t x_143, intptr_t y_144) {
  intptr_t x_145; intptr_t x_146; intptr_t loop_147; intptr_t x_148;
  intptr_t x_161; intptr_t x_528; intptr_t x_529;
  x_146 = fn0_lt_507(x_143, y_144);
  switch(x_146){
    case 4: //true_4
      x_145 = 6;
      break;
    case 5: //false_5
      x_148 = mkclo(fn1_loop_524, 2, 2);
      setclo(x_148, pred_113, 1);
      setclo(x_148, sub_126, 2);
      loop_147 = x_148;
      x_528 = appc(loop_147, x_143);
      x_529 = appc(x_528, y_144);
      x_161 = x_529;
      x_145 = x_161;
      break;
  }
  return x_145;
}

intptr_t fn1_div_523(intptr_t* env) {
  intptr_t x_143; intptr_t y_144; intptr_t x_531;
  x_143 = env[1];
  y_144 = env[2];
  x_531 = fn0_div_522(x_143, y_144);
  return x_531;
}

intptr_t fn0_rem_532(intptr_t x_163, intptr_t y_164) {
  intptr_t x_165; intptr_t x_166; intptr_t x_167;
  x_167 = fn0_div_522(x_163, y_164);
  x_166 = fn0_mul_519(x_167, y_164);
  x_165 = fn0_sub_516(x_163, x_166);
  return x_165;
}

intptr_t fn1_rem_533(intptr_t* env) {
  intptr_t x_163; intptr_t y_164; intptr_t x_534;
  x_163 = env[1];
  y_164 = env[2];
  x_534 = fn0_rem_532(x_163, y_164);
  return x_534;
}

intptr_t fn0_free_listUU_535(intptr_t A_169, intptr_t f_170, intptr_t __171) {
  intptr_t x_172; intptr_t x_173; intptr_t hd_174; intptr_t tl_175;
  intptr_t __176; intptr_t x_177; intptr_t x_178; intptr_t x_537;
  switch(__171){
    case 31: //nilUU_31
      x_172 = 24;
      break;
    default:
      hd_174 = getbox(__171, 0);
      tl_175 = getbox(__171, 1);
      x_537 = appc(f_170, hd_174);
      x_177 = x_537;
      __176 = x_177;
      x_178 = fn0_free_listUU_535(nothing, f_170, tl_175);
      x_173 = x_178;
      x_172 = x_173;
      break;
  }
  return x_172;
}

intptr_t fn1_free_listUU_536(intptr_t* env) {
  intptr_t A_169; intptr_t f_170; intptr_t __171; intptr_t x_539;
  A_169 = env[1];
  f_170 = env[2];
  __171 = env[3];
  x_539 = fn0_free_listUU_535(A_169, f_170, __171);
  return x_539;
}

intptr_t fn0_free_listUL_540(intptr_t A_180, intptr_t f_181, intptr_t __182) {
  intptr_t x_183; intptr_t x_184; intptr_t hd_185; intptr_t tl_186;
  intptr_t __187; intptr_t x_188; intptr_t x_189; intptr_t x_542;
  switch(__182){
    case 29: //nilUL_29
      x_183 = 24;
      break;
    default:
      hd_185 = getbox(__182, 0);
      tl_186 = getbox(__182, 1);
      x_542 = appc(f_181, hd_185);
      x_188 = x_542;
      __187 = x_188;
      x_189 = fn0_free_listUL_540(nothing, f_181, tl_186);
      x_184 = x_189;
      ffree(__182);
      x_183 = x_184;
      break;
  }
  return x_183;
}

intptr_t fn1_free_listUL_541(intptr_t* env) {
  intptr_t A_180; intptr_t f_181; intptr_t __182; intptr_t x_544;
  A_180 = env[1];
  f_181 = env[2];
  __182 = env[3];
  x_544 = fn0_free_listUL_540(A_180, f_181, __182);
  return x_544;
}

intptr_t fn0_free_listLL_545(intptr_t A_191, intptr_t f_192, intptr_t __193) {
  intptr_t x_194; intptr_t x_195; intptr_t hd_196; intptr_t tl_197;
  intptr_t __198; intptr_t x_199; intptr_t x_200; intptr_t x_547;
  switch(__193){
    case 25: //nilLL_25
      x_194 = 24;
      break;
    default:
      hd_196 = getbox(__193, 0);
      tl_197 = getbox(__193, 1);
      x_547 = appc(f_192, hd_196);
      x_199 = x_547;
      __198 = x_199;
      x_200 = fn0_free_listLL_545(nothing, f_192, tl_197);
      x_195 = x_200;
      ffree(__193);
      x_194 = x_195;
      break;
  }
  return x_194;
}

intptr_t fn1_free_listLL_546(intptr_t* env) {
  intptr_t A_191; intptr_t f_192; intptr_t __193; intptr_t x_549;
  A_191 = env[1];
  f_192 = env[2];
  __193 = env[3];
  x_549 = fn0_free_listLL_545(A_191, f_192, __193);
  return x_549;
}

intptr_t fn0_pow_550(intptr_t x_202, intptr_t y_203) {
  intptr_t loop_204; intptr_t x_205; intptr_t x_214; intptr_t x_556;
  intptr_t x_557;
  x_205 = mkclo(fn1_loop_552, 1, 2);
  setclo(x_205, x_202, 1);
  loop_204 = x_205;
  x_556 = appc(loop_204, 1);
  x_557 = appc(x_556, y_203);
  x_214 = x_557;
  return x_214;
}

intptr_t fn1_pow_551(intptr_t* env) {
  intptr_t x_202; intptr_t y_203; intptr_t x_559;
  x_202 = env[1];
  y_203 = env[2];
  x_559 = fn0_pow_550(x_202, y_203);
  return x_559;
}

intptr_t fn0_powm_560(intptr_t x_216, intptr_t y_217, intptr_t m_218) {
  intptr_t loop_219; intptr_t x_220; intptr_t x_230; intptr_t x_566;
  intptr_t x_567;
  x_220 = mkclo(fn1_loop_562, 2, 2);
  setclo(x_220, x_216, 1);
  setclo(x_220, m_218, 2);
  loop_219 = x_220;
  x_566 = appc(loop_219, 1);
  x_567 = appc(x_566, y_217);
  x_230 = x_567;
  return x_230;
}

intptr_t fn1_powm_561(intptr_t* env) {
  intptr_t x_216; intptr_t y_217; intptr_t m_218; intptr_t x_569;
  x_216 = env[1];
  y_217 = env[2];
  m_218 = env[3];
  x_569 = fn0_powm_560(x_216, y_217, m_218);
  return x_569;
}

intptr_t fn0_ord_570(intptr_t c_232) {
  intptr_t x_233;
  x_233 = __ord__(c_232);
  return x_233;
}

intptr_t fn1_ord_571(intptr_t* env) {
  intptr_t c_232; intptr_t x_572;
  c_232 = env[1];
  x_572 = fn0_ord_570(c_232);
  return x_572;
}

intptr_t fn0_chr_573(intptr_t i_235) {
  intptr_t x_236;
  x_236 = __chr__(i_235);
  return x_236;
}

intptr_t fn1_chr_574(intptr_t* env) {
  intptr_t i_235; intptr_t x_575;
  i_235 = env[1];
  x_575 = fn0_chr_573(i_235);
  return x_575;
}

intptr_t fn0_str_576(intptr_t c_238) {
  intptr_t x_239; intptr_t x_240;
  x_240 = __str__("");
  x_239 = __push__(x_240, c_238);
  return x_239;
}

intptr_t fn1_str_577(intptr_t* env) {
  intptr_t c_238; intptr_t x_578;
  c_238 = env[1];
  x_578 = fn0_str_576(c_238);
  return x_578;
}

intptr_t fn0_strlen_579(intptr_t s_242) {
  intptr_t x_243;
  x_243 = __size__(s_242);
  return x_243;
}

intptr_t fn1_strlen_580(intptr_t* env) {
  intptr_t s_242; intptr_t x_581;
  s_242 = env[1];
  x_581 = fn0_strlen_579(s_242);
  return x_581;
}

intptr_t fn0_string_of_int_582(intptr_t i_245) {
  intptr_t aux_246; intptr_t x_247; intptr_t x_265; intptr_t x_266;
  intptr_t x_267; intptr_t x_268; intptr_t x_269; intptr_t x_270;
  intptr_t x_271; intptr_t x_587; intptr_t x_589;
  x_247 = mkclo(fn1_aux_584, 3, 1);
  setclo(x_247, ord_231, 1);
  setclo(x_247, chr_234, 2);
  setclo(x_247, str_237, 3);
  aux_246 = x_247;
  x_266 = __lte__(0, i_245);
  switch(x_266){
    case 4: //true_4
      x_587 = appc(aux_246, i_245);
      x_267 = x_587;
      x_265 = x_267;
      break;
    case 5: //false_5
      x_269 = __str__("~");
      x_271 = __neg__(i_245);
      x_589 = appc(aux_246, x_271);
      x_270 = x_589;
      x_268 = __cat__(x_269, x_270);
      x_265 = x_268;
      break;
  }
  return x_265;
}

intptr_t fn1_string_of_int_583(intptr_t* env) {
  intptr_t i_245; intptr_t x_591;
  i_245 = env[1];
  x_591 = fn0_string_of_int_582(i_245);
  return x_591;
}

intptr_t fn0_lookup_592(intptr_t n_273, intptr_t __274) {
  intptr_t x_275; intptr_t x_276; intptr_t __277; intptr_t l_278;
  intptr_t r_279; intptr_t x_280; intptr_t x_281; intptr_t x_282;
  intptr_t x_283; intptr_t x_284;
  switch(__274){
    case 13: //Leaf_13
      x_275 = 5;
      break;
    default:
      __277 = getbox(__274, 0);
      l_278 = getbox(__274, 1);
      r_279 = getbox(__274, 2);
      x_281 = __eq__(__277, n_273);
      switch(x_281){
        case 4: //true_4
          x_280 = 4;
          break;
        case 5: //false_5
          x_283 = fn0_lookup_592(n_273, l_278);
          x_284 = fn0_lookup_592(n_273, r_279);
          x_282 = fn0_or_498(x_283, x_284);
          x_280 = x_282;
          break;
      }
      x_276 = x_280;
      x_275 = x_276;
      break;
  }
  return x_275;
}

intptr_t fn1_lookup_593(intptr_t* env) {
  intptr_t n_273; intptr_t __274; intptr_t x_594;
  n_273 = env[1];
  __274 = env[2];
  x_594 = fn0_lookup_592(n_273, __274);
  return x_594;
}

intptr_t fn0_leaf_worker_595(intptr_t c_286) {
  intptr_t x_287;
  x_287 = lazy(lazy__597, 2);
  setlazy(x_287, leaf_worker_285, 0);
  setlazy(x_287, c_286, 1);
  return x_287;
}

intptr_t fn1_leaf_worker_596(intptr_t* env) {
  intptr_t c_286; intptr_t x_598;
  c_286 = env[1];
  x_598 = fn0_leaf_worker_595(c_286);
  return x_598;
}

intptr_t fn0_node_worker_599(intptr_t x_302, intptr_t l_303, intptr_t r_304, intptr_t __305, intptr_t __306, intptr_t __307) {
  intptr_t x_308;
  x_308 = lazy(lazy__601, 6);
  setlazy(x_308, or_87, 0);
  setlazy(x_308, node_worker_301, 1);
  setlazy(x_308, x_302, 2);
  setlazy(x_308, __305, 3);
  setlazy(x_308, __306, 4);
  setlazy(x_308, __307, 5);
  return x_308;
}

intptr_t fn1_node_worker_600(intptr_t* env) {
  intptr_t x_302; intptr_t l_303; intptr_t r_304; intptr_t __305;
  intptr_t __306; intptr_t __307; intptr_t x_602;
  x_302 = env[1];
  l_303 = env[2];
  r_304 = env[3];
  __305 = env[4];
  __306 = env[5];
  __307 = env[6];
  x_602 = fn0_node_worker_599(x_302, l_303, r_304, __305, __306, __307);
  return x_602;
}

intptr_t fn0_cleaf_603(intptr_t __354) {
  intptr_t x_355;
  x_355 = lazy(lazy__605, 1);
  setlazy(x_355, leaf_worker_285, 0);
  return x_355;
}

intptr_t fn1_cleaf_604(intptr_t* env) {
  intptr_t __354; intptr_t x_607;
  __354 = env[1];
  x_607 = fn0_cleaf_603(__354);
  return x_607;
}

intptr_t fn0_cnode_608(intptr_t x_362, intptr_t l_363, intptr_t r_364, intptr_t __365, intptr_t __366) {
  intptr_t x_367;
  x_367 = lazy(lazy__610, 4);
  setlazy(x_367, node_worker_301, 0);
  setlazy(x_367, x_362, 1);
  setlazy(x_367, __365, 2);
  setlazy(x_367, __366, 3);
  return x_367;
}

intptr_t fn1_cnode_609(intptr_t* env) {
  intptr_t x_362; intptr_t l_363; intptr_t r_364; intptr_t __365;
  intptr_t __366; intptr_t x_612;
  x_362 = env[1];
  l_363 = env[2];
  r_364 = env[3];
  __365 = env[4];
  __366 = env[5];
  x_612 = fn0_cnode_608(x_362, l_363, r_364, __365, __366);
  return x_612;
}

intptr_t fn0_cfree_613(intptr_t t_378, intptr_t ct_379) {
  intptr_t x_380;
  x_380 = lazy(lazy__615, 1);
  setlazy(x_380, ct_379, 0);
  return x_380;
}

intptr_t fn1_cfree_614(intptr_t* env) {
  intptr_t t_378; intptr_t ct_379; intptr_t x_616;
  t_378 = env[1];
  ct_379 = env[2];
  x_616 = fn0_cfree_613(t_378, ct_379);
  return x_616;
}

intptr_t fn0_clookup_617(intptr_t k_387, intptr_t t_388, intptr_t ct_389) {
  intptr_t x_390;
  x_390 = lazy(lazy__619, 2);
  setlazy(x_390, k_387, 0);
  setlazy(x_390, ct_389, 1);
  return x_390;
}

intptr_t fn1_clookup_618(intptr_t* env) {
  intptr_t k_387; intptr_t t_388; intptr_t ct_389; intptr_t x_621;
  k_387 = env[1];
  t_388 = env[2];
  ct_389 = env[3];
  x_621 = fn0_clookup_617(k_387, t_388, ct_389);
  return x_621;
}

intptr_t fn0_mytree1_622(intptr_t x_404) {
  intptr_t x_405; intptr_t x_406; intptr_t x_407;
  x_406 = fn0_cleaf_603(24);
  x_407 = fn0_cleaf_603(24);
  x_405 = fn0_cnode_608(x_404, nothing, nothing, x_406, x_407);
  return x_405;
}

intptr_t fn1_mytree1_623(intptr_t* env) {
  intptr_t x_404; intptr_t x_624;
  x_404 = env[1];
  x_624 = fn0_mytree1_622(x_404);
  return x_624;
}

intptr_t fn0_mytree2_625(intptr_t x_409) {
  intptr_t x_410; intptr_t x_411; intptr_t x_412;
  x_411 = fn0_mytree1_622(1);
  x_412 = fn0_mytree1_622(2);
  x_410 = fn0_cnode_608(x_409, nothing, nothing, x_411, x_412);
  return x_410;
}

intptr_t fn1_mytree2_626(intptr_t* env) {
  intptr_t x_409; intptr_t x_627;
  x_409 = env[1];
  x_627 = fn0_mytree2_625(x_409);
  return x_627;
}

intptr_t fn0_mytree3_628(intptr_t x_414) {
  intptr_t x_415; intptr_t x_416; intptr_t x_417;
  x_416 = fn0_mytree2_625(3);
  x_417 = fn0_mytree2_625(4);
  x_415 = fn0_cnode_608(x_414, nothing, nothing, x_416, x_417);
  return x_415;
}

intptr_t fn1_mytree3_629(intptr_t* env) {
  intptr_t x_414; intptr_t x_630;
  x_414 = env[1];
  x_630 = fn0_mytree3_628(x_414);
  return x_630;
}

intptr_t fn0_mytree4_631(intptr_t x_419) {
  intptr_t x_420; intptr_t x_421; intptr_t x_422;
  x_421 = fn0_mytree3_628(8);
  x_422 = fn0_mytree3_628(7);
  x_420 = fn0_cnode_608(x_419, nothing, nothing, x_421, x_422);
  return x_420;
}

intptr_t fn1_mytree4_632(intptr_t* env) {
  intptr_t x_419; intptr_t x_633;
  x_419 = env[1];
  x_633 = fn0_mytree4_631(x_419);
  return x_633;
}

intptr_t fn0_mytree5_634(intptr_t x_424) {
  intptr_t x_425; intptr_t x_426; intptr_t x_427;
  x_426 = fn0_mytree4_631(9);
  x_427 = fn0_mytree4_631(10);
  x_425 = fn0_cnode_608(x_424, nothing, nothing, x_426, x_427);
  return x_425;
}

intptr_t fn1_mytree5_635(intptr_t* env) {
  intptr_t x_424; intptr_t x_636;
  x_424 = env[1];
  x_636 = fn0_mytree5_634(x_424);
  return x_636;
}

intptr_t fn0_mytree6_637(intptr_t x_429) {
  intptr_t x_430; intptr_t x_431; intptr_t x_432;
  x_431 = fn0_mytree5_634(11);
  x_432 = fn0_mytree5_634(12);
  x_430 = fn0_cnode_608(x_429, nothing, nothing, x_431, x_432);
  return x_430;
}

intptr_t fn1_mytree6_638(intptr_t* env) {
  intptr_t x_429; intptr_t x_639;
  x_429 = env[1];
  x_639 = fn0_mytree6_637(x_429);
  return x_639;
}

intptr_t lazy__641(intptr_t* env) {
  intptr_t cfree_377; intptr_t clookup_386; intptr_t ct_433; intptr_t _436;
  intptr_t x_437; intptr_t x_438; intptr_t x_439; intptr_t m_440;
  intptr_t n_441; intptr_t __442; intptr_t x_443; intptr_t x_444;
  intptr_t x_445; intptr_t x_446; intptr_t x_447; intptr_t x_448;
  intptr_t x_449;
  cfree_377 = env[0];
  clookup_386 = env[1];
  ct_433 = env[2];
  x_438 = fn0_clookup_617(1, nothing, ct_433);
  x_437 = force(x_438);
  ffree(x_438);
  _436 = x_437;
  m_440 = getbox(_436, 0);
  n_441 = getbox(_436, 1);
  switch(m_440){
    case 4: //true_4
      x_445 = __str__("true");
      x_444 = __print__(x_445);
      x_443 = x_444;
      break;
    case 5: //false_5
      x_447 = __str__("false");
      x_446 = __print__(x_447);
      x_443 = x_446;
      break;
  }
  __442 = x_443;
  x_449 = fn0_cfree_613(nothing, n_441);
  x_448 = force(x_449);
  ffree(x_449);
  x_439 = x_448;
  ffree(_436);
  return x_439;
}

intptr_t lazy__619(intptr_t* env) {
  intptr_t k_387; intptr_t ct_389; intptr_t c_391; intptr_t x_392;
  intptr_t c_393; intptr_t x_394; intptr_t x_395; intptr_t _396;
  intptr_t x_397; intptr_t x_398; intptr_t m_399; intptr_t n_400;
  intptr_t x_401; intptr_t x_402;
  k_387 = env[0];
  ct_389 = env[1];
  x_392 = force(ct_389);
  ffree(ct_389);
  c_391 = x_392;
  x_395 = mkbox(16, 1); //Lookup_16
  setbox(x_395, k_387, 0);
  x_394 = __send__(c_391, x_395);
  c_393 = x_394;
  x_397 = __recv0__(c_393);
  _396 = x_397;
  m_399 = getbox(_396, 0);
  n_400 = getbox(_396, 1);
  x_401 = lazy(lazy__620, 1);
  setlazy(x_401, n_400, 0);
  x_402 = rebox(_396, 43); //ex1UL_43
  setbox(x_402, m_399, 0);
  setbox(x_402, x_401, 1);
  x_398 = x_402;
  return x_398;
}

intptr_t lazy__620(intptr_t* env) {
  intptr_t n_400;
  n_400 = env[0];
  return n_400;
}

intptr_t lazy__615(intptr_t* env) {
  intptr_t ct_379; intptr_t c_381; intptr_t x_382; intptr_t c_383;
  intptr_t x_384; intptr_t x_385;
  ct_379 = env[0];
  x_382 = force(ct_379);
  ffree(ct_379);
  c_381 = x_382;
  x_384 = __send__(c_381, 15);
  c_383 = x_384;
  x_385 = __close1__(c_383);
  return x_385;
}

intptr_t lazy__610(intptr_t* env) {
  intptr_t node_worker_301; intptr_t x_362; intptr_t __365; intptr_t __366;
  intptr_t l_ch_368; intptr_t x_369; intptr_t r_ch_370; intptr_t x_371;
  intptr_t x_372; intptr_t x_373;
  node_worker_301 = env[0];
  x_362 = env[1];
  __365 = env[2];
  __366 = env[3];
  x_369 = force(__365);
  ffree(__365);
  l_ch_368 = x_369;
  x_371 = force(__366);
  ffree(__366);
  r_ch_370 = x_371;
  x_373 = mkclo(fn1_lam_611, 4, 1);
  setclo(x_373, node_worker_301, 1);
  setclo(x_373, x_362, 2);
  setclo(x_373, l_ch_368, 3);
  setclo(x_373, r_ch_370, 4);
  x_372 = __fork__(x_373);
  return x_372;
}

intptr_t fn1_lam_611(intptr_t* env) {
  intptr_t node_worker_301; intptr_t x_362; intptr_t l_ch_368;
  intptr_t r_ch_370; intptr_t lam_374; intptr_t _375; intptr_t x_376;
  lam_374 = env[0];
  node_worker_301 = env[1];
  x_362 = env[2];
  l_ch_368 = env[3];
  r_ch_370 = env[4];
  _375 = env[5];
  x_376 = fn0_node_worker_599(x_362, nothing, nothing, l_ch_368, r_ch_370, _375);
  return x_376;
}

intptr_t lazy__605(intptr_t* env) {
  intptr_t leaf_worker_285; intptr_t x_356; intptr_t x_357;
  leaf_worker_285 = env[0];
  x_357 = mkclo(fn1_lam_606, 1, 1);
  setclo(x_357, leaf_worker_285, 1);
  x_356 = __fork__(x_357);
  return x_356;
}

intptr_t fn1_lam_606(intptr_t* env) {
  intptr_t leaf_worker_285; intptr_t lam_358; intptr_t _359; intptr_t x_360;
  lam_358 = env[0];
  leaf_worker_285 = env[1];
  _359 = env[2];
  x_360 = fn0_leaf_worker_595(_359);
  return x_360;
}

intptr_t lazy__601(intptr_t* env) {
  intptr_t or_87; intptr_t node_worker_301; intptr_t x_302; intptr_t __305;
  intptr_t __306; intptr_t __307; intptr_t _309; intptr_t x_310;
  intptr_t x_311; intptr_t m_312; intptr_t n_313; intptr_t x_314;
  intptr_t l_ch_315; intptr_t x_316; intptr_t r_ch_317; intptr_t x_318;
  intptr_t __319; intptr_t x_320; intptr_t __321; intptr_t x_322;
  intptr_t x_323; intptr_t x_324; intptr_t k_325; intptr_t x_326;
  intptr_t x_327; intptr_t c_328; intptr_t x_329; intptr_t x_330;
  intptr_t x_331; intptr_t l_ch_332; intptr_t x_333; intptr_t x_334;
  intptr_t r_ch_335; intptr_t x_336; intptr_t x_337; intptr_t _338;
  intptr_t x_339; intptr_t x_340; intptr_t m_341; intptr_t n_342;
  intptr_t _343; intptr_t x_344; intptr_t x_345; intptr_t m_346;
  intptr_t n_347; intptr_t c_348; intptr_t x_349; intptr_t x_350;
  intptr_t x_351; intptr_t x_352;
  or_87 = env[0];
  node_worker_301 = env[1];
  x_302 = env[2];
  __305 = env[3];
  __306 = env[4];
  __307 = env[5];
  x_310 = __recv0__(__307);
  _309 = x_310;
  m_312 = getbox(_309, 0);
  n_313 = getbox(_309, 1);
  switch(m_312){
    case 15: //Free_15
      x_316 = __send__(__305, 15);
      l_ch_315 = x_316;
      x_318 = __send__(__306, 15);
      r_ch_317 = x_318;
      x_320 = __close1__(l_ch_315);
      __319 = x_320;
      x_322 = __close1__(r_ch_317);
      __321 = x_322;
      x_323 = __close0__(n_313);
      x_314 = x_323;
      break;
    default:
      k_325 = getbox(m_312, 0);
      x_327 = __eq__(x_302, k_325);
      switch(x_327){
        case 4: //true_4
          x_329 = __send__(n_313, 4);
          c_328 = x_329;
          x_331 = fn0_node_worker_599(x_302, nothing, nothing, __305, __306, c_328);
          x_330 = force(x_331);
          ffree(x_331);
          x_326 = x_330;
          break;
        case 5: //false_5
          x_334 = mkbox(16, 1); //Lookup_16
          setbox(x_334, k_325, 0);
          x_333 = __send__(__305, x_334);
          l_ch_332 = x_333;
          x_337 = mkbox(16, 1); //Lookup_16
          setbox(x_337, k_325, 0);
          x_336 = __send__(__306, x_337);
          r_ch_335 = x_336;
          x_339 = __recv0__(l_ch_332);
          _338 = x_339;
          m_341 = getbox(_338, 0);
          n_342 = getbox(_338, 1);
          x_344 = __recv0__(r_ch_335);
          _343 = x_344;
          m_346 = getbox(_343, 0);
          n_347 = getbox(_343, 1);
          x_350 = fn0_or_498(m_341, m_346);
          x_349 = __send__(n_313, x_350);
          c_348 = x_349;
          x_352 = fn0_node_worker_599(x_302, nothing, nothing, n_342, n_347, c_348);
          x_351 = force(x_352);
          ffree(x_352);
          x_345 = x_351;
          ffree(_343);
          x_340 = x_345;
          ffree(_338);
          x_326 = x_340;
          break;
      }
      x_324 = x_326;
      x_314 = x_324;
      break;
  }
  x_311 = x_314;
  ffree(_309);
  return x_311;
}

intptr_t lazy__597(intptr_t* env) {
  intptr_t leaf_worker_285; intptr_t c_286; intptr_t _288; intptr_t x_289;
  intptr_t x_290; intptr_t m_291; intptr_t n_292; intptr_t x_293;
  intptr_t x_294; intptr_t x_295; intptr_t c_297; intptr_t x_298;
  intptr_t x_299; intptr_t x_300;
  leaf_worker_285 = env[0];
  c_286 = env[1];
  x_289 = __recv0__(c_286);
  _288 = x_289;
  m_291 = getbox(_288, 0);
  n_292 = getbox(_288, 1);
  switch(m_291){
    case 15: //Free_15
      x_294 = __close0__(n_292);
      x_293 = x_294;
      break;
    default:
      x_298 = __send__(n_292, 5);
      c_297 = x_298;
      x_300 = fn0_leaf_worker_595(c_297);
      x_299 = force(x_300);
      ffree(x_300);
      x_295 = x_299;
      x_293 = x_295;
      break;
  }
  x_290 = x_293;
  ffree(_288);
  return x_290;
}

intptr_t fn1_aux_584(intptr_t* env) {
  intptr_t ord_231; intptr_t chr_234; intptr_t str_237; intptr_t aux_248;
  intptr_t i_249; intptr_t x_250; intptr_t x_251; intptr_t r_252;
  intptr_t x_253; intptr_t i_254; intptr_t x_255; intptr_t x_256;
  intptr_t x_257; intptr_t x_258; intptr_t x_259; intptr_t x_260;
  intptr_t x_261; intptr_t x_262; intptr_t x_263; intptr_t x_264;
  intptr_t x_585;
  aux_248 = env[0];
  ord_231 = env[1];
  chr_234 = env[2];
  str_237 = env[3];
  i_249 = env[4];
  x_251 = __lte__(10, i_249);
  switch(x_251){
    case 4: //true_4
      x_253 = __mod__(i_249, 10);
      r_252 = x_253;
      x_255 = __div__(i_249, 10);
      i_254 = x_255;
      x_585 = appc(aux_248, i_254);
      x_257 = x_585;
      x_260 = fn0_ord_570('0');
      x_259 = __add__(r_252, x_260);
      x_258 = fn0_chr_573(x_259);
      x_256 = __push__(x_257, x_258);
      x_250 = x_256;
      break;
    case 5: //false_5
      x_264 = fn0_ord_570('0');
      x_263 = __add__(i_249, x_264);
      x_262 = fn0_chr_573(x_263);
      x_261 = fn0_str_576(x_262);
      x_250 = x_261;
      break;
  }
  return x_250;
}

intptr_t fn1_loop_562(intptr_t* env) {
  intptr_t x_216; intptr_t m_218; intptr_t loop_221; intptr_t acc_222;
  intptr_t y_223; intptr_t x_224; intptr_t x_225; intptr_t x_226;
  intptr_t x_227; intptr_t x_228; intptr_t x_229; intptr_t x_563;
  intptr_t x_564;
  loop_221 = env[0];
  x_216 = env[1];
  m_218 = env[2];
  acc_222 = env[3];
  y_223 = env[4];
  x_225 = __lte__(y_223, 0);
  switch(x_225){
    case 4: //true_4
      x_224 = acc_222;
      break;
    case 5: //false_5
      x_228 = __mul__(x_216, acc_222);
      x_227 = __mod__(x_228, m_218);
      x_229 = __sub__(y_223, 1);
      x_563 = appc(loop_221, x_227);
      x_564 = appc(x_563, x_229);
      x_226 = x_564;
      x_224 = x_226;
      break;
  }
  return x_224;
}

intptr_t fn1_loop_552(intptr_t* env) {
  intptr_t x_202; intptr_t loop_206; intptr_t acc_207; intptr_t y_208;
  intptr_t x_209; intptr_t x_210; intptr_t x_211; intptr_t x_212;
  intptr_t x_213; intptr_t x_553; intptr_t x_554;
  loop_206 = env[0];
  x_202 = env[1];
  acc_207 = env[2];
  y_208 = env[3];
  x_210 = __lte__(y_208, 0);
  switch(x_210){
    case 4: //true_4
      x_209 = acc_207;
      break;
    case 5: //false_5
      x_212 = __mul__(x_202, acc_207);
      x_213 = __sub__(y_208, 1);
      x_553 = appc(loop_206, x_212);
      x_554 = appc(x_553, x_213);
      x_211 = x_554;
      x_209 = x_211;
      break;
  }
  return x_209;
}

intptr_t fn1_loop_524(intptr_t* env) {
  intptr_t pred_113; intptr_t sub_126; intptr_t loop_149; intptr_t x_150;
  intptr_t y_151; intptr_t x_152; intptr_t x_153; intptr_t x_154;
  intptr_t x_155; intptr_t x_156; intptr_t x_157; intptr_t n_158;
  intptr_t x_159; intptr_t x_160; intptr_t x_525; intptr_t x_526;
  loop_149 = env[0];
  pred_113 = env[1];
  sub_126 = env[2];
  x_150 = env[3];
  y_151 = env[4];
  x_154 = fn0_pred_510(y_151);
  x_153 = fn0_sub_516(x_150, x_154);
  switch(x_153){
    case 6: //zero_6
      x_152 = 6;
      break;
    default:
      x_157 = fn0_pred_510(y_151);
      x_156 = fn0_sub_516(x_150, x_157);
      n_158 = getbox(x_156, 0);
      x_525 = appc(loop_149, n_158);
      x_526 = appc(x_525, y_151);
      x_159 = x_526;
      x_160 = mkbox(7, 1); //succ_7
      setbox(x_160, x_159, 0);
      x_155 = x_160;
      x_152 = x_155;
      break;
  }
  return x_152;
}

int main() {
  begin_run();
  intptr_t ct_433; intptr_t x_434; intptr_t x_435; intptr_t x_640;
  idU_1 = mkclo(fn1_idU_451, 0, 2);
  idL_4 = mkclo(fn1_idL_454, 0, 2);
  rwlUU_7 = mkclo(fn1_rwlUU_457, 0, 6);
  rwlUL_14 = mkclo(fn1_rwlUL_460, 0, 6);
  rwlLU_21 = mkclo(fn1_rwlLU_463, 0, 6);
  rwlLL_28 = mkclo(fn1_rwlLL_466, 0, 6);
  rwrUU_35 = mkclo(fn1_rwrUU_469, 0, 6);
  rwrUL_42 = mkclo(fn1_rwrUL_472, 0, 6);
  rwrLU_49 = mkclo(fn1_rwrLU_475, 0, 6);
  rwrLL_56 = mkclo(fn1_rwrLL_478, 0, 6);
  sing_elimUU_63 = mkclo(fn1_sing_elimUU_481, 0, 3);
  sing_elimUL_67 = mkclo(fn1_sing_elimUL_484, 0, 3);
  sing_elimLU_71 = mkclo(fn1_sing_elimLU_487, 0, 3);
  sing_elimLL_75 = mkclo(fn1_sing_elimLL_490, 0, 3);
  not_79 = mkclo(fn1_not_493, 0, 1);
  and_82 = mkclo(fn1_and_496, 0, 2);
  or_87 = mkclo(fn1_or_499, 0, 2);
  xor_92 = mkclo(fn1_xor_502, 0, 2);
  lte_98 = mkclo(fn1_lte_505, 0, 2);
  lt_108 = mkclo(fn1_lt_508, 0, 2);
  pred_113 = mkclo(fn1_pred_511, 0, 1);
  add_118 = mkclo(fn1_add_514, 0, 2);
  sub_126 = mkclo(fn1_sub_517, 0, 2);
  mul_134 = mkclo(fn1_mul_520, 0, 2);
  div_142 = mkclo(fn1_div_523, 0, 2);
  rem_162 = mkclo(fn1_rem_533, 0, 2);
  free_listUU_168 = mkclo(fn1_free_listUU_536, 0, 3);
  free_listUL_179 = mkclo(fn1_free_listUL_541, 0, 3);
  free_listLL_190 = mkclo(fn1_free_listLL_546, 0, 3);
  pow_201 = mkclo(fn1_pow_551, 0, 2);
  powm_215 = mkclo(fn1_powm_561, 0, 3);
  ord_231 = mkclo(fn1_ord_571, 0, 1);
  chr_234 = mkclo(fn1_chr_574, 0, 1);
  str_237 = mkclo(fn1_str_577, 0, 1);
  strlen_241 = mkclo(fn1_strlen_580, 0, 1);
  string_of_int_244 = mkclo(fn1_string_of_int_583, 0, 1);
  lookup_272 = mkclo(fn1_lookup_593, 0, 2);
  leaf_worker_285 = mkclo(fn1_leaf_worker_596, 0, 1);
  node_worker_301 = mkclo(fn1_node_worker_600, 0, 6);
  cleaf_353 = mkclo(fn1_cleaf_604, 0, 1);
  cnode_361 = mkclo(fn1_cnode_609, 0, 5);
  cfree_377 = mkclo(fn1_cfree_614, 0, 2);
  clookup_386 = mkclo(fn1_clookup_618, 0, 3);
  mytree1_403 = mkclo(fn1_mytree1_623, 0, 1);
  mytree2_408 = mkclo(fn1_mytree2_626, 0, 1);
  mytree3_413 = mkclo(fn1_mytree3_629, 0, 1);
  mytree4_418 = mkclo(fn1_mytree4_632, 0, 1);
  mytree5_423 = mkclo(fn1_mytree5_635, 0, 1);
  mytree6_428 = mkclo(fn1_mytree6_638, 0, 1);
  x_434 = fn0_mytree6_637(100);
  ct_433 = x_434;
  x_435 = lazy(lazy__641, 3);
  setlazy(x_435, cfree_377, 0);
  setlazy(x_435, clookup_386, 1);
  setlazy(x_435, ct_433, 2);
  x_640 = force(x_435);
  end_run();
}

