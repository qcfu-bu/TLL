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
intptr_t hd_vec1_272; intptr_t hd_vec2_279; intptr_t hd_vec3_286;
intptr_t vlength_293; intptr_t xs_303; intptr_t x_305; intptr_t y_307;
intptr_t z_309;

intptr_t fn0_idU_311(intptr_t A_2, intptr_t m_3) {
  
  
  return m_3;
}

intptr_t fn1_idU_312(intptr_t* env) {
  intptr_t A_2; intptr_t m_3; intptr_t x_313;
  A_2 = env[1];
  m_3 = env[2];
  x_313 = fn0_idU_311(A_2, m_3);
  return x_313;
}

intptr_t fn0_idL_314(intptr_t A_5, intptr_t m_6) {
  
  
  return m_6;
}

intptr_t fn1_idL_315(intptr_t* env) {
  intptr_t A_5; intptr_t m_6; intptr_t x_316;
  A_5 = env[1];
  m_6 = env[2];
  x_316 = fn0_idL_314(A_5, m_6);
  return x_316;
}

intptr_t fn0_rwlUU_317(intptr_t A_8, intptr_t m_9, intptr_t n_10, intptr_t B_11, intptr_t __12, intptr_t __13) {
  
  
  return __13;
}

intptr_t fn1_rwlUU_318(intptr_t* env) {
  intptr_t A_8; intptr_t m_9; intptr_t n_10; intptr_t B_11; intptr_t __12;
  intptr_t __13; intptr_t x_319;
  A_8 = env[1];
  m_9 = env[2];
  n_10 = env[3];
  B_11 = env[4];
  __12 = env[5];
  __13 = env[6];
  x_319 = fn0_rwlUU_317(A_8, m_9, n_10, B_11, __12, __13);
  return x_319;
}

intptr_t fn0_rwlUL_320(intptr_t A_15, intptr_t m_16, intptr_t n_17, intptr_t B_18, intptr_t __19, intptr_t __20) {
  
  
  return __20;
}

intptr_t fn1_rwlUL_321(intptr_t* env) {
  intptr_t A_15; intptr_t m_16; intptr_t n_17; intptr_t B_18; intptr_t __19;
  intptr_t __20; intptr_t x_322;
  A_15 = env[1];
  m_16 = env[2];
  n_17 = env[3];
  B_18 = env[4];
  __19 = env[5];
  __20 = env[6];
  x_322 = fn0_rwlUL_320(A_15, m_16, n_17, B_18, __19, __20);
  return x_322;
}

intptr_t fn0_rwlLU_323(intptr_t A_22, intptr_t m_23, intptr_t n_24, intptr_t B_25, intptr_t __26, intptr_t __27) {
  
  
  return __27;
}

intptr_t fn1_rwlLU_324(intptr_t* env) {
  intptr_t A_22; intptr_t m_23; intptr_t n_24; intptr_t B_25; intptr_t __26;
  intptr_t __27; intptr_t x_325;
  A_22 = env[1];
  m_23 = env[2];
  n_24 = env[3];
  B_25 = env[4];
  __26 = env[5];
  __27 = env[6];
  x_325 = fn0_rwlLU_323(A_22, m_23, n_24, B_25, __26, __27);
  return x_325;
}

intptr_t fn0_rwlLL_326(intptr_t A_29, intptr_t m_30, intptr_t n_31, intptr_t B_32, intptr_t __33, intptr_t __34) {
  
  
  return __34;
}

intptr_t fn1_rwlLL_327(intptr_t* env) {
  intptr_t A_29; intptr_t m_30; intptr_t n_31; intptr_t B_32; intptr_t __33;
  intptr_t __34; intptr_t x_328;
  A_29 = env[1];
  m_30 = env[2];
  n_31 = env[3];
  B_32 = env[4];
  __33 = env[5];
  __34 = env[6];
  x_328 = fn0_rwlLL_326(A_29, m_30, n_31, B_32, __33, __34);
  return x_328;
}

intptr_t fn0_rwrUU_329(intptr_t A_36, intptr_t m_37, intptr_t n_38, intptr_t B_39, intptr_t __40, intptr_t __41) {
  
  
  return __41;
}

intptr_t fn1_rwrUU_330(intptr_t* env) {
  intptr_t A_36; intptr_t m_37; intptr_t n_38; intptr_t B_39; intptr_t __40;
  intptr_t __41; intptr_t x_331;
  A_36 = env[1];
  m_37 = env[2];
  n_38 = env[3];
  B_39 = env[4];
  __40 = env[5];
  __41 = env[6];
  x_331 = fn0_rwrUU_329(A_36, m_37, n_38, B_39, __40, __41);
  return x_331;
}

intptr_t fn0_rwrUL_332(intptr_t A_43, intptr_t m_44, intptr_t n_45, intptr_t B_46, intptr_t __47, intptr_t __48) {
  
  
  return __48;
}

intptr_t fn1_rwrUL_333(intptr_t* env) {
  intptr_t A_43; intptr_t m_44; intptr_t n_45; intptr_t B_46; intptr_t __47;
  intptr_t __48; intptr_t x_334;
  A_43 = env[1];
  m_44 = env[2];
  n_45 = env[3];
  B_46 = env[4];
  __47 = env[5];
  __48 = env[6];
  x_334 = fn0_rwrUL_332(A_43, m_44, n_45, B_46, __47, __48);
  return x_334;
}

intptr_t fn0_rwrLU_335(intptr_t A_50, intptr_t m_51, intptr_t n_52, intptr_t B_53, intptr_t __54, intptr_t __55) {
  
  
  return __55;
}

intptr_t fn1_rwrLU_336(intptr_t* env) {
  intptr_t A_50; intptr_t m_51; intptr_t n_52; intptr_t B_53; intptr_t __54;
  intptr_t __55; intptr_t x_337;
  A_50 = env[1];
  m_51 = env[2];
  n_52 = env[3];
  B_53 = env[4];
  __54 = env[5];
  __55 = env[6];
  x_337 = fn0_rwrLU_335(A_50, m_51, n_52, B_53, __54, __55);
  return x_337;
}

intptr_t fn0_rwrLL_338(intptr_t A_57, intptr_t m_58, intptr_t n_59, intptr_t B_60, intptr_t __61, intptr_t __62) {
  
  
  return __62;
}

intptr_t fn1_rwrLL_339(intptr_t* env) {
  intptr_t A_57; intptr_t m_58; intptr_t n_59; intptr_t B_60; intptr_t __61;
  intptr_t __62; intptr_t x_340;
  A_57 = env[1];
  m_58 = env[2];
  n_59 = env[3];
  B_60 = env[4];
  __61 = env[5];
  __62 = env[6];
  x_340 = fn0_rwrLL_338(A_57, m_58, n_59, B_60, __61, __62);
  return x_340;
}

intptr_t fn0_sing_elimUU_341(intptr_t A_64, intptr_t x_65, intptr_t __66) {
  
  
  return __66;
}

intptr_t fn1_sing_elimUU_342(intptr_t* env) {
  intptr_t A_64; intptr_t x_65; intptr_t __66; intptr_t x_343;
  A_64 = env[1];
  x_65 = env[2];
  __66 = env[3];
  x_343 = fn0_sing_elimUU_341(A_64, x_65, __66);
  return x_343;
}

intptr_t fn0_sing_elimUL_344(intptr_t A_68, intptr_t x_69, intptr_t __70) {
  
  
  return __70;
}

intptr_t fn1_sing_elimUL_345(intptr_t* env) {
  intptr_t A_68; intptr_t x_69; intptr_t __70; intptr_t x_346;
  A_68 = env[1];
  x_69 = env[2];
  __70 = env[3];
  x_346 = fn0_sing_elimUL_344(A_68, x_69, __70);
  return x_346;
}

intptr_t fn0_sing_elimLU_347(intptr_t A_72, intptr_t x_73, intptr_t __74) {
  
  absurd();
  return nothing;
}

intptr_t fn1_sing_elimLU_348(intptr_t* env) {
  intptr_t A_72; intptr_t x_73; intptr_t __74; intptr_t x_349;
  A_72 = env[1];
  x_73 = env[2];
  __74 = env[3];
  x_349 = fn0_sing_elimLU_347(A_72, x_73, __74);
  return x_349;
}

intptr_t fn0_sing_elimLL_350(intptr_t A_76, intptr_t x_77, intptr_t __78) {
  
  
  return __78;
}

intptr_t fn1_sing_elimLL_351(intptr_t* env) {
  intptr_t A_76; intptr_t x_77; intptr_t __78; intptr_t x_352;
  A_76 = env[1];
  x_77 = env[2];
  __78 = env[3];
  x_352 = fn0_sing_elimLL_350(A_76, x_77, __78);
  return x_352;
}

intptr_t fn0_not_353(intptr_t __80) {
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

intptr_t fn1_not_354(intptr_t* env) {
  intptr_t __80; intptr_t x_355;
  __80 = env[1];
  x_355 = fn0_not_353(__80);
  return x_355;
}

intptr_t fn0_and_356(intptr_t __83, intptr_t __84) {
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

intptr_t fn1_and_357(intptr_t* env) {
  intptr_t __83; intptr_t __84; intptr_t x_358;
  __83 = env[1];
  __84 = env[2];
  x_358 = fn0_and_356(__83, __84);
  return x_358;
}

intptr_t fn0_or_359(intptr_t __88, intptr_t __89) {
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

intptr_t fn1_or_360(intptr_t* env) {
  intptr_t __88; intptr_t __89; intptr_t x_361;
  __88 = env[1];
  __89 = env[2];
  x_361 = fn0_or_359(__88, __89);
  return x_361;
}

intptr_t fn0_xor_362(intptr_t __93, intptr_t __94) {
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

intptr_t fn1_xor_363(intptr_t* env) {
  intptr_t __93; intptr_t __94; intptr_t x_364;
  __93 = env[1];
  __94 = env[2];
  x_364 = fn0_xor_362(__93, __94);
  return x_364;
}

intptr_t fn0_lte_365(intptr_t __99, intptr_t __100) {
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
          x_107 = fn0_lte_365(n_103, n_106);
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

intptr_t fn1_lte_366(intptr_t* env) {
  intptr_t __99; intptr_t __100; intptr_t x_367;
  __99 = env[1];
  __100 = env[2];
  x_367 = fn0_lte_365(__99, __100);
  return x_367;
}

intptr_t fn0_lt_368(intptr_t x_109, intptr_t y_110) {
  intptr_t x_111; intptr_t x_112;
  x_112 = mkbox(7, 1); //succ_7
  setbox(x_112, x_109, 0);
  x_111 = fn0_lte_365(x_112, y_110);
  return x_111;
}

intptr_t fn1_lt_369(intptr_t* env) {
  intptr_t x_109; intptr_t y_110; intptr_t x_370;
  x_109 = env[1];
  y_110 = env[2];
  x_370 = fn0_lt_368(x_109, y_110);
  return x_370;
}

intptr_t fn0_pred_371(intptr_t __114) {
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

intptr_t fn1_pred_372(intptr_t* env) {
  intptr_t __114; intptr_t x_373;
  __114 = env[1];
  x_373 = fn0_pred_371(__114);
  return x_373;
}

intptr_t fn0_add_374(intptr_t __119, intptr_t __120) {
  intptr_t x_121; intptr_t x_122; intptr_t n_123; intptr_t x_124;
  intptr_t x_125;
  switch(__119){
    case 6: //zero_6
      x_121 = __120;
      break;
    default:
      n_123 = getbox(__119, 0);
      x_124 = fn0_add_374(n_123, __120);
      x_125 = mkbox(7, 1); //succ_7
      setbox(x_125, x_124, 0);
      x_122 = x_125;
      x_121 = x_122;
      break;
  }
  return x_121;
}

intptr_t fn1_add_375(intptr_t* env) {
  intptr_t __119; intptr_t __120; intptr_t x_376;
  __119 = env[1];
  __120 = env[2];
  x_376 = fn0_add_374(__119, __120);
  return x_376;
}

intptr_t fn0_sub_377(intptr_t __127, intptr_t __128) {
  intptr_t x_129; intptr_t x_130; intptr_t n_131; intptr_t x_132;
  intptr_t x_133;
  switch(__128){
    case 6: //zero_6
      x_129 = __127;
      break;
    default:
      n_131 = getbox(__128, 0);
      x_133 = fn0_pred_371(__127);
      x_132 = fn0_sub_377(x_133, n_131);
      x_130 = x_132;
      x_129 = x_130;
      break;
  }
  return x_129;
}

intptr_t fn1_sub_378(intptr_t* env) {
  intptr_t __127; intptr_t __128; intptr_t x_379;
  __127 = env[1];
  __128 = env[2];
  x_379 = fn0_sub_377(__127, __128);
  return x_379;
}

intptr_t fn0_mul_380(intptr_t __135, intptr_t __136) {
  intptr_t x_137; intptr_t x_138; intptr_t n_139; intptr_t x_140;
  intptr_t x_141;
  switch(__135){
    case 6: //zero_6
      x_137 = 6;
      break;
    default:
      n_139 = getbox(__135, 0);
      x_141 = fn0_mul_380(n_139, __136);
      x_140 = fn0_add_374(__136, x_141);
      x_138 = x_140;
      x_137 = x_138;
      break;
  }
  return x_137;
}

intptr_t fn1_mul_381(intptr_t* env) {
  intptr_t __135; intptr_t __136; intptr_t x_382;
  __135 = env[1];
  __136 = env[2];
  x_382 = fn0_mul_380(__135, __136);
  return x_382;
}

intptr_t fn0_div_383(intptr_t x_143, intptr_t y_144) {
  intptr_t x_145; intptr_t x_146; intptr_t loop_147; intptr_t x_148;
  intptr_t x_161; intptr_t x_389; intptr_t x_390;
  x_146 = fn0_lt_368(x_143, y_144);
  switch(x_146){
    case 4: //true_4
      x_145 = 6;
      break;
    case 5: //false_5
      x_148 = mkclo(fn1_loop_385, 2, 2);
      setclo(x_148, pred_113, 1);
      setclo(x_148, sub_126, 2);
      loop_147 = x_148;
      x_389 = appc(loop_147, x_143);
      x_390 = appc(x_389, y_144);
      x_161 = x_390;
      x_145 = x_161;
      break;
  }
  return x_145;
}

intptr_t fn1_div_384(intptr_t* env) {
  intptr_t x_143; intptr_t y_144; intptr_t x_392;
  x_143 = env[1];
  y_144 = env[2];
  x_392 = fn0_div_383(x_143, y_144);
  return x_392;
}

intptr_t fn0_rem_393(intptr_t x_163, intptr_t y_164) {
  intptr_t x_165; intptr_t x_166; intptr_t x_167;
  x_167 = fn0_div_383(x_163, y_164);
  x_166 = fn0_mul_380(x_167, y_164);
  x_165 = fn0_sub_377(x_163, x_166);
  return x_165;
}

intptr_t fn1_rem_394(intptr_t* env) {
  intptr_t x_163; intptr_t y_164; intptr_t x_395;
  x_163 = env[1];
  y_164 = env[2];
  x_395 = fn0_rem_393(x_163, y_164);
  return x_395;
}

intptr_t fn0_free_listUU_396(intptr_t A_169, intptr_t f_170, intptr_t __171) {
  intptr_t x_172; intptr_t x_173; intptr_t hd_174; intptr_t tl_175;
  intptr_t __176; intptr_t x_177; intptr_t x_178; intptr_t x_398;
  switch(__171){
    case 29: //nilUU_29
      x_172 = 22;
      break;
    default:
      hd_174 = getbox(__171, 0);
      tl_175 = getbox(__171, 1);
      x_398 = appc(f_170, hd_174);
      x_177 = x_398;
      __176 = x_177;
      x_178 = fn0_free_listUU_396(nothing, f_170, tl_175);
      x_173 = x_178;
      x_172 = x_173;
      break;
  }
  return x_172;
}

intptr_t fn1_free_listUU_397(intptr_t* env) {
  intptr_t A_169; intptr_t f_170; intptr_t __171; intptr_t x_400;
  A_169 = env[1];
  f_170 = env[2];
  __171 = env[3];
  x_400 = fn0_free_listUU_396(A_169, f_170, __171);
  return x_400;
}

intptr_t fn0_free_listUL_401(intptr_t A_180, intptr_t f_181, intptr_t __182) {
  intptr_t x_183; intptr_t x_184; intptr_t hd_185; intptr_t tl_186;
  intptr_t __187; intptr_t x_188; intptr_t x_189; intptr_t x_403;
  switch(__182){
    case 27: //nilUL_27
      x_183 = 22;
      break;
    default:
      hd_185 = getbox(__182, 0);
      tl_186 = getbox(__182, 1);
      x_403 = appc(f_181, hd_185);
      x_188 = x_403;
      __187 = x_188;
      x_189 = fn0_free_listUL_401(nothing, f_181, tl_186);
      x_184 = x_189;
      ffree(__182);
      x_183 = x_184;
      break;
  }
  return x_183;
}

intptr_t fn1_free_listUL_402(intptr_t* env) {
  intptr_t A_180; intptr_t f_181; intptr_t __182; intptr_t x_405;
  A_180 = env[1];
  f_181 = env[2];
  __182 = env[3];
  x_405 = fn0_free_listUL_401(A_180, f_181, __182);
  return x_405;
}

intptr_t fn0_free_listLL_406(intptr_t A_191, intptr_t f_192, intptr_t __193) {
  intptr_t x_194; intptr_t x_195; intptr_t hd_196; intptr_t tl_197;
  intptr_t __198; intptr_t x_199; intptr_t x_200; intptr_t x_408;
  switch(__193){
    case 23: //nilLL_23
      x_194 = 22;
      break;
    default:
      hd_196 = getbox(__193, 0);
      tl_197 = getbox(__193, 1);
      x_408 = appc(f_192, hd_196);
      x_199 = x_408;
      __198 = x_199;
      x_200 = fn0_free_listLL_406(nothing, f_192, tl_197);
      x_195 = x_200;
      ffree(__193);
      x_194 = x_195;
      break;
  }
  return x_194;
}

intptr_t fn1_free_listLL_407(intptr_t* env) {
  intptr_t A_191; intptr_t f_192; intptr_t __193; intptr_t x_410;
  A_191 = env[1];
  f_192 = env[2];
  __193 = env[3];
  x_410 = fn0_free_listLL_406(A_191, f_192, __193);
  return x_410;
}

intptr_t fn0_pow_411(intptr_t x_202, intptr_t y_203) {
  intptr_t loop_204; intptr_t x_205; intptr_t x_214; intptr_t x_417;
  intptr_t x_418;
  x_205 = mkclo(fn1_loop_413, 1, 2);
  setclo(x_205, x_202, 1);
  loop_204 = x_205;
  x_417 = appc(loop_204, 1);
  x_418 = appc(x_417, y_203);
  x_214 = x_418;
  return x_214;
}

intptr_t fn1_pow_412(intptr_t* env) {
  intptr_t x_202; intptr_t y_203; intptr_t x_420;
  x_202 = env[1];
  y_203 = env[2];
  x_420 = fn0_pow_411(x_202, y_203);
  return x_420;
}

intptr_t fn0_powm_421(intptr_t x_216, intptr_t y_217, intptr_t m_218) {
  intptr_t loop_219; intptr_t x_220; intptr_t x_230; intptr_t x_427;
  intptr_t x_428;
  x_220 = mkclo(fn1_loop_423, 2, 2);
  setclo(x_220, x_216, 1);
  setclo(x_220, m_218, 2);
  loop_219 = x_220;
  x_427 = appc(loop_219, 1);
  x_428 = appc(x_427, y_217);
  x_230 = x_428;
  return x_230;
}

intptr_t fn1_powm_422(intptr_t* env) {
  intptr_t x_216; intptr_t y_217; intptr_t m_218; intptr_t x_430;
  x_216 = env[1];
  y_217 = env[2];
  m_218 = env[3];
  x_430 = fn0_powm_421(x_216, y_217, m_218);
  return x_430;
}

intptr_t fn0_ord_431(intptr_t c_232) {
  intptr_t x_233;
  x_233 = __ord__(c_232);
  return x_233;
}

intptr_t fn1_ord_432(intptr_t* env) {
  intptr_t c_232; intptr_t x_433;
  c_232 = env[1];
  x_433 = fn0_ord_431(c_232);
  return x_433;
}

intptr_t fn0_chr_434(intptr_t i_235) {
  intptr_t x_236;
  x_236 = __chr__(i_235);
  return x_236;
}

intptr_t fn1_chr_435(intptr_t* env) {
  intptr_t i_235; intptr_t x_436;
  i_235 = env[1];
  x_436 = fn0_chr_434(i_235);
  return x_436;
}

intptr_t fn0_str_437(intptr_t c_238) {
  intptr_t x_239; intptr_t x_240;
  x_240 = __str__("");
  x_239 = __push__(x_240, c_238);
  return x_239;
}

intptr_t fn1_str_438(intptr_t* env) {
  intptr_t c_238; intptr_t x_439;
  c_238 = env[1];
  x_439 = fn0_str_437(c_238);
  return x_439;
}

intptr_t fn0_strlen_440(intptr_t s_242) {
  intptr_t x_243;
  x_243 = __size__(s_242);
  return x_243;
}

intptr_t fn1_strlen_441(intptr_t* env) {
  intptr_t s_242; intptr_t x_442;
  s_242 = env[1];
  x_442 = fn0_strlen_440(s_242);
  return x_442;
}

intptr_t fn0_string_of_int_443(intptr_t i_245) {
  intptr_t aux_246; intptr_t x_247; intptr_t x_265; intptr_t x_266;
  intptr_t x_267; intptr_t x_268; intptr_t x_269; intptr_t x_270;
  intptr_t x_271; intptr_t x_448; intptr_t x_450;
  x_247 = mkclo(fn1_aux_445, 3, 1);
  setclo(x_247, ord_231, 1);
  setclo(x_247, chr_234, 2);
  setclo(x_247, str_237, 3);
  aux_246 = x_247;
  x_266 = __lte__(0, i_245);
  switch(x_266){
    case 4: //true_4
      x_448 = appc(aux_246, i_245);
      x_267 = x_448;
      x_265 = x_267;
      break;
    case 5: //false_5
      x_269 = __str__("~");
      x_271 = __neg__(i_245);
      x_450 = appc(aux_246, x_271);
      x_270 = x_450;
      x_268 = __cat__(x_269, x_270);
      x_265 = x_268;
      break;
  }
  return x_265;
}

intptr_t fn1_string_of_int_444(intptr_t* env) {
  intptr_t i_245; intptr_t x_452;
  i_245 = env[1];
  x_452 = fn0_string_of_int_443(i_245);
  return x_452;
}

intptr_t fn0_hd_vec1_453(intptr_t A_273, intptr_t n_274, intptr_t __275) {
  intptr_t x_276; intptr_t hd_277;
  hd_277 = getbox(__275, 0);
  x_276 = hd_277;
  return x_276;
}

intptr_t fn1_hd_vec1_454(intptr_t* env) {
  intptr_t A_273; intptr_t n_274; intptr_t __275; intptr_t x_455;
  A_273 = env[1];
  n_274 = env[2];
  __275 = env[3];
  x_455 = fn0_hd_vec1_453(A_273, n_274, __275);
  return x_455;
}

intptr_t fn0_hd_vec2_456(intptr_t A_280, intptr_t n_281, intptr_t xs_282) {
  intptr_t x_283; intptr_t hd_284;
  hd_284 = getbox(xs_282, 0);
  x_283 = hd_284;
  return x_283;
}

intptr_t fn1_hd_vec2_457(intptr_t* env) {
  intptr_t A_280; intptr_t n_281; intptr_t xs_282; intptr_t x_458;
  A_280 = env[1];
  n_281 = env[2];
  xs_282 = env[3];
  x_458 = fn0_hd_vec2_456(A_280, n_281, xs_282);
  return x_458;
}

intptr_t fn0_hd_vec3_459(intptr_t A_287, intptr_t n_288, intptr_t xs_289) {
  intptr_t x_290; intptr_t hd_291;
  hd_291 = getbox(xs_289, 0);
  x_290 = hd_291;
  return x_290;
}

intptr_t fn1_hd_vec3_460(intptr_t* env) {
  intptr_t A_287; intptr_t n_288; intptr_t xs_289; intptr_t x_461;
  A_287 = env[1];
  n_288 = env[2];
  xs_289 = env[3];
  x_461 = fn0_hd_vec3_459(A_287, n_288, xs_289);
  return x_461;
}

intptr_t fn0_vlength_462(intptr_t A_294, intptr_t n_295, intptr_t __296) {
  intptr_t x_297; intptr_t x_298; intptr_t tl_300; intptr_t x_301;
  intptr_t x_302;
  switch(__296){
    case 45: //vnilU_45
      x_297 = 6;
      break;
    default:
      tl_300 = getbox(__296, 1);
      x_301 = fn0_vlength_462(nothing, nothing, tl_300);
      x_302 = mkbox(7, 1); //succ_7
      setbox(x_302, x_301, 0);
      x_298 = x_302;
      x_297 = x_298;
      break;
  }
  return x_297;
}

intptr_t fn1_vlength_463(intptr_t* env) {
  intptr_t A_294; intptr_t n_295; intptr_t __296; intptr_t x_464;
  A_294 = env[1];
  n_295 = env[2];
  __296 = env[3];
  x_464 = fn0_vlength_462(A_294, n_295, __296);
  return x_464;
}

intptr_t fn1_aux_445(intptr_t* env) {
  intptr_t ord_231; intptr_t chr_234; intptr_t str_237; intptr_t aux_248;
  intptr_t i_249; intptr_t x_250; intptr_t x_251; intptr_t r_252;
  intptr_t x_253; intptr_t i_254; intptr_t x_255; intptr_t x_256;
  intptr_t x_257; intptr_t x_258; intptr_t x_259; intptr_t x_260;
  intptr_t x_261; intptr_t x_262; intptr_t x_263; intptr_t x_264;
  intptr_t x_446;
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
      x_446 = appc(aux_248, i_254);
      x_257 = x_446;
      x_260 = fn0_ord_431('0');
      x_259 = __add__(r_252, x_260);
      x_258 = fn0_chr_434(x_259);
      x_256 = __push__(x_257, x_258);
      x_250 = x_256;
      break;
    case 5: //false_5
      x_264 = fn0_ord_431('0');
      x_263 = __add__(i_249, x_264);
      x_262 = fn0_chr_434(x_263);
      x_261 = fn0_str_437(x_262);
      x_250 = x_261;
      break;
  }
  return x_250;
}

intptr_t fn1_loop_423(intptr_t* env) {
  intptr_t x_216; intptr_t m_218; intptr_t loop_221; intptr_t acc_222;
  intptr_t y_223; intptr_t x_224; intptr_t x_225; intptr_t x_226;
  intptr_t x_227; intptr_t x_228; intptr_t x_229; intptr_t x_424;
  intptr_t x_425;
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
      x_424 = appc(loop_221, x_227);
      x_425 = appc(x_424, x_229);
      x_226 = x_425;
      x_224 = x_226;
      break;
  }
  return x_224;
}

intptr_t fn1_loop_413(intptr_t* env) {
  intptr_t x_202; intptr_t loop_206; intptr_t acc_207; intptr_t y_208;
  intptr_t x_209; intptr_t x_210; intptr_t x_211; intptr_t x_212;
  intptr_t x_213; intptr_t x_414; intptr_t x_415;
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
      x_414 = appc(loop_206, x_212);
      x_415 = appc(x_414, x_213);
      x_211 = x_415;
      x_209 = x_211;
      break;
  }
  return x_209;
}

intptr_t fn1_loop_385(intptr_t* env) {
  intptr_t pred_113; intptr_t sub_126; intptr_t loop_149; intptr_t x_150;
  intptr_t y_151; intptr_t x_152; intptr_t x_153; intptr_t x_154;
  intptr_t x_155; intptr_t x_156; intptr_t x_157; intptr_t n_158;
  intptr_t x_159; intptr_t x_160; intptr_t x_386; intptr_t x_387;
  loop_149 = env[0];
  pred_113 = env[1];
  sub_126 = env[2];
  x_150 = env[3];
  y_151 = env[4];
  x_154 = fn0_pred_371(y_151);
  x_153 = fn0_sub_377(x_150, x_154);
  switch(x_153){
    case 6: //zero_6
      x_152 = 6;
      break;
    default:
      x_157 = fn0_pred_371(y_151);
      x_156 = fn0_sub_377(x_150, x_157);
      n_158 = getbox(x_156, 0);
      x_386 = appc(loop_149, n_158);
      x_387 = appc(x_386, y_151);
      x_159 = x_387;
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
  intptr_t x_304; intptr_t x_306; intptr_t x_308; intptr_t x_310;
  idU_1 = mkclo(fn1_idU_312, 0, 2);
  idL_4 = mkclo(fn1_idL_315, 0, 2);
  rwlUU_7 = mkclo(fn1_rwlUU_318, 0, 6);
  rwlUL_14 = mkclo(fn1_rwlUL_321, 0, 6);
  rwlLU_21 = mkclo(fn1_rwlLU_324, 0, 6);
  rwlLL_28 = mkclo(fn1_rwlLL_327, 0, 6);
  rwrUU_35 = mkclo(fn1_rwrUU_330, 0, 6);
  rwrUL_42 = mkclo(fn1_rwrUL_333, 0, 6);
  rwrLU_49 = mkclo(fn1_rwrLU_336, 0, 6);
  rwrLL_56 = mkclo(fn1_rwrLL_339, 0, 6);
  sing_elimUU_63 = mkclo(fn1_sing_elimUU_342, 0, 3);
  sing_elimUL_67 = mkclo(fn1_sing_elimUL_345, 0, 3);
  sing_elimLU_71 = mkclo(fn1_sing_elimLU_348, 0, 3);
  sing_elimLL_75 = mkclo(fn1_sing_elimLL_351, 0, 3);
  not_79 = mkclo(fn1_not_354, 0, 1);
  and_82 = mkclo(fn1_and_357, 0, 2);
  or_87 = mkclo(fn1_or_360, 0, 2);
  xor_92 = mkclo(fn1_xor_363, 0, 2);
  lte_98 = mkclo(fn1_lte_366, 0, 2);
  lt_108 = mkclo(fn1_lt_369, 0, 2);
  pred_113 = mkclo(fn1_pred_372, 0, 1);
  add_118 = mkclo(fn1_add_375, 0, 2);
  sub_126 = mkclo(fn1_sub_378, 0, 2);
  mul_134 = mkclo(fn1_mul_381, 0, 2);
  div_142 = mkclo(fn1_div_384, 0, 2);
  rem_162 = mkclo(fn1_rem_394, 0, 2);
  free_listUU_168 = mkclo(fn1_free_listUU_397, 0, 3);
  free_listUL_179 = mkclo(fn1_free_listUL_402, 0, 3);
  free_listLL_190 = mkclo(fn1_free_listLL_407, 0, 3);
  pow_201 = mkclo(fn1_pow_412, 0, 2);
  powm_215 = mkclo(fn1_powm_422, 0, 3);
  ord_231 = mkclo(fn1_ord_432, 0, 1);
  chr_234 = mkclo(fn1_chr_435, 0, 1);
  str_237 = mkclo(fn1_str_438, 0, 1);
  strlen_241 = mkclo(fn1_strlen_441, 0, 1);
  string_of_int_244 = mkclo(fn1_string_of_int_444, 0, 1);
  hd_vec1_272 = mkclo(fn1_hd_vec1_454, 0, 3);
  hd_vec2_279 = mkclo(fn1_hd_vec2_457, 0, 3);
  hd_vec3_286 = mkclo(fn1_hd_vec3_460, 0, 3);
  vlength_293 = mkclo(fn1_vlength_463, 0, 3);
  x_304 = mkbox(46, 2); //vconsU_46
  setbox(x_304, 6, 0);
  setbox(x_304, 45, 1);
  xs_303 = x_304;
  x_306 = fn0_hd_vec1_453(nothing, nothing, xs_303);
  x_305 = x_306;
  x_308 = fn0_hd_vec2_456(nothing, nothing, xs_303);
  y_307 = x_308;
  x_310 = fn0_hd_vec3_459(nothing, nothing, xs_303);
  z_309 = x_310;
  end_run();
}

