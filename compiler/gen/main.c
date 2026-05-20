#include "main.h"

tll_object* idU_1; tll_object* idL_4; tll_object* rwlUU_7;
tll_object* rwlUL_14; tll_object* rwlLU_21; tll_object* rwlLL_28;
tll_object* rwrUU_35; tll_object* rwrUL_42; tll_object* rwrLU_49;
tll_object* rwrLL_56; tll_object* sing_elimUU_63; tll_object* sing_elimUL_67;
tll_object* sing_elimLU_71; tll_object* sing_elimLL_75; tll_object* not_79;
tll_object* and_82; tll_object* or_87; tll_object* xor_92;
tll_object* string_of_bool_98; tll_object* lte_103; tll_object* lt_113;
tll_object* pred_118; tll_object* add_123; tll_object* sub_131;
tll_object* mul_139; tll_object* div_147; tll_object* rem_167;
tll_object* rconsUU_173; tll_object* rconsUL_184; tll_object* rconsLL_195;
tll_object* free_listUU_206; tll_object* free_listUL_217;
tll_object* free_listLL_228; tll_object* pow_239; tll_object* powm_253;
tll_object* ord_269; tll_object* chr_272; tll_object* str_275;
tll_object* strlen_279; tll_object* string_of_int_282;
tll_object* splitU_310; tll_object* splitL_330; tll_object* mergeU_350;
tll_object* mergeL_370; tll_object* msortU_390; tll_object* msortL_410;
tll_object* cmsort_workerU_430; tll_object* cmsort_workerL_502;
tll_object* cmsortU_574; tll_object* cmsortL_590; tll_object* mklistU_606;
tll_object* mklistL_613; tll_object* list_lenU_620;
tll_object* list_lenL_628; tll_object* print_listU_636;
tll_object* print_listL_654;

tll_object* fn0_idU_682(tll_object* A_2, tll_object* m_3) {
  
  
  return m_3;
}

tll_object* fn1_idU_683(tll_object* env[]) {
  tll_object* A_2; tll_object* m_3; tll_object* x_684;
  A_2 = env[1];
  m_3 = env[2];
  x_684 = fn0_idU_682(A_2, m_3);
  return x_684;
}

tll_object* fn0_idL_685(tll_object* A_5, tll_object* m_6) {
  
  
  return m_6;
}

tll_object* fn1_idL_686(tll_object* env[]) {
  tll_object* A_5; tll_object* m_6; tll_object* x_687;
  A_5 = env[1];
  m_6 = env[2];
  x_687 = fn0_idL_685(A_5, m_6);
  return x_687;
}

tll_object* fn0_rwlUU_688(tll_object* A_8, tll_object* m_9, tll_object* n_10, tll_object* B_11, tll_object* __12, tll_object* __13) {
  
  
  return __13;
}

tll_object* fn1_rwlUU_689(tll_object* env[]) {
  tll_object* A_8; tll_object* m_9; tll_object* n_10; tll_object* B_11;
  tll_object* __12; tll_object* __13; tll_object* x_690;
  A_8 = env[1];
  m_9 = env[2];
  n_10 = env[3];
  B_11 = env[4];
  __12 = env[5];
  __13 = env[6];
  x_690 = fn0_rwlUU_688(A_8, m_9, n_10, B_11, __12, __13);
  return x_690;
}

tll_object* fn0_rwlUL_691(tll_object* A_15, tll_object* m_16, tll_object* n_17, tll_object* B_18, tll_object* __19, tll_object* __20) {
  
  
  return __20;
}

tll_object* fn1_rwlUL_692(tll_object* env[]) {
  tll_object* A_15; tll_object* m_16; tll_object* n_17; tll_object* B_18;
  tll_object* __19; tll_object* __20; tll_object* x_693;
  A_15 = env[1];
  m_16 = env[2];
  n_17 = env[3];
  B_18 = env[4];
  __19 = env[5];
  __20 = env[6];
  x_693 = fn0_rwlUL_691(A_15, m_16, n_17, B_18, __19, __20);
  return x_693;
}

tll_object* fn0_rwlLU_694(tll_object* A_22, tll_object* m_23, tll_object* n_24, tll_object* B_25, tll_object* __26, tll_object* __27) {
  
  
  return __27;
}

tll_object* fn1_rwlLU_695(tll_object* env[]) {
  tll_object* A_22; tll_object* m_23; tll_object* n_24; tll_object* B_25;
  tll_object* __26; tll_object* __27; tll_object* x_696;
  A_22 = env[1];
  m_23 = env[2];
  n_24 = env[3];
  B_25 = env[4];
  __26 = env[5];
  __27 = env[6];
  x_696 = fn0_rwlLU_694(A_22, m_23, n_24, B_25, __26, __27);
  return x_696;
}

tll_object* fn0_rwlLL_697(tll_object* A_29, tll_object* m_30, tll_object* n_31, tll_object* B_32, tll_object* __33, tll_object* __34) {
  
  
  return __34;
}

tll_object* fn1_rwlLL_698(tll_object* env[]) {
  tll_object* A_29; tll_object* m_30; tll_object* n_31; tll_object* B_32;
  tll_object* __33; tll_object* __34; tll_object* x_699;
  A_29 = env[1];
  m_30 = env[2];
  n_31 = env[3];
  B_32 = env[4];
  __33 = env[5];
  __34 = env[6];
  x_699 = fn0_rwlLL_697(A_29, m_30, n_31, B_32, __33, __34);
  return x_699;
}

tll_object* fn0_rwrUU_700(tll_object* A_36, tll_object* m_37, tll_object* n_38, tll_object* B_39, tll_object* __40, tll_object* __41) {
  
  
  return __41;
}

tll_object* fn1_rwrUU_701(tll_object* env[]) {
  tll_object* A_36; tll_object* m_37; tll_object* n_38; tll_object* B_39;
  tll_object* __40; tll_object* __41; tll_object* x_702;
  A_36 = env[1];
  m_37 = env[2];
  n_38 = env[3];
  B_39 = env[4];
  __40 = env[5];
  __41 = env[6];
  x_702 = fn0_rwrUU_700(A_36, m_37, n_38, B_39, __40, __41);
  return x_702;
}

tll_object* fn0_rwrUL_703(tll_object* A_43, tll_object* m_44, tll_object* n_45, tll_object* B_46, tll_object* __47, tll_object* __48) {
  
  
  return __48;
}

tll_object* fn1_rwrUL_704(tll_object* env[]) {
  tll_object* A_43; tll_object* m_44; tll_object* n_45; tll_object* B_46;
  tll_object* __47; tll_object* __48; tll_object* x_705;
  A_43 = env[1];
  m_44 = env[2];
  n_45 = env[3];
  B_46 = env[4];
  __47 = env[5];
  __48 = env[6];
  x_705 = fn0_rwrUL_703(A_43, m_44, n_45, B_46, __47, __48);
  return x_705;
}

tll_object* fn0_rwrLU_706(tll_object* A_50, tll_object* m_51, tll_object* n_52, tll_object* B_53, tll_object* __54, tll_object* __55) {
  
  
  return __55;
}

tll_object* fn1_rwrLU_707(tll_object* env[]) {
  tll_object* A_50; tll_object* m_51; tll_object* n_52; tll_object* B_53;
  tll_object* __54; tll_object* __55; tll_object* x_708;
  A_50 = env[1];
  m_51 = env[2];
  n_52 = env[3];
  B_53 = env[4];
  __54 = env[5];
  __55 = env[6];
  x_708 = fn0_rwrLU_706(A_50, m_51, n_52, B_53, __54, __55);
  return x_708;
}

tll_object* fn0_rwrLL_709(tll_object* A_57, tll_object* m_58, tll_object* n_59, tll_object* B_60, tll_object* __61, tll_object* __62) {
  
  
  return __62;
}

tll_object* fn1_rwrLL_710(tll_object* env[]) {
  tll_object* A_57; tll_object* m_58; tll_object* n_59; tll_object* B_60;
  tll_object* __61; tll_object* __62; tll_object* x_711;
  A_57 = env[1];
  m_58 = env[2];
  n_59 = env[3];
  B_60 = env[4];
  __61 = env[5];
  __62 = env[6];
  x_711 = fn0_rwrLL_709(A_57, m_58, n_59, B_60, __61, __62);
  return x_711;
}

tll_object* fn0_sing_elimUU_712(tll_object* A_64, tll_object* x_65, tll_object* __66) {
  
  
  return __66;
}

tll_object* fn1_sing_elimUU_713(tll_object* env[]) {
  tll_object* A_64; tll_object* x_65; tll_object* __66; tll_object* x_714;
  A_64 = env[1];
  x_65 = env[2];
  __66 = env[3];
  x_714 = fn0_sing_elimUU_712(A_64, x_65, __66);
  return x_714;
}

tll_object* fn0_sing_elimUL_715(tll_object* A_68, tll_object* x_69, tll_object* __70) {
  
  
  return __70;
}

tll_object* fn1_sing_elimUL_716(tll_object* env[]) {
  tll_object* A_68; tll_object* x_69; tll_object* __70; tll_object* x_717;
  A_68 = env[1];
  x_69 = env[2];
  __70 = env[3];
  x_717 = fn0_sing_elimUL_715(A_68, x_69, __70);
  return x_717;
}

tll_object* fn0_sing_elimLU_718(tll_object* A_72, tll_object* x_73, tll_object* __74) {
  
  absurd();
  return NULL;
}

tll_object* fn1_sing_elimLU_719(tll_object* env[]) {
  tll_object* A_72; tll_object* x_73; tll_object* __74; tll_object* x_720;
  A_72 = env[1];
  x_73 = env[2];
  __74 = env[3];
  x_720 = fn0_sing_elimLU_718(A_72, x_73, __74);
  return x_720;
}

tll_object* fn0_sing_elimLL_721(tll_object* A_76, tll_object* x_77, tll_object* __78) {
  
  
  return __78;
}

tll_object* fn1_sing_elimLL_722(tll_object* env[]) {
  tll_object* A_76; tll_object* x_77; tll_object* __78; tll_object* x_723;
  A_76 = env[1];
  x_77 = env[2];
  __78 = env[3];
  x_723 = fn0_sing_elimLL_721(A_76, x_77, __78);
  return x_723;
}

tll_object* fn0_not_724(tll_object* __80) {
  tll_object* x_81;
  switch(tll_unbox(__80)){
    case 4: //true_4
      x_81 = tll_box(5);
      break;
    case 5: //false_5
      x_81 = tll_box(4);
      break;
  }
  return x_81;
}

tll_object* fn1_not_725(tll_object* env[]) {
  tll_object* __80; tll_object* x_726;
  __80 = env[1];
  x_726 = fn0_not_724(__80);
  return x_726;
}

tll_object* fn0_and_727(tll_object* __83, tll_object* __84) {
  tll_object* x_85; tll_object* x_86;
  switch(tll_unbox(__83)){
    case 4: //true_4
      switch(tll_unbox(__84)){
        case 4: //true_4
          x_86 = tll_box(4);
          break;
        case 5: //false_5
          x_86 = tll_box(5);
          break;
      }
      x_85 = x_86;
      break;
    case 5: //false_5
      x_85 = tll_box(5);
      break;
  }
  return x_85;
}

tll_object* fn1_and_728(tll_object* env[]) {
  tll_object* __83; tll_object* __84; tll_object* x_729;
  __83 = env[1];
  __84 = env[2];
  x_729 = fn0_and_727(__83, __84);
  return x_729;
}

tll_object* fn0_or_730(tll_object* __88, tll_object* __89) {
  tll_object* x_90; tll_object* x_91;
  switch(tll_unbox(__88)){
    case 4: //true_4
      x_90 = tll_box(4);
      break;
    case 5: //false_5
      switch(tll_unbox(__89)){
        case 4: //true_4
          x_91 = tll_box(4);
          break;
        case 5: //false_5
          x_91 = tll_box(5);
          break;
      }
      x_90 = x_91;
      break;
  }
  return x_90;
}

tll_object* fn1_or_731(tll_object* env[]) {
  tll_object* __88; tll_object* __89; tll_object* x_732;
  __88 = env[1];
  __89 = env[2];
  x_732 = fn0_or_730(__88, __89);
  return x_732;
}

tll_object* fn0_xor_733(tll_object* __93, tll_object* __94) {
  tll_object* x_95; tll_object* x_96; tll_object* x_97;
  switch(tll_unbox(__93)){
    case 4: //true_4
      switch(tll_unbox(__94)){
        case 4: //true_4
          x_96 = tll_box(5);
          break;
        case 5: //false_5
          x_96 = tll_box(4);
          break;
      }
      x_95 = x_96;
      break;
    case 5: //false_5
      switch(tll_unbox(__94)){
        case 4: //true_4
          x_97 = tll_box(4);
          break;
        case 5: //false_5
          x_97 = tll_box(5);
          break;
      }
      x_95 = x_97;
      break;
  }
  return x_95;
}

tll_object* fn1_xor_734(tll_object* env[]) {
  tll_object* __93; tll_object* __94; tll_object* x_735;
  __93 = env[1];
  __94 = env[2];
  x_735 = fn0_xor_733(__93, __94);
  return x_735;
}

tll_object* fn0_string_of_bool_736(tll_object* __99) {
  tll_object* x_100; tll_object* x_101; tll_object* x_102;
  switch(tll_unbox(__99)){
    case 4: //true_4
      x_101 = tll_string_make("true");
      x_100 = x_101;
      break;
    case 5: //false_5
      x_102 = tll_string_make("false");
      x_100 = x_102;
      break;
  }
  return x_100;
}

tll_object* fn1_string_of_bool_737(tll_object* env[]) {
  tll_object* __99; tll_object* x_738;
  __99 = env[1];
  x_738 = fn0_string_of_bool_736(__99);
  return x_738;
}

tll_object* fn0_lte_739(tll_object* __104, tll_object* __105) {
  tll_object* x_106; tll_object* x_107; tll_object* n_108; tll_object* x_109;
  tll_object* x_110; tll_object* n_111; tll_object* x_112;
  switch(tll_unbox(__104)){
    case 6: //zero_6
      x_106 = tll_box(4);
      break;
    default:
      n_108 = tll_ctor_get(__104, 0);
      switch(tll_unbox(__105)){
        case 6: //zero_6
          x_109 = tll_box(5);
          break;
        default:
          n_111 = tll_ctor_get(__105, 0);
          x_112 = fn0_lte_739(n_108, n_111);
          x_110 = x_112;
          x_109 = x_110;
          break;
      }
      x_107 = x_109;
      x_106 = x_107;
      break;
  }
  return x_106;
}

tll_object* fn1_lte_740(tll_object* env[]) {
  tll_object* __104; tll_object* __105; tll_object* x_741;
  __104 = env[1];
  __105 = env[2];
  x_741 = fn0_lte_739(__104, __105);
  return x_741;
}

tll_object* fn0_lt_742(tll_object* x_114, tll_object* y_115) {
  tll_object* x_116; tll_object* x_117;
  x_117 = tll_ctor_make(7, 1); //succ_7
  tll_ctor_set(x_117, x_114, 0);
  x_116 = fn0_lte_739(x_117, y_115);
  return x_116;
}

tll_object* fn1_lt_743(tll_object* env[]) {
  tll_object* x_114; tll_object* y_115; tll_object* x_744;
  x_114 = env[1];
  y_115 = env[2];
  x_744 = fn0_lt_742(x_114, y_115);
  return x_744;
}

tll_object* fn0_pred_745(tll_object* __119) {
  tll_object* x_120; tll_object* x_121; tll_object* n_122;
  switch(tll_unbox(__119)){
    case 6: //zero_6
      x_120 = tll_box(6);
      break;
    default:
      n_122 = tll_ctor_get(__119, 0);
      x_121 = n_122;
      x_120 = x_121;
      break;
  }
  return x_120;
}

tll_object* fn1_pred_746(tll_object* env[]) {
  tll_object* __119; tll_object* x_747;
  __119 = env[1];
  x_747 = fn0_pred_745(__119);
  return x_747;
}

tll_object* fn0_add_748(tll_object* __124, tll_object* __125) {
  tll_object* x_126; tll_object* x_127; tll_object* n_128; tll_object* x_129;
  tll_object* x_130;
  switch(tll_unbox(__124)){
    case 6: //zero_6
      x_126 = __125;
      break;
    default:
      n_128 = tll_ctor_get(__124, 0);
      x_129 = fn0_add_748(n_128, __125);
      x_130 = tll_ctor_make(7, 1); //succ_7
      tll_ctor_set(x_130, x_129, 0);
      x_127 = x_130;
      x_126 = x_127;
      break;
  }
  return x_126;
}

tll_object* fn1_add_749(tll_object* env[]) {
  tll_object* __124; tll_object* __125; tll_object* x_750;
  __124 = env[1];
  __125 = env[2];
  x_750 = fn0_add_748(__124, __125);
  return x_750;
}

tll_object* fn0_sub_751(tll_object* __132, tll_object* __133) {
  tll_object* x_134; tll_object* x_135; tll_object* n_136; tll_object* x_137;
  tll_object* x_138;
  switch(tll_unbox(__133)){
    case 6: //zero_6
      x_134 = __132;
      break;
    default:
      n_136 = tll_ctor_get(__133, 0);
      x_138 = fn0_pred_745(__132);
      x_137 = fn0_sub_751(x_138, n_136);
      x_135 = x_137;
      x_134 = x_135;
      break;
  }
  return x_134;
}

tll_object* fn1_sub_752(tll_object* env[]) {
  tll_object* __132; tll_object* __133; tll_object* x_753;
  __132 = env[1];
  __133 = env[2];
  x_753 = fn0_sub_751(__132, __133);
  return x_753;
}

tll_object* fn0_mul_754(tll_object* __140, tll_object* __141) {
  tll_object* x_142; tll_object* x_143; tll_object* n_144; tll_object* x_145;
  tll_object* x_146;
  switch(tll_unbox(__140)){
    case 6: //zero_6
      x_142 = tll_box(6);
      break;
    default:
      n_144 = tll_ctor_get(__140, 0);
      x_146 = fn0_mul_754(n_144, __141);
      x_145 = fn0_add_748(__141, x_146);
      x_143 = x_145;
      x_142 = x_143;
      break;
  }
  return x_142;
}

tll_object* fn1_mul_755(tll_object* env[]) {
  tll_object* __140; tll_object* __141; tll_object* x_756;
  __140 = env[1];
  __141 = env[2];
  x_756 = fn0_mul_754(__140, __141);
  return x_756;
}

tll_object* fn0_div_757(tll_object* x_148, tll_object* y_149) {
  tll_object* x_150; tll_object* x_151; tll_object* loop_152;
  tll_object* x_153; tll_object* x_166; tll_object* x_763; tll_object* x_764;
  x_151 = fn0_lt_742(x_148, y_149);
  switch(tll_unbox(x_151)){
    case 4: //true_4
      x_150 = tll_box(6);
      break;
    case 5: //false_5
      x_153 = tll_closure_make(fn1_loop_759, 2, 2);
      tll_closure_set(x_153, pred_118, 1);
      tll_closure_set(x_153, sub_131, 2);
      loop_152 = x_153;
      x_763 = tll_closure_app(loop_152, x_148);
      x_764 = tll_closure_app(x_763, y_149);
      x_166 = x_764;
      x_150 = x_166;
      break;
  }
  return x_150;
}

tll_object* fn1_div_758(tll_object* env[]) {
  tll_object* x_148; tll_object* y_149; tll_object* x_766;
  x_148 = env[1];
  y_149 = env[2];
  x_766 = fn0_div_757(x_148, y_149);
  return x_766;
}

tll_object* fn0_rem_767(tll_object* x_168, tll_object* y_169) {
  tll_object* x_170; tll_object* x_171; tll_object* x_172;
  x_172 = fn0_div_757(x_168, y_169);
  x_171 = fn0_mul_754(x_172, y_169);
  x_170 = fn0_sub_751(x_168, x_171);
  return x_170;
}

tll_object* fn1_rem_768(tll_object* env[]) {
  tll_object* x_168; tll_object* y_169; tll_object* x_769;
  x_168 = env[1];
  y_169 = env[2];
  x_769 = fn0_rem_767(x_168, y_169);
  return x_769;
}

tll_object* fn0_rconsUU_770(tll_object* A_174, tll_object* __175, tll_object* __176) {
  tll_object* x_177; tll_object* x_178; tll_object* x_179;
  tll_object* hd_180; tll_object* tl_181; tll_object* x_182;
  tll_object* x_183;
  switch(tll_unbox(__175)){
    case 33: //nilUU_33
      x_178 = tll_ctor_make(34, 2); //consUU_34
      tll_ctor_set(x_178, __176, 0);
      tll_ctor_set(x_178, tll_box(33), 1);
      x_177 = x_178;
      break;
    default:
      hd_180 = tll_ctor_get(__175, 0);
      tl_181 = tll_ctor_get(__175, 1);
      x_182 = fn0_rconsUU_770(NULL, tl_181, __176);
      x_183 = tll_ctor_make(34, 2); //consUU_34
      tll_ctor_set(x_183, hd_180, 0);
      tll_ctor_set(x_183, x_182, 1);
      x_179 = x_183;
      x_177 = x_179;
      break;
  }
  return x_177;
}

tll_object* fn1_rconsUU_771(tll_object* env[]) {
  tll_object* A_174; tll_object* __175; tll_object* __176; tll_object* x_772;
  A_174 = env[1];
  __175 = env[2];
  __176 = env[3];
  x_772 = fn0_rconsUU_770(A_174, __175, __176);
  return x_772;
}

tll_object* fn0_rconsUL_773(tll_object* A_185, tll_object* __186, tll_object* __187) {
  tll_object* x_188; tll_object* x_189; tll_object* x_190;
  tll_object* hd_191; tll_object* tl_192; tll_object* x_193;
  tll_object* x_194;
  switch(tll_unbox(__186)){
    case 31: //nilUL_31
      x_189 = tll_ctor_make(32, 2); //consUL_32
      tll_ctor_set(x_189, __187, 0);
      tll_ctor_set(x_189, tll_box(31), 1);
      x_188 = x_189;
      break;
    default:
      hd_191 = tll_ctor_get(__186, 0);
      tl_192 = tll_ctor_get(__186, 1);
      x_193 = fn0_rconsUL_773(NULL, tl_192, __187);
      x_194 = tll_ctor_set_tag(__186, 32); //consUL_32
      tll_ctor_set(x_194, hd_191, 0);
      tll_ctor_set(x_194, x_193, 1);
      x_190 = x_194;
      x_188 = x_190;
      break;
  }
  return x_188;
}

tll_object* fn1_rconsUL_774(tll_object* env[]) {
  tll_object* A_185; tll_object* __186; tll_object* __187; tll_object* x_775;
  A_185 = env[1];
  __186 = env[2];
  __187 = env[3];
  x_775 = fn0_rconsUL_773(A_185, __186, __187);
  return x_775;
}

tll_object* fn0_rconsLL_776(tll_object* A_196, tll_object* __197, tll_object* __198) {
  tll_object* x_199; tll_object* x_200; tll_object* x_201;
  tll_object* hd_202; tll_object* tl_203; tll_object* x_204;
  tll_object* x_205;
  switch(tll_unbox(__197)){
    case 27: //nilLL_27
      x_200 = tll_ctor_make(28, 2); //consLL_28
      tll_ctor_set(x_200, __198, 0);
      tll_ctor_set(x_200, tll_box(27), 1);
      x_199 = x_200;
      break;
    default:
      hd_202 = tll_ctor_get(__197, 0);
      tl_203 = tll_ctor_get(__197, 1);
      x_204 = fn0_rconsLL_776(NULL, tl_203, __198);
      x_205 = tll_ctor_set_tag(__197, 28); //consLL_28
      tll_ctor_set(x_205, hd_202, 0);
      tll_ctor_set(x_205, x_204, 1);
      x_201 = x_205;
      x_199 = x_201;
      break;
  }
  return x_199;
}

tll_object* fn1_rconsLL_777(tll_object* env[]) {
  tll_object* A_196; tll_object* __197; tll_object* __198; tll_object* x_778;
  A_196 = env[1];
  __197 = env[2];
  __198 = env[3];
  x_778 = fn0_rconsLL_776(A_196, __197, __198);
  return x_778;
}

tll_object* fn0_free_listUU_779(tll_object* A_207, tll_object* f_208, tll_object* __209) {
  tll_object* x_210; tll_object* x_211; tll_object* hd_212;
  tll_object* tl_213; tll_object* __214; tll_object* x_215;
  tll_object* x_216; tll_object* x_781;
  switch(tll_unbox(__209)){
    case 33: //nilUU_33
      x_210 = tll_box(22);
      break;
    default:
      hd_212 = tll_ctor_get(__209, 0);
      tl_213 = tll_ctor_get(__209, 1);
      x_781 = tll_closure_app(f_208, hd_212);
      x_215 = x_781;
      __214 = x_215;
      x_216 = fn0_free_listUU_779(NULL, f_208, tl_213);
      x_211 = x_216;
      x_210 = x_211;
      break;
  }
  return x_210;
}

tll_object* fn1_free_listUU_780(tll_object* env[]) {
  tll_object* A_207; tll_object* f_208; tll_object* __209; tll_object* x_783;
  A_207 = env[1];
  f_208 = env[2];
  __209 = env[3];
  x_783 = fn0_free_listUU_779(A_207, f_208, __209);
  return x_783;
}

tll_object* fn0_free_listUL_784(tll_object* A_218, tll_object* f_219, tll_object* __220) {
  tll_object* x_221; tll_object* x_222; tll_object* hd_223;
  tll_object* tl_224; tll_object* __225; tll_object* x_226;
  tll_object* x_227; tll_object* x_786;
  switch(tll_unbox(__220)){
    case 31: //nilUL_31
      x_221 = tll_box(22);
      break;
    default:
      hd_223 = tll_ctor_get(__220, 0);
      tl_224 = tll_ctor_get(__220, 1);
      x_786 = tll_closure_app(f_219, hd_223);
      x_226 = x_786;
      __225 = x_226;
      x_227 = fn0_free_listUL_784(NULL, f_219, tl_224);
      x_222 = x_227;
      tll_free(__220);
      x_221 = x_222;
      break;
  }
  return x_221;
}

tll_object* fn1_free_listUL_785(tll_object* env[]) {
  tll_object* A_218; tll_object* f_219; tll_object* __220; tll_object* x_788;
  A_218 = env[1];
  f_219 = env[2];
  __220 = env[3];
  x_788 = fn0_free_listUL_784(A_218, f_219, __220);
  return x_788;
}

tll_object* fn0_free_listLL_789(tll_object* A_229, tll_object* f_230, tll_object* __231) {
  tll_object* x_232; tll_object* x_233; tll_object* hd_234;
  tll_object* tl_235; tll_object* __236; tll_object* x_237;
  tll_object* x_238; tll_object* x_791;
  switch(tll_unbox(__231)){
    case 27: //nilLL_27
      x_232 = tll_box(22);
      break;
    default:
      hd_234 = tll_ctor_get(__231, 0);
      tl_235 = tll_ctor_get(__231, 1);
      x_791 = tll_closure_app(f_230, hd_234);
      x_237 = x_791;
      __236 = x_237;
      x_238 = fn0_free_listLL_789(NULL, f_230, tl_235);
      x_233 = x_238;
      tll_free(__231);
      x_232 = x_233;
      break;
  }
  return x_232;
}

tll_object* fn1_free_listLL_790(tll_object* env[]) {
  tll_object* A_229; tll_object* f_230; tll_object* __231; tll_object* x_793;
  A_229 = env[1];
  f_230 = env[2];
  __231 = env[3];
  x_793 = fn0_free_listLL_789(A_229, f_230, __231);
  return x_793;
}

tll_object* fn0_pow_794(tll_object* x_240, tll_object* y_241) {
  tll_object* loop_242; tll_object* x_243; tll_object* x_252;
  tll_object* x_800; tll_object* x_801;
  x_243 = tll_closure_make(fn1_loop_796, 1, 2);
  tll_closure_set(x_243, x_240, 1);
  loop_242 = x_243;
  x_800 = tll_closure_app(loop_242, tll_box(1));
  x_801 = tll_closure_app(x_800, y_241);
  x_252 = x_801;
  return x_252;
}

tll_object* fn1_pow_795(tll_object* env[]) {
  tll_object* x_240; tll_object* y_241; tll_object* x_803;
  x_240 = env[1];
  y_241 = env[2];
  x_803 = fn0_pow_794(x_240, y_241);
  return x_803;
}

tll_object* fn0_powm_804(tll_object* x_254, tll_object* y_255, tll_object* m_256) {
  tll_object* loop_257; tll_object* x_258; tll_object* x_268;
  tll_object* x_810; tll_object* x_811;
  x_258 = tll_closure_make(fn1_loop_806, 2, 2);
  tll_closure_set(x_258, x_254, 1);
  tll_closure_set(x_258, m_256, 2);
  loop_257 = x_258;
  x_810 = tll_closure_app(loop_257, tll_box(1));
  x_811 = tll_closure_app(x_810, y_255);
  x_268 = x_811;
  return x_268;
}

tll_object* fn1_powm_805(tll_object* env[]) {
  tll_object* x_254; tll_object* y_255; tll_object* m_256; tll_object* x_813;
  x_254 = env[1];
  y_255 = env[2];
  m_256 = env[3];
  x_813 = fn0_powm_804(x_254, y_255, m_256);
  return x_813;
}

tll_object* fn0_ord_814(tll_object* c_270) {
  tll_object* x_271;
  x_271 = tll_char_to_int(c_270);
  return x_271;
}

tll_object* fn1_ord_815(tll_object* env[]) {
  tll_object* c_270; tll_object* x_816;
  c_270 = env[1];
  x_816 = fn0_ord_814(c_270);
  return x_816;
}

tll_object* fn0_chr_817(tll_object* i_273) {
  tll_object* x_274;
  x_274 = tll_int_to_char(i_273);
  return x_274;
}

tll_object* fn1_chr_818(tll_object* env[]) {
  tll_object* i_273; tll_object* x_819;
  i_273 = env[1];
  x_819 = fn0_chr_817(i_273);
  return x_819;
}

tll_object* fn0_str_820(tll_object* c_276) {
  tll_object* x_277; tll_object* x_278;
  x_278 = tll_string_make("");
  x_277 = tll_string_pushback(x_278, c_276);
  return x_277;
}

tll_object* fn1_str_821(tll_object* env[]) {
  tll_object* c_276; tll_object* x_822;
  c_276 = env[1];
  x_822 = fn0_str_820(c_276);
  return x_822;
}

tll_object* fn0_strlen_823(tll_object* s_280) {
  tll_object* x_281;
  x_281 = tll_string_size(s_280);
  return x_281;
}

tll_object* fn1_strlen_824(tll_object* env[]) {
  tll_object* s_280; tll_object* x_825;
  s_280 = env[1];
  x_825 = fn0_strlen_823(s_280);
  return x_825;
}

tll_object* fn0_string_of_int_826(tll_object* i_283) {
  tll_object* aux_284; tll_object* x_285; tll_object* x_303;
  tll_object* x_304; tll_object* x_305; tll_object* x_306; tll_object* x_307;
  tll_object* x_308; tll_object* x_309; tll_object* x_831; tll_object* x_833;
  x_285 = tll_closure_make(fn1_aux_828, 3, 1);
  tll_closure_set(x_285, ord_269, 1);
  tll_closure_set(x_285, chr_272, 2);
  tll_closure_set(x_285, str_275, 3);
  aux_284 = x_285;
  x_304 = tll_int_lte(tll_box(0), i_283);
  switch(tll_unbox(x_304)){
    case 4: //true_4
      x_831 = tll_closure_app(aux_284, i_283);
      x_305 = x_831;
      x_303 = x_305;
      break;
    case 5: //false_5
      x_307 = tll_string_make("~");
      x_309 = tll_int_neg(i_283);
      x_833 = tll_closure_app(aux_284, x_309);
      x_308 = x_833;
      x_306 = tll_string_concat(x_307, x_308);
      x_303 = x_306;
      break;
  }
  return x_303;
}

tll_object* fn1_string_of_int_827(tll_object* env[]) {
  tll_object* i_283; tll_object* x_835;
  i_283 = env[1];
  x_835 = fn0_string_of_int_826(i_283);
  return x_835;
}

tll_object* fn0_splitU_836(tll_object* __311) {
  tll_object* x_312; tll_object* x_313; tll_object* x_314;
  tll_object* hd_315; tll_object* tl_316; tll_object* x_317;
  tll_object* x_318; tll_object* x_319; tll_object* x_320;
  tll_object* hd_321; tll_object* tl_322; tll_object* x_323;
  tll_object* x_324; tll_object* m_325; tll_object* n_326; tll_object* x_327;
  tll_object* x_328; tll_object* x_329;
  switch(tll_unbox(__311)){
    case 33: //nilUU_33
      x_313 = tll_ctor_make(46, 2); //ex1UU_46
      tll_ctor_set(x_313, tll_box(33), 0);
      tll_ctor_set(x_313, tll_box(33), 1);
      x_312 = x_313;
      break;
    default:
      hd_315 = tll_ctor_get(__311, 0);
      tl_316 = tll_ctor_get(__311, 1);
      switch(tll_unbox(tl_316)){
        case 33: //nilUU_33
          x_318 = tll_ctor_make(34, 2); //consUU_34
          tll_ctor_set(x_318, hd_315, 0);
          tll_ctor_set(x_318, tll_box(33), 1);
          x_319 = tll_ctor_make(46, 2); //ex1UU_46
          tll_ctor_set(x_319, x_318, 0);
          tll_ctor_set(x_319, tll_box(33), 1);
          x_317 = x_319;
          break;
        default:
          hd_321 = tll_ctor_get(tl_316, 0);
          tl_322 = tll_ctor_get(tl_316, 1);
          x_324 = fn0_splitU_836(tl_322);
          m_325 = tll_ctor_get(x_324, 0);
          n_326 = tll_ctor_get(x_324, 1);
          x_327 = tll_ctor_set_tag(x_324, 34); //consUU_34
          tll_ctor_set(x_327, hd_315, 0);
          tll_ctor_set(x_327, m_325, 1);
          x_328 = tll_ctor_make(34, 2); //consUU_34
          tll_ctor_set(x_328, hd_321, 0);
          tll_ctor_set(x_328, n_326, 1);
          x_329 = tll_ctor_make(46, 2); //ex1UU_46
          tll_ctor_set(x_329, x_327, 0);
          tll_ctor_set(x_329, x_328, 1);
          x_323 = x_329;
          x_320 = x_323;
          x_317 = x_320;
          break;
      }
      x_314 = x_317;
      x_312 = x_314;
      break;
  }
  return x_312;
}

tll_object* fn1_splitU_837(tll_object* env[]) {
  tll_object* __311; tll_object* x_838;
  __311 = env[1];
  x_838 = fn0_splitU_836(__311);
  return x_838;
}

tll_object* fn0_splitL_839(tll_object* __331) {
  tll_object* x_332; tll_object* x_333; tll_object* x_334;
  tll_object* hd_335; tll_object* tl_336; tll_object* x_337;
  tll_object* x_338; tll_object* x_339; tll_object* x_340;
  tll_object* hd_341; tll_object* tl_342; tll_object* x_343;
  tll_object* x_344; tll_object* m_345; tll_object* n_346; tll_object* x_347;
  tll_object* x_348; tll_object* x_349;
  switch(tll_unbox(__331)){
    case 31: //nilUL_31
      x_333 = tll_ctor_make(43, 2); //ex1LL_43
      tll_ctor_set(x_333, tll_box(31), 0);
      tll_ctor_set(x_333, tll_box(31), 1);
      x_332 = x_333;
      break;
    default:
      hd_335 = tll_ctor_get(__331, 0);
      tl_336 = tll_ctor_get(__331, 1);
      switch(tll_unbox(tl_336)){
        case 31: //nilUL_31
          x_338 = tll_ctor_set_tag(__331, 32); //consUL_32
          tll_ctor_set(x_338, hd_335, 0);
          tll_ctor_set(x_338, tll_box(31), 1);
          x_339 = tll_ctor_make(43, 2); //ex1LL_43
          tll_ctor_set(x_339, x_338, 0);
          tll_ctor_set(x_339, tll_box(31), 1);
          x_337 = x_339;
          break;
        default:
          hd_341 = tll_ctor_get(tl_336, 0);
          tl_342 = tll_ctor_get(tl_336, 1);
          x_344 = fn0_splitL_839(tl_342);
          m_345 = tll_ctor_get(x_344, 0);
          n_346 = tll_ctor_get(x_344, 1);
          x_347 = tll_ctor_set_tag(x_344, 32); //consUL_32
          tll_ctor_set(x_347, hd_335, 0);
          tll_ctor_set(x_347, m_345, 1);
          x_348 = tll_ctor_set_tag(tl_336, 32); //consUL_32
          tll_ctor_set(x_348, hd_341, 0);
          tll_ctor_set(x_348, n_346, 1);
          x_349 = tll_ctor_set_tag(__331, 43); //ex1LL_43
          tll_ctor_set(x_349, x_347, 0);
          tll_ctor_set(x_349, x_348, 1);
          x_343 = x_349;
          x_340 = x_343;
          x_337 = x_340;
          break;
      }
      x_334 = x_337;
      x_332 = x_334;
      break;
  }
  return x_332;
}

tll_object* fn1_splitL_840(tll_object* env[]) {
  tll_object* __331; tll_object* x_841;
  __331 = env[1];
  x_841 = fn0_splitL_839(__331);
  return x_841;
}

tll_object* fn0_mergeU_842(tll_object* __351, tll_object* __352) {
  tll_object* x_353; tll_object* x_354; tll_object* hd_355;
  tll_object* tl_356; tll_object* x_357; tll_object* x_358;
  tll_object* x_359; tll_object* hd_360; tll_object* tl_361;
  tll_object* x_362; tll_object* x_363; tll_object* x_364; tll_object* x_365;
  tll_object* x_366; tll_object* x_367; tll_object* x_368; tll_object* x_369;
  switch(tll_unbox(__351)){
    case 33: //nilUU_33
      x_353 = __352;
      break;
    default:
      hd_355 = tll_ctor_get(__351, 0);
      tl_356 = tll_ctor_get(__351, 1);
      switch(tll_unbox(__352)){
        case 33: //nilUU_33
          x_358 = tll_ctor_make(34, 2); //consUU_34
          tll_ctor_set(x_358, hd_355, 0);
          tll_ctor_set(x_358, tl_356, 1);
          x_357 = x_358;
          break;
        default:
          hd_360 = tll_ctor_get(__352, 0);
          tl_361 = tll_ctor_get(__352, 1);
          x_363 = tll_int_lte(hd_355, hd_360);
          switch(tll_unbox(x_363)){
            case 4: //true_4
              x_365 = tll_ctor_make(34, 2); //consUU_34
              tll_ctor_set(x_365, hd_360, 0);
              tll_ctor_set(x_365, tl_361, 1);
              x_364 = fn0_mergeU_842(tl_356, x_365);
              x_366 = tll_ctor_make(34, 2); //consUU_34
              tll_ctor_set(x_366, hd_355, 0);
              tll_ctor_set(x_366, x_364, 1);
              x_362 = x_366;
              break;
            case 5: //false_5
              x_368 = tll_ctor_make(34, 2); //consUU_34
              tll_ctor_set(x_368, hd_355, 0);
              tll_ctor_set(x_368, tl_356, 1);
              x_367 = fn0_mergeU_842(x_368, tl_361);
              x_369 = tll_ctor_make(34, 2); //consUU_34
              tll_ctor_set(x_369, hd_360, 0);
              tll_ctor_set(x_369, x_367, 1);
              x_362 = x_369;
              break;
          }
          x_359 = x_362;
          x_357 = x_359;
          break;
      }
      x_354 = x_357;
      x_353 = x_354;
      break;
  }
  return x_353;
}

tll_object* fn1_mergeU_843(tll_object* env[]) {
  tll_object* __351; tll_object* __352; tll_object* x_844;
  __351 = env[1];
  __352 = env[2];
  x_844 = fn0_mergeU_842(__351, __352);
  return x_844;
}

tll_object* fn0_mergeL_845(tll_object* __371, tll_object* __372) {
  tll_object* x_373; tll_object* x_374; tll_object* hd_375;
  tll_object* tl_376; tll_object* x_377; tll_object* x_378;
  tll_object* x_379; tll_object* hd_380; tll_object* tl_381;
  tll_object* x_382; tll_object* x_383; tll_object* x_384; tll_object* x_385;
  tll_object* x_386; tll_object* x_387; tll_object* x_388; tll_object* x_389;
  switch(tll_unbox(__371)){
    case 31: //nilUL_31
      x_373 = __372;
      break;
    default:
      hd_375 = tll_ctor_get(__371, 0);
      tl_376 = tll_ctor_get(__371, 1);
      switch(tll_unbox(__372)){
        case 31: //nilUL_31
          x_378 = tll_ctor_set_tag(__371, 32); //consUL_32
          tll_ctor_set(x_378, hd_375, 0);
          tll_ctor_set(x_378, tl_376, 1);
          x_377 = x_378;
          break;
        default:
          hd_380 = tll_ctor_get(__372, 0);
          tl_381 = tll_ctor_get(__372, 1);
          x_383 = tll_int_lte(hd_375, hd_380);
          switch(tll_unbox(x_383)){
            case 4: //true_4
              x_385 = tll_ctor_set_tag(__372, 32); //consUL_32
              tll_ctor_set(x_385, hd_380, 0);
              tll_ctor_set(x_385, tl_381, 1);
              x_384 = fn0_mergeL_845(tl_376, x_385);
              x_386 = tll_ctor_set_tag(__371, 32); //consUL_32
              tll_ctor_set(x_386, hd_375, 0);
              tll_ctor_set(x_386, x_384, 1);
              x_382 = x_386;
              break;
            case 5: //false_5
              x_388 = tll_ctor_set_tag(__372, 32); //consUL_32
              tll_ctor_set(x_388, hd_375, 0);
              tll_ctor_set(x_388, tl_376, 1);
              x_387 = fn0_mergeL_845(x_388, tl_381);
              x_389 = tll_ctor_set_tag(__371, 32); //consUL_32
              tll_ctor_set(x_389, hd_380, 0);
              tll_ctor_set(x_389, x_387, 1);
              x_382 = x_389;
              break;
          }
          x_379 = x_382;
          x_377 = x_379;
          break;
      }
      x_374 = x_377;
      x_373 = x_374;
      break;
  }
  return x_373;
}

tll_object* fn1_mergeL_846(tll_object* env[]) {
  tll_object* __371; tll_object* __372; tll_object* x_847;
  __371 = env[1];
  __372 = env[2];
  x_847 = fn0_mergeL_845(__371, __372);
  return x_847;
}

tll_object* fn0_msortU_848(tll_object* __391) {
  tll_object* x_392; tll_object* x_393; tll_object* hd_394;
  tll_object* tl_395; tll_object* x_396; tll_object* x_397;
  tll_object* x_398; tll_object* hd_399; tll_object* tl_400;
  tll_object* x_401; tll_object* x_402; tll_object* x_403; tll_object* x_404;
  tll_object* m_405; tll_object* n_406; tll_object* x_407; tll_object* x_408;
  tll_object* x_409;
  switch(tll_unbox(__391)){
    case 33: //nilUU_33
      x_392 = tll_box(33);
      break;
    default:
      hd_394 = tll_ctor_get(__391, 0);
      tl_395 = tll_ctor_get(__391, 1);
      switch(tll_unbox(tl_395)){
        case 33: //nilUU_33
          x_397 = tll_ctor_make(34, 2); //consUU_34
          tll_ctor_set(x_397, hd_394, 0);
          tll_ctor_set(x_397, tll_box(33), 1);
          x_396 = x_397;
          break;
        default:
          hd_399 = tll_ctor_get(tl_395, 0);
          tl_400 = tll_ctor_get(tl_395, 1);
          x_403 = tll_ctor_make(34, 2); //consUU_34
          tll_ctor_set(x_403, hd_399, 0);
          tll_ctor_set(x_403, tl_400, 1);
          x_404 = tll_ctor_make(34, 2); //consUU_34
          tll_ctor_set(x_404, hd_394, 0);
          tll_ctor_set(x_404, x_403, 1);
          x_402 = fn0_splitU_836(x_404);
          m_405 = tll_ctor_get(x_402, 0);
          n_406 = tll_ctor_get(x_402, 1);
          x_408 = fn0_msortU_848(m_405);
          x_409 = fn0_msortU_848(n_406);
          x_407 = fn0_mergeU_842(x_408, x_409);
          x_401 = x_407;
          tll_free(x_402);
          x_398 = x_401;
          x_396 = x_398;
          break;
      }
      x_393 = x_396;
      x_392 = x_393;
      break;
  }
  return x_392;
}

tll_object* fn1_msortU_849(tll_object* env[]) {
  tll_object* __391; tll_object* x_850;
  __391 = env[1];
  x_850 = fn0_msortU_848(__391);
  return x_850;
}

tll_object* fn0_msortL_851(tll_object* __411) {
  tll_object* x_412; tll_object* x_413; tll_object* hd_414;
  tll_object* tl_415; tll_object* x_416; tll_object* x_417;
  tll_object* x_418; tll_object* hd_419; tll_object* tl_420;
  tll_object* x_421; tll_object* x_422; tll_object* x_423; tll_object* x_424;
  tll_object* m_425; tll_object* n_426; tll_object* x_427; tll_object* x_428;
  tll_object* x_429;
  switch(tll_unbox(__411)){
    case 31: //nilUL_31
      x_412 = tll_box(31);
      break;
    default:
      hd_414 = tll_ctor_get(__411, 0);
      tl_415 = tll_ctor_get(__411, 1);
      switch(tll_unbox(tl_415)){
        case 31: //nilUL_31
          x_417 = tll_ctor_set_tag(__411, 32); //consUL_32
          tll_ctor_set(x_417, hd_414, 0);
          tll_ctor_set(x_417, tll_box(31), 1);
          x_416 = x_417;
          break;
        default:
          hd_419 = tll_ctor_get(tl_415, 0);
          tl_420 = tll_ctor_get(tl_415, 1);
          x_423 = tll_ctor_set_tag(tl_415, 32); //consUL_32
          tll_ctor_set(x_423, hd_419, 0);
          tll_ctor_set(x_423, tl_420, 1);
          x_424 = tll_ctor_set_tag(__411, 32); //consUL_32
          tll_ctor_set(x_424, hd_414, 0);
          tll_ctor_set(x_424, x_423, 1);
          x_422 = fn0_splitL_839(x_424);
          m_425 = tll_ctor_get(x_422, 0);
          n_426 = tll_ctor_get(x_422, 1);
          x_428 = fn0_msortL_851(m_425);
          x_429 = fn0_msortL_851(n_426);
          x_427 = fn0_mergeL_845(x_428, x_429);
          x_421 = x_427;
          tll_free(x_422);
          x_418 = x_421;
          x_416 = x_418;
          break;
      }
      x_413 = x_416;
      x_412 = x_413;
      break;
  }
  return x_412;
}

tll_object* fn1_msortL_852(tll_object* env[]) {
  tll_object* __411; tll_object* x_853;
  __411 = env[1];
  x_853 = fn0_msortL_851(__411);
  return x_853;
}

tll_object* fn0_cmsort_workerU_854(tll_object* __431, tll_object* zs_432, tll_object* __433) {
  tll_object* x_434; tll_object* x_435; tll_object* x_439;
  tll_object* hd_440; tll_object* tl_441; tll_object* x_442;
  tll_object* x_443; tll_object* x_448; tll_object* hd_449;
  tll_object* tl_450; tll_object* x_451; tll_object* x_452;
  tll_object* x_453; tll_object* x_460; tll_object* x_461; tll_object* x_462;
  tll_object* x_463; tll_object* m_464; tll_object* n_465; tll_object* x_466;
  switch(tll_unbox(zs_432)){
    case 33: //nilUU_33
      x_435 = tll_thunk_make(thunk__856, 1);
      tll_thunk_set(x_435, __433, 0);
      x_434 = x_435;
      break;
    default:
      hd_440 = tll_ctor_get(zs_432, 0);
      tl_441 = tll_ctor_get(zs_432, 1);
      switch(tll_unbox(tl_441)){
        case 33: //nilUU_33
          x_443 = tll_thunk_make(thunk__857, 2);
          tll_thunk_set(x_443, __433, 0);
          tll_thunk_set(x_443, hd_440, 1);
          x_442 = x_443;
          break;
        default:
          hd_449 = tll_ctor_get(tl_441, 0);
          tl_450 = tll_ctor_get(tl_441, 1);
          x_452 = tll_int_lte(__431, tll_box(0));
          switch(tll_unbox(x_452)){
            case 4: //true_4
              x_453 = tll_thunk_make(thunk__858, 5);
              tll_thunk_set(x_453, msortU_390, 0);
              tll_thunk_set(x_453, __433, 1);
              tll_thunk_set(x_453, hd_440, 2);
              tll_thunk_set(x_453, hd_449, 3);
              tll_thunk_set(x_453, tl_450, 4);
              x_451 = x_453;
              break;
            case 5: //false_5
              x_462 = tll_ctor_make(34, 2); //consUU_34
              tll_ctor_set(x_462, hd_449, 0);
              tll_ctor_set(x_462, tl_450, 1);
              x_463 = tll_ctor_make(34, 2); //consUU_34
              tll_ctor_set(x_463, hd_440, 0);
              tll_ctor_set(x_463, x_462, 1);
              x_461 = fn0_splitU_836(x_463);
              m_464 = tll_ctor_get(x_461, 0);
              n_465 = tll_ctor_get(x_461, 1);
              x_466 = tll_thunk_make(thunk__859, 7);
              tll_thunk_set(x_466, rwlUU_7, 0);
              tll_thunk_set(x_466, mergeU_350, 1);
              tll_thunk_set(x_466, cmsort_workerU_430, 2);
              tll_thunk_set(x_466, __431, 3);
              tll_thunk_set(x_466, __433, 4);
              tll_thunk_set(x_466, m_464, 5);
              tll_thunk_set(x_466, n_465, 6);
              x_460 = x_466;
              tll_free(x_461);
              x_451 = x_460;
              break;
          }
          x_448 = x_451;
          x_442 = x_448;
          break;
      }
      x_439 = x_442;
      x_434 = x_439;
      break;
  }
  return x_434;
}

tll_object* fn1_cmsort_workerU_855(tll_object* env[]) {
  tll_object* __431; tll_object* zs_432; tll_object* __433;
  tll_object* x_862;
  __431 = env[1];
  zs_432 = env[2];
  __433 = env[3];
  x_862 = fn0_cmsort_workerU_854(__431, zs_432, __433);
  return x_862;
}

tll_object* fn0_cmsort_workerL_863(tll_object* __503, tll_object* zs_504, tll_object* __505) {
  tll_object* x_506; tll_object* x_507; tll_object* x_511;
  tll_object* hd_512; tll_object* tl_513; tll_object* x_514;
  tll_object* x_515; tll_object* x_520; tll_object* hd_521;
  tll_object* tl_522; tll_object* x_523; tll_object* x_524;
  tll_object* x_525; tll_object* x_532; tll_object* x_533; tll_object* x_534;
  tll_object* x_535; tll_object* m_536; tll_object* n_537; tll_object* x_538;
  switch(tll_unbox(zs_504)){
    case 31: //nilUL_31
      x_507 = tll_thunk_make(thunk__865, 1);
      tll_thunk_set(x_507, __505, 0);
      x_506 = x_507;
      break;
    default:
      hd_512 = tll_ctor_get(zs_504, 0);
      tl_513 = tll_ctor_get(zs_504, 1);
      switch(tll_unbox(tl_513)){
        case 31: //nilUL_31
          x_515 = tll_thunk_make(thunk__866, 3);
          tll_thunk_set(x_515, zs_504, 0);
          tll_thunk_set(x_515, __505, 1);
          tll_thunk_set(x_515, hd_512, 2);
          x_514 = x_515;
          break;
        default:
          hd_521 = tll_ctor_get(tl_513, 0);
          tl_522 = tll_ctor_get(tl_513, 1);
          x_524 = tll_int_lte(__503, tll_box(0));
          switch(tll_unbox(x_524)){
            case 4: //true_4
              x_525 = tll_thunk_make(thunk__867, 7);
              tll_thunk_set(x_525, msortL_410, 0);
              tll_thunk_set(x_525, zs_504, 1);
              tll_thunk_set(x_525, __505, 2);
              tll_thunk_set(x_525, hd_512, 3);
              tll_thunk_set(x_525, tl_513, 4);
              tll_thunk_set(x_525, hd_521, 5);
              tll_thunk_set(x_525, tl_522, 6);
              x_523 = x_525;
              break;
            case 5: //false_5
              x_534 = tll_ctor_set_tag(tl_513, 32); //consUL_32
              tll_ctor_set(x_534, hd_521, 0);
              tll_ctor_set(x_534, tl_522, 1);
              x_535 = tll_ctor_set_tag(zs_504, 32); //consUL_32
              tll_ctor_set(x_535, hd_512, 0);
              tll_ctor_set(x_535, x_534, 1);
              x_533 = fn0_splitL_839(x_535);
              m_536 = tll_ctor_get(x_533, 0);
              n_537 = tll_ctor_get(x_533, 1);
              x_538 = tll_thunk_make(thunk__868, 7);
              tll_thunk_set(x_538, rwlLL_28, 0);
              tll_thunk_set(x_538, mergeL_370, 1);
              tll_thunk_set(x_538, cmsort_workerL_502, 2);
              tll_thunk_set(x_538, __503, 3);
              tll_thunk_set(x_538, __505, 4);
              tll_thunk_set(x_538, m_536, 5);
              tll_thunk_set(x_538, n_537, 6);
              x_532 = x_538;
              tll_free(x_533);
              x_523 = x_532;
              break;
          }
          x_520 = x_523;
          x_514 = x_520;
          break;
      }
      x_511 = x_514;
      x_506 = x_511;
      break;
  }
  return x_506;
}

tll_object* fn1_cmsort_workerL_864(tll_object* env[]) {
  tll_object* __503; tll_object* zs_504; tll_object* __505;
  tll_object* x_871;
  __503 = env[1];
  zs_504 = env[2];
  __505 = env[3];
  x_871 = fn0_cmsort_workerL_863(__503, zs_504, __505);
  return x_871;
}

tll_object* fn0_cmsortU_872(tll_object* zs_575) {
  tll_object* x_576;
  x_576 = tll_thunk_make(thunk__874, 2);
  tll_thunk_set(x_576, cmsort_workerU_430, 0);
  tll_thunk_set(x_576, zs_575, 1);
  return x_576;
}

tll_object* fn1_cmsortU_873(tll_object* env[]) {
  tll_object* zs_575; tll_object* x_876;
  zs_575 = env[1];
  x_876 = fn0_cmsortU_872(zs_575);
  return x_876;
}

tll_object* fn0_cmsortL_877(tll_object* zs_591) {
  tll_object* x_592;
  x_592 = tll_thunk_make(thunk__879, 2);
  tll_thunk_set(x_592, cmsort_workerL_502, 0);
  tll_thunk_set(x_592, zs_591, 1);
  return x_592;
}

tll_object* fn1_cmsortL_878(tll_object* env[]) {
  tll_object* zs_591; tll_object* x_881;
  zs_591 = env[1];
  x_881 = fn0_cmsortL_877(zs_591);
  return x_881;
}

tll_object* fn0_mklistU_882(tll_object* n_607) {
  tll_object* x_608; tll_object* x_609; tll_object* x_610; tll_object* x_611;
  tll_object* x_612;
  x_609 = tll_int_lte(n_607, tll_box(0));
  switch(tll_unbox(x_609)){
    case 4: //true_4
      x_608 = tll_box(33);
      break;
    case 5: //false_5
      x_611 = tll_int_sub(n_607, tll_box(1));
      x_610 = fn0_mklistU_882(x_611);
      x_612 = tll_ctor_make(34, 2); //consUU_34
      tll_ctor_set(x_612, n_607, 0);
      tll_ctor_set(x_612, x_610, 1);
      x_608 = x_612;
      break;
  }
  return x_608;
}

tll_object* fn1_mklistU_883(tll_object* env[]) {
  tll_object* n_607; tll_object* x_884;
  n_607 = env[1];
  x_884 = fn0_mklistU_882(n_607);
  return x_884;
}

tll_object* fn0_mklistL_885(tll_object* n_614) {
  tll_object* x_615; tll_object* x_616; tll_object* x_617; tll_object* x_618;
  tll_object* x_619;
  x_616 = tll_int_lte(n_614, tll_box(0));
  switch(tll_unbox(x_616)){
    case 4: //true_4
      x_615 = tll_box(31);
      break;
    case 5: //false_5
      x_618 = tll_int_sub(n_614, tll_box(1));
      x_617 = fn0_mklistL_885(x_618);
      x_619 = tll_ctor_make(32, 2); //consUL_32
      tll_ctor_set(x_619, n_614, 0);
      tll_ctor_set(x_619, x_617, 1);
      x_615 = x_619;
      break;
  }
  return x_615;
}

tll_object* fn1_mklistL_886(tll_object* env[]) {
  tll_object* n_614; tll_object* x_887;
  n_614 = env[1];
  x_887 = fn0_mklistL_885(n_614);
  return x_887;
}

tll_object* fn0_list_lenU_888(tll_object* __621) {
  tll_object* x_622; tll_object* x_623; tll_object* tl_625;
  tll_object* x_626; tll_object* x_627;
  switch(tll_unbox(__621)){
    case 33: //nilUU_33
      x_622 = tll_box(0);
      break;
    default:
      tl_625 = tll_ctor_get(__621, 1);
      x_627 = fn0_list_lenU_888(tl_625);
      x_626 = tll_int_add(tll_box(1), x_627);
      x_623 = x_626;
      x_622 = x_623;
      break;
  }
  return x_622;
}

tll_object* fn1_list_lenU_889(tll_object* env[]) {
  tll_object* __621; tll_object* x_890;
  __621 = env[1];
  x_890 = fn0_list_lenU_888(__621);
  return x_890;
}

tll_object* fn0_list_lenL_891(tll_object* __629) {
  tll_object* x_630; tll_object* x_631; tll_object* tl_633;
  tll_object* x_634; tll_object* x_635;
  switch(tll_unbox(__629)){
    case 31: //nilUL_31
      x_630 = tll_box(0);
      break;
    default:
      tl_633 = tll_ctor_get(__629, 1);
      x_635 = fn0_list_lenL_891(tl_633);
      x_634 = tll_int_add(tll_box(1), x_635);
      x_631 = x_634;
      tll_free(__629);
      x_630 = x_631;
      break;
  }
  return x_630;
}

tll_object* fn1_list_lenL_892(tll_object* env[]) {
  tll_object* __629; tll_object* x_893;
  __629 = env[1];
  x_893 = fn0_list_lenL_891(__629);
  return x_893;
}

tll_object* fn0_print_listU_894(tll_object* __637) {
  tll_object* x_638; tll_object* x_639; tll_object* x_642;
  tll_object* hd_643; tll_object* tl_644; tll_object* x_645;
  switch(tll_unbox(__637)){
    case 33: //nilUU_33
      x_639 = tll_thunk_make(thunk__896, 0);
      x_638 = x_639;
      break;
    default:
      hd_643 = tll_ctor_get(__637, 0);
      tl_644 = tll_ctor_get(__637, 1);
      x_645 = tll_thunk_make(thunk__897, 4);
      tll_thunk_set(x_645, string_of_int_282, 0);
      tll_thunk_set(x_645, print_listU_636, 1);
      tll_thunk_set(x_645, hd_643, 2);
      tll_thunk_set(x_645, tl_644, 3);
      x_642 = x_645;
      x_638 = x_642;
      break;
  }
  return x_638;
}

tll_object* fn1_print_listU_895(tll_object* env[]) {
  tll_object* __637; tll_object* x_898;
  __637 = env[1];
  x_898 = fn0_print_listU_894(__637);
  return x_898;
}

tll_object* fn0_print_listL_899(tll_object* __655) {
  tll_object* x_656; tll_object* x_657; tll_object* x_660;
  tll_object* hd_661; tll_object* tl_662; tll_object* x_663;
  switch(tll_unbox(__655)){
    case 31: //nilUL_31
      x_657 = tll_thunk_make(thunk__901, 0);
      x_656 = x_657;
      break;
    default:
      hd_661 = tll_ctor_get(__655, 0);
      tl_662 = tll_ctor_get(__655, 1);
      x_663 = tll_thunk_make(thunk__902, 4);
      tll_thunk_set(x_663, string_of_int_282, 0);
      tll_thunk_set(x_663, print_listL_654, 1);
      tll_thunk_set(x_663, hd_661, 2);
      tll_thunk_set(x_663, tl_662, 3);
      x_660 = x_663;
      tll_free(__655);
      x_656 = x_660;
      break;
  }
  return x_656;
}

tll_object* fn1_print_listL_900(tll_object* env[]) {
  tll_object* __655; tll_object* x_903;
  __655 = env[1];
  x_903 = fn0_print_listL_899(__655);
  return x_903;
}

tll_object* thunk__905(tll_object* env[]) {
  tll_object* string_of_int_282; tll_object* cmsortL_590;
  tll_object* list_lenL_628; tll_object* test_672; tll_object* _675;
  tll_object* x_676; tll_object* x_677; tll_object* len_678;
  tll_object* x_679; tll_object* x_680; tll_object* x_681;
  string_of_int_282 = env[0];
  cmsortL_590 = env[1];
  list_lenL_628 = env[2];
  test_672 = env[3];
  x_677 = fn0_cmsortL_877(test_672);
  x_676 = tll_thunk_force(x_677);
  tll_free(x_677);
  _675 = x_676;
  x_679 = fn0_list_lenL_891(_675);
  len_678 = x_679;
  x_681 = fn0_string_of_int_826(len_678);
  x_680 = tll_effect_print(x_681);
  return x_680;
}

tll_object* thunk__902(tll_object* env[]) {
  tll_object* string_of_int_282; tll_object* print_listL_654;
  tll_object* hd_661; tll_object* tl_662; tll_object* __664;
  tll_object* x_665; tll_object* x_666; tll_object* __667; tll_object* x_668;
  tll_object* x_669; tll_object* x_670; tll_object* x_671;
  string_of_int_282 = env[0];
  print_listL_654 = env[1];
  hd_661 = env[2];
  tl_662 = env[3];
  x_666 = fn0_string_of_int_826(hd_661);
  x_665 = tll_effect_print(x_666);
  __664 = x_665;
  x_669 = tll_string_make(" :: ");
  x_668 = tll_effect_print(x_669);
  __667 = x_668;
  x_671 = fn0_print_listL_899(tl_662);
  x_670 = tll_thunk_force(x_671);
  tll_free(x_671);
  return x_670;
}

tll_object* thunk__901(tll_object* env[]) {
  tll_object* x_658; tll_object* x_659;
  x_659 = tll_string_make("nil");
  x_658 = tll_effect_print(x_659);
  return x_658;
}

tll_object* thunk__897(tll_object* env[]) {
  tll_object* string_of_int_282; tll_object* print_listU_636;
  tll_object* hd_643; tll_object* tl_644; tll_object* __646;
  tll_object* x_647; tll_object* x_648; tll_object* __649; tll_object* x_650;
  tll_object* x_651; tll_object* x_652; tll_object* x_653;
  string_of_int_282 = env[0];
  print_listU_636 = env[1];
  hd_643 = env[2];
  tl_644 = env[3];
  x_648 = fn0_string_of_int_826(hd_643);
  x_647 = tll_effect_print(x_648);
  __646 = x_647;
  x_651 = tll_string_make(" :: ");
  x_650 = tll_effect_print(x_651);
  __649 = x_650;
  x_653 = fn0_print_listU_894(tl_644);
  x_652 = tll_thunk_force(x_653);
  tll_free(x_653);
  return x_652;
}

tll_object* thunk__896(tll_object* env[]) {
  tll_object* x_640; tll_object* x_641;
  x_641 = tll_string_make("nil");
  x_640 = tll_effect_print(x_641);
  return x_640;
}

tll_object* thunk__879(tll_object* env[]) {
  tll_object* cmsort_workerL_502; tll_object* zs_591; tll_object* c_593;
  tll_object* x_594; tll_object* x_595; tll_object* _599; tll_object* x_600;
  tll_object* x_601; tll_object* m_602; tll_object* n_603; tll_object* __604;
  tll_object* x_605;
  cmsort_workerL_502 = env[0];
  zs_591 = env[1];
  x_595 = tll_closure_make(fn1_lam_880, 2, 1);
  tll_closure_set(x_595, cmsort_workerL_502, 1);
  tll_closure_set(x_595, zs_591, 2);
  x_594 = tll_effect_fork(x_595);
  c_593 = x_594;
  x_600 = tll_effect_recv1(c_593);
  _599 = x_600;
  m_602 = tll_ctor_get(_599, 0);
  n_603 = tll_ctor_get(_599, 1);
  x_605 = tll_effect_close1(n_603);
  __604 = x_605;
  x_601 = m_602;
  tll_free(_599);
  return x_601;
}

tll_object* fn1_lam_880(tll_object* env[]) {
  tll_object* cmsort_workerL_502; tll_object* zs_591; tll_object* lam_596;
  tll_object* _597; tll_object* x_598;
  lam_596 = env[0];
  cmsort_workerL_502 = env[1];
  zs_591 = env[2];
  _597 = env[3];
  x_598 = fn0_cmsort_workerL_863(tll_box(3), zs_591, _597);
  return x_598;
}

tll_object* thunk__874(tll_object* env[]) {
  tll_object* cmsort_workerU_430; tll_object* zs_575; tll_object* c_577;
  tll_object* x_578; tll_object* x_579; tll_object* _583; tll_object* x_584;
  tll_object* x_585; tll_object* m_586; tll_object* n_587; tll_object* __588;
  tll_object* x_589;
  cmsort_workerU_430 = env[0];
  zs_575 = env[1];
  x_579 = tll_closure_make(fn1_lam_875, 2, 1);
  tll_closure_set(x_579, cmsort_workerU_430, 1);
  tll_closure_set(x_579, zs_575, 2);
  x_578 = tll_effect_fork(x_579);
  c_577 = x_578;
  x_584 = tll_effect_recv0(c_577);
  _583 = x_584;
  m_586 = tll_ctor_get(_583, 0);
  n_587 = tll_ctor_get(_583, 1);
  x_589 = tll_effect_close1(n_587);
  __588 = x_589;
  x_585 = m_586;
  tll_free(_583);
  return x_585;
}

tll_object* fn1_lam_875(tll_object* env[]) {
  tll_object* cmsort_workerU_430; tll_object* zs_575; tll_object* lam_580;
  tll_object* _581; tll_object* x_582;
  lam_580 = env[0];
  cmsort_workerU_430 = env[1];
  zs_575 = env[2];
  _581 = env[3];
  x_582 = fn0_cmsort_workerU_854(tll_box(3), zs_575, _581);
  return x_582;
}

tll_object* thunk__868(tll_object* env[]) {
  tll_object* rwlLL_28; tll_object* mergeL_370;
  tll_object* cmsort_workerL_502; tll_object* __503; tll_object* __505;
  tll_object* m_536; tll_object* n_537; tll_object* r1_539;
  tll_object* x_540; tll_object* x_541; tll_object* r2_546;
  tll_object* x_547; tll_object* x_548; tll_object* _553; tll_object* x_554;
  tll_object* x_555; tll_object* m_556; tll_object* n_557; tll_object* _558;
  tll_object* x_559; tll_object* x_560; tll_object* m_561; tll_object* n_562;
  tll_object* zs1_563; tll_object* x_564; tll_object* zs1_565;
  tll_object* x_566; tll_object* c_567; tll_object* x_568; tll_object* __569;
  tll_object* x_570; tll_object* __571; tll_object* x_572; tll_object* x_573;
  rwlLL_28 = env[0];
  mergeL_370 = env[1];
  cmsort_workerL_502 = env[2];
  __503 = env[3];
  __505 = env[4];
  m_536 = env[5];
  n_537 = env[6];
  x_541 = tll_closure_make(fn1_lam_869, 3, 1);
  tll_closure_set(x_541, cmsort_workerL_502, 1);
  tll_closure_set(x_541, __503, 2);
  tll_closure_set(x_541, m_536, 3);
  x_540 = tll_effect_fork(x_541);
  r1_539 = x_540;
  x_548 = tll_closure_make(fn1_lam_870, 3, 1);
  tll_closure_set(x_548, cmsort_workerL_502, 1);
  tll_closure_set(x_548, __503, 2);
  tll_closure_set(x_548, n_537, 3);
  x_547 = tll_effect_fork(x_548);
  r2_546 = x_547;
  x_554 = tll_effect_recv1(r1_539);
  _553 = x_554;
  m_556 = tll_ctor_get(_553, 0);
  n_557 = tll_ctor_get(_553, 1);
  x_559 = tll_effect_recv1(r2_546);
  _558 = x_559;
  m_561 = tll_ctor_get(_558, 0);
  n_562 = tll_ctor_get(_558, 1);
  x_564 = fn0_mergeL_845(m_556, m_561);
  zs1_563 = x_564;
  x_566 = fn0_rwlLL_697(NULL, NULL, NULL, NULL, NULL, zs1_563);
  zs1_565 = x_566;
  x_568 = tll_effect_send(__505, zs1_565);
  c_567 = x_568;
  x_570 = tll_effect_close1(n_557);
  __569 = x_570;
  x_572 = tll_effect_close1(n_562);
  __571 = x_572;
  x_573 = tll_effect_close0(c_567);
  x_560 = x_573;
  tll_free(_558);
  x_555 = x_560;
  tll_free(_553);
  return x_555;
}

tll_object* fn1_lam_869(tll_object* env[]) {
  tll_object* cmsort_workerL_502; tll_object* __503; tll_object* m_536;
  tll_object* lam_542; tll_object* _543; tll_object* x_544;
  tll_object* x_545;
  lam_542 = env[0];
  cmsort_workerL_502 = env[1];
  __503 = env[2];
  m_536 = env[3];
  _543 = env[4];
  x_545 = tll_int_sub(__503, tll_box(1));
  x_544 = fn0_cmsort_workerL_863(x_545, m_536, _543);
  return x_544;
}

tll_object* fn1_lam_870(tll_object* env[]) {
  tll_object* cmsort_workerL_502; tll_object* __503; tll_object* n_537;
  tll_object* lam_549; tll_object* _550; tll_object* x_551;
  tll_object* x_552;
  lam_549 = env[0];
  cmsort_workerL_502 = env[1];
  __503 = env[2];
  n_537 = env[3];
  _550 = env[4];
  x_552 = tll_int_sub(__503, tll_box(1));
  x_551 = fn0_cmsort_workerL_863(x_552, n_537, _550);
  return x_551;
}

tll_object* thunk__867(tll_object* env[]) {
  tll_object* msortL_410; tll_object* zs_504; tll_object* __505;
  tll_object* hd_512; tll_object* tl_513; tll_object* hd_521;
  tll_object* tl_522; tll_object* c_526; tll_object* x_527;
  tll_object* x_528; tll_object* x_529; tll_object* x_530; tll_object* x_531;
  msortL_410 = env[0];
  zs_504 = env[1];
  __505 = env[2];
  hd_512 = env[3];
  tl_513 = env[4];
  hd_521 = env[5];
  tl_522 = env[6];
  x_529 = tll_ctor_set_tag(tl_513, 32); //consUL_32
  tll_ctor_set(x_529, hd_521, 0);
  tll_ctor_set(x_529, tl_522, 1);
  x_530 = tll_ctor_set_tag(zs_504, 32); //consUL_32
  tll_ctor_set(x_530, hd_512, 0);
  tll_ctor_set(x_530, x_529, 1);
  x_528 = fn0_msortL_851(x_530);
  x_527 = tll_effect_send(__505, x_528);
  c_526 = x_527;
  x_531 = tll_effect_close0(c_526);
  return x_531;
}

tll_object* thunk__866(tll_object* env[]) {
  tll_object* zs_504; tll_object* __505; tll_object* hd_512;
  tll_object* c_516; tll_object* x_517; tll_object* x_518; tll_object* x_519;
  zs_504 = env[0];
  __505 = env[1];
  hd_512 = env[2];
  x_518 = tll_ctor_set_tag(zs_504, 32); //consUL_32
  tll_ctor_set(x_518, hd_512, 0);
  tll_ctor_set(x_518, tll_box(31), 1);
  x_517 = tll_effect_send(__505, x_518);
  c_516 = x_517;
  x_519 = tll_effect_close0(c_516);
  return x_519;
}

tll_object* thunk__865(tll_object* env[]) {
  tll_object* __505; tll_object* c_508; tll_object* x_509; tll_object* x_510;
  __505 = env[0];
  x_509 = tll_effect_send(__505, tll_box(31));
  c_508 = x_509;
  x_510 = tll_effect_close0(c_508);
  return x_510;
}

tll_object* thunk__859(tll_object* env[]) {
  tll_object* rwlUU_7; tll_object* mergeU_350;
  tll_object* cmsort_workerU_430; tll_object* __431; tll_object* __433;
  tll_object* m_464; tll_object* n_465; tll_object* r1_467;
  tll_object* x_468; tll_object* x_469; tll_object* r2_474;
  tll_object* x_475; tll_object* x_476; tll_object* _481; tll_object* x_482;
  tll_object* x_483; tll_object* m_484; tll_object* n_485; tll_object* _486;
  tll_object* x_487; tll_object* x_488; tll_object* m_489; tll_object* n_490;
  tll_object* zs1_491; tll_object* x_492; tll_object* zs1_493;
  tll_object* x_494; tll_object* c_495; tll_object* x_496; tll_object* __497;
  tll_object* x_498; tll_object* __499; tll_object* x_500; tll_object* x_501;
  rwlUU_7 = env[0];
  mergeU_350 = env[1];
  cmsort_workerU_430 = env[2];
  __431 = env[3];
  __433 = env[4];
  m_464 = env[5];
  n_465 = env[6];
  x_469 = tll_closure_make(fn1_lam_860, 3, 1);
  tll_closure_set(x_469, cmsort_workerU_430, 1);
  tll_closure_set(x_469, __431, 2);
  tll_closure_set(x_469, m_464, 3);
  x_468 = tll_effect_fork(x_469);
  r1_467 = x_468;
  x_476 = tll_closure_make(fn1_lam_861, 3, 1);
  tll_closure_set(x_476, cmsort_workerU_430, 1);
  tll_closure_set(x_476, __431, 2);
  tll_closure_set(x_476, n_465, 3);
  x_475 = tll_effect_fork(x_476);
  r2_474 = x_475;
  x_482 = tll_effect_recv0(r1_467);
  _481 = x_482;
  m_484 = tll_ctor_get(_481, 0);
  n_485 = tll_ctor_get(_481, 1);
  x_487 = tll_effect_recv0(r2_474);
  _486 = x_487;
  m_489 = tll_ctor_get(_486, 0);
  n_490 = tll_ctor_get(_486, 1);
  x_492 = fn0_mergeU_842(m_484, m_489);
  zs1_491 = x_492;
  x_494 = fn0_rwlUU_688(NULL, NULL, NULL, NULL, NULL, zs1_491);
  zs1_493 = x_494;
  x_496 = tll_effect_send(__433, zs1_493);
  c_495 = x_496;
  x_498 = tll_effect_close1(n_485);
  __497 = x_498;
  x_500 = tll_effect_close1(n_490);
  __499 = x_500;
  x_501 = tll_effect_close0(c_495);
  x_488 = x_501;
  tll_free(_486);
  x_483 = x_488;
  tll_free(_481);
  return x_483;
}

tll_object* fn1_lam_860(tll_object* env[]) {
  tll_object* cmsort_workerU_430; tll_object* __431; tll_object* m_464;
  tll_object* lam_470; tll_object* _471; tll_object* x_472;
  tll_object* x_473;
  lam_470 = env[0];
  cmsort_workerU_430 = env[1];
  __431 = env[2];
  m_464 = env[3];
  _471 = env[4];
  x_473 = tll_int_sub(__431, tll_box(1));
  x_472 = fn0_cmsort_workerU_854(x_473, m_464, _471);
  return x_472;
}

tll_object* fn1_lam_861(tll_object* env[]) {
  tll_object* cmsort_workerU_430; tll_object* __431; tll_object* n_465;
  tll_object* lam_477; tll_object* _478; tll_object* x_479;
  tll_object* x_480;
  lam_477 = env[0];
  cmsort_workerU_430 = env[1];
  __431 = env[2];
  n_465 = env[3];
  _478 = env[4];
  x_480 = tll_int_sub(__431, tll_box(1));
  x_479 = fn0_cmsort_workerU_854(x_480, n_465, _478);
  return x_479;
}

tll_object* thunk__858(tll_object* env[]) {
  tll_object* msortU_390; tll_object* __433; tll_object* hd_440;
  tll_object* hd_449; tll_object* tl_450; tll_object* c_454;
  tll_object* x_455; tll_object* x_456; tll_object* x_457; tll_object* x_458;
  tll_object* x_459;
  msortU_390 = env[0];
  __433 = env[1];
  hd_440 = env[2];
  hd_449 = env[3];
  tl_450 = env[4];
  x_457 = tll_ctor_make(34, 2); //consUU_34
  tll_ctor_set(x_457, hd_449, 0);
  tll_ctor_set(x_457, tl_450, 1);
  x_458 = tll_ctor_make(34, 2); //consUU_34
  tll_ctor_set(x_458, hd_440, 0);
  tll_ctor_set(x_458, x_457, 1);
  x_456 = fn0_msortU_848(x_458);
  x_455 = tll_effect_send(__433, x_456);
  c_454 = x_455;
  x_459 = tll_effect_close0(c_454);
  return x_459;
}

tll_object* thunk__857(tll_object* env[]) {
  tll_object* __433; tll_object* hd_440; tll_object* c_444;
  tll_object* x_445; tll_object* x_446; tll_object* x_447;
  __433 = env[0];
  hd_440 = env[1];
  x_446 = tll_ctor_make(34, 2); //consUU_34
  tll_ctor_set(x_446, hd_440, 0);
  tll_ctor_set(x_446, tll_box(33), 1);
  x_445 = tll_effect_send(__433, x_446);
  c_444 = x_445;
  x_447 = tll_effect_close0(c_444);
  return x_447;
}

tll_object* thunk__856(tll_object* env[]) {
  tll_object* __433; tll_object* c_436; tll_object* x_437; tll_object* x_438;
  __433 = env[0];
  x_437 = tll_effect_send(__433, tll_box(33));
  c_436 = x_437;
  x_438 = tll_effect_close0(c_436);
  return x_438;
}

tll_object* fn1_aux_828(tll_object* env[]) {
  tll_object* ord_269; tll_object* chr_272; tll_object* str_275;
  tll_object* aux_286; tll_object* i_287; tll_object* x_288;
  tll_object* x_289; tll_object* r_290; tll_object* x_291; tll_object* i_292;
  tll_object* x_293; tll_object* x_294; tll_object* x_295; tll_object* x_296;
  tll_object* x_297; tll_object* x_298; tll_object* x_299; tll_object* x_300;
  tll_object* x_301; tll_object* x_302; tll_object* x_829;
  aux_286 = env[0];
  ord_269 = env[1];
  chr_272 = env[2];
  str_275 = env[3];
  i_287 = env[4];
  x_289 = tll_int_lte(tll_box(10), i_287);
  switch(tll_unbox(x_289)){
    case 4: //true_4
      x_291 = tll_int_mod(i_287, tll_box(10));
      r_290 = x_291;
      x_293 = tll_int_div(i_287, tll_box(10));
      i_292 = x_293;
      x_829 = tll_closure_app(aux_286, i_292);
      x_295 = x_829;
      x_298 = fn0_ord_814(tll_box('0'));
      x_297 = tll_int_add(r_290, x_298);
      x_296 = fn0_chr_817(x_297);
      x_294 = tll_string_pushback(x_295, x_296);
      x_288 = x_294;
      break;
    case 5: //false_5
      x_302 = fn0_ord_814(tll_box('0'));
      x_301 = tll_int_add(i_287, x_302);
      x_300 = fn0_chr_817(x_301);
      x_299 = fn0_str_820(x_300);
      x_288 = x_299;
      break;
  }
  return x_288;
}

tll_object* fn1_loop_806(tll_object* env[]) {
  tll_object* x_254; tll_object* m_256; tll_object* loop_259;
  tll_object* acc_260; tll_object* y_261; tll_object* x_262;
  tll_object* x_263; tll_object* x_264; tll_object* x_265; tll_object* x_266;
  tll_object* x_267; tll_object* x_807; tll_object* x_808;
  loop_259 = env[0];
  x_254 = env[1];
  m_256 = env[2];
  acc_260 = env[3];
  y_261 = env[4];
  x_263 = tll_int_lte(y_261, tll_box(0));
  switch(tll_unbox(x_263)){
    case 4: //true_4
      x_262 = acc_260;
      break;
    case 5: //false_5
      x_266 = tll_int_mul(x_254, acc_260);
      x_265 = tll_int_mod(x_266, m_256);
      x_267 = tll_int_sub(y_261, tll_box(1));
      x_807 = tll_closure_app(loop_259, x_265);
      x_808 = tll_closure_app(x_807, x_267);
      x_264 = x_808;
      x_262 = x_264;
      break;
  }
  return x_262;
}

tll_object* fn1_loop_796(tll_object* env[]) {
  tll_object* x_240; tll_object* loop_244; tll_object* acc_245;
  tll_object* y_246; tll_object* x_247; tll_object* x_248; tll_object* x_249;
  tll_object* x_250; tll_object* x_251; tll_object* x_797; tll_object* x_798;
  loop_244 = env[0];
  x_240 = env[1];
  acc_245 = env[2];
  y_246 = env[3];
  x_248 = tll_int_lte(y_246, tll_box(0));
  switch(tll_unbox(x_248)){
    case 4: //true_4
      x_247 = acc_245;
      break;
    case 5: //false_5
      x_250 = tll_int_mul(x_240, acc_245);
      x_251 = tll_int_sub(y_246, tll_box(1));
      x_797 = tll_closure_app(loop_244, x_250);
      x_798 = tll_closure_app(x_797, x_251);
      x_249 = x_798;
      x_247 = x_249;
      break;
  }
  return x_247;
}

tll_object* fn1_loop_759(tll_object* env[]) {
  tll_object* pred_118; tll_object* sub_131; tll_object* loop_154;
  tll_object* x_155; tll_object* y_156; tll_object* x_157; tll_object* x_158;
  tll_object* x_159; tll_object* x_160; tll_object* x_161; tll_object* x_162;
  tll_object* n_163; tll_object* x_164; tll_object* x_165; tll_object* x_760;
  tll_object* x_761;
  loop_154 = env[0];
  pred_118 = env[1];
  sub_131 = env[2];
  x_155 = env[3];
  y_156 = env[4];
  x_159 = fn0_pred_745(y_156);
  x_158 = fn0_sub_751(x_155, x_159);
  switch(tll_unbox(x_158)){
    case 6: //zero_6
      x_157 = tll_box(6);
      break;
    default:
      x_162 = fn0_pred_745(y_156);
      x_161 = fn0_sub_751(x_155, x_162);
      n_163 = tll_ctor_get(x_161, 0);
      x_760 = tll_closure_app(loop_154, n_163);
      x_761 = tll_closure_app(x_760, y_156);
      x_164 = x_761;
      x_165 = tll_ctor_make(7, 1); //succ_7
      tll_ctor_set(x_165, x_164, 0);
      x_160 = x_165;
      x_157 = x_160;
      break;
  }
  return x_157;
}

int main() {
  tll_init();
  tll_object* test_672; tll_object* x_673; tll_object* x_674;
  tll_object* x_904;
  idU_1 = tll_closure_make(fn1_idU_683, 0, 2);
  idL_4 = tll_closure_make(fn1_idL_686, 0, 2);
  rwlUU_7 = tll_closure_make(fn1_rwlUU_689, 0, 6);
  rwlUL_14 = tll_closure_make(fn1_rwlUL_692, 0, 6);
  rwlLU_21 = tll_closure_make(fn1_rwlLU_695, 0, 6);
  rwlLL_28 = tll_closure_make(fn1_rwlLL_698, 0, 6);
  rwrUU_35 = tll_closure_make(fn1_rwrUU_701, 0, 6);
  rwrUL_42 = tll_closure_make(fn1_rwrUL_704, 0, 6);
  rwrLU_49 = tll_closure_make(fn1_rwrLU_707, 0, 6);
  rwrLL_56 = tll_closure_make(fn1_rwrLL_710, 0, 6);
  sing_elimUU_63 = tll_closure_make(fn1_sing_elimUU_713, 0, 3);
  sing_elimUL_67 = tll_closure_make(fn1_sing_elimUL_716, 0, 3);
  sing_elimLU_71 = tll_closure_make(fn1_sing_elimLU_719, 0, 3);
  sing_elimLL_75 = tll_closure_make(fn1_sing_elimLL_722, 0, 3);
  not_79 = tll_closure_make(fn1_not_725, 0, 1);
  and_82 = tll_closure_make(fn1_and_728, 0, 2);
  or_87 = tll_closure_make(fn1_or_731, 0, 2);
  xor_92 = tll_closure_make(fn1_xor_734, 0, 2);
  string_of_bool_98 = tll_closure_make(fn1_string_of_bool_737, 0, 1);
  lte_103 = tll_closure_make(fn1_lte_740, 0, 2);
  lt_113 = tll_closure_make(fn1_lt_743, 0, 2);
  pred_118 = tll_closure_make(fn1_pred_746, 0, 1);
  add_123 = tll_closure_make(fn1_add_749, 0, 2);
  sub_131 = tll_closure_make(fn1_sub_752, 0, 2);
  mul_139 = tll_closure_make(fn1_mul_755, 0, 2);
  div_147 = tll_closure_make(fn1_div_758, 0, 2);
  rem_167 = tll_closure_make(fn1_rem_768, 0, 2);
  rconsUU_173 = tll_closure_make(fn1_rconsUU_771, 0, 3);
  rconsUL_184 = tll_closure_make(fn1_rconsUL_774, 0, 3);
  rconsLL_195 = tll_closure_make(fn1_rconsLL_777, 0, 3);
  free_listUU_206 = tll_closure_make(fn1_free_listUU_780, 0, 3);
  free_listUL_217 = tll_closure_make(fn1_free_listUL_785, 0, 3);
  free_listLL_228 = tll_closure_make(fn1_free_listLL_790, 0, 3);
  pow_239 = tll_closure_make(fn1_pow_795, 0, 2);
  powm_253 = tll_closure_make(fn1_powm_805, 0, 3);
  ord_269 = tll_closure_make(fn1_ord_815, 0, 1);
  chr_272 = tll_closure_make(fn1_chr_818, 0, 1);
  str_275 = tll_closure_make(fn1_str_821, 0, 1);
  strlen_279 = tll_closure_make(fn1_strlen_824, 0, 1);
  string_of_int_282 = tll_closure_make(fn1_string_of_int_827, 0, 1);
  splitU_310 = tll_closure_make(fn1_splitU_837, 0, 1);
  splitL_330 = tll_closure_make(fn1_splitL_840, 0, 1);
  mergeU_350 = tll_closure_make(fn1_mergeU_843, 0, 2);
  mergeL_370 = tll_closure_make(fn1_mergeL_846, 0, 2);
  msortU_390 = tll_closure_make(fn1_msortU_849, 0, 1);
  msortL_410 = tll_closure_make(fn1_msortL_852, 0, 1);
  cmsort_workerU_430 = tll_closure_make(fn1_cmsort_workerU_855, 0, 3);
  cmsort_workerL_502 = tll_closure_make(fn1_cmsort_workerL_864, 0, 3);
  cmsortU_574 = tll_closure_make(fn1_cmsortU_873, 0, 1);
  cmsortL_590 = tll_closure_make(fn1_cmsortL_878, 0, 1);
  mklistU_606 = tll_closure_make(fn1_mklistU_883, 0, 1);
  mklistL_613 = tll_closure_make(fn1_mklistL_886, 0, 1);
  list_lenU_620 = tll_closure_make(fn1_list_lenU_889, 0, 1);
  list_lenL_628 = tll_closure_make(fn1_list_lenL_892, 0, 1);
  print_listU_636 = tll_closure_make(fn1_print_listU_895, 0, 1);
  print_listL_654 = tll_closure_make(fn1_print_listL_900, 0, 1);
  x_673 = fn0_mklistL_885(tll_box(1000000));
  test_672 = x_673;
  x_674 = tll_thunk_make(thunk__905, 4);
  tll_thunk_set(x_674, string_of_int_282, 0);
  tll_thunk_set(x_674, cmsortL_590, 1);
  tll_thunk_set(x_674, list_lenL_628, 2);
  tll_thunk_set(x_674, test_672, 3);
  x_904 = tll_thunk_force(x_674);
  tll_exit();
}

