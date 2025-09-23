#include "main.h"

intptr_t idU_1; intptr_t idL_4; intptr_t rwlUU_7; intptr_t rwlUL_14;
intptr_t rwlLU_21; intptr_t rwlLL_28; intptr_t rwrUU_35; intptr_t rwrUL_42;
intptr_t rwrLU_49; intptr_t rwrLL_56; intptr_t sing_elimUU_63;
intptr_t sing_elimUL_67; intptr_t sing_elimLU_71; intptr_t sing_elimLL_75;
intptr_t not_79; intptr_t and_82; intptr_t or_87; intptr_t xor_92;
intptr_t string_of_bool_98; intptr_t lte_103; intptr_t lt_113;
intptr_t pred_118; intptr_t add_123; intptr_t sub_131; intptr_t mul_139;
intptr_t div_147; intptr_t rem_167; intptr_t rconsUU_173;
intptr_t rconsUL_184; intptr_t rconsLL_195; intptr_t free_listUU_206;
intptr_t free_listUL_217; intptr_t free_listLL_228; intptr_t pow_239;
intptr_t powm_253; intptr_t ord_269; intptr_t chr_272; intptr_t str_275;
intptr_t strlen_279; intptr_t string_of_int_282; intptr_t map_310;
intptr_t reduce_324; intptr_t leaf_worker_338; intptr_t node_worker_362;
intptr_t cleaf_418; intptr_t cnode_427; intptr_t ctree_of_tree_443;
intptr_t cfree_454; intptr_t cmap_464; intptr_t creduce_476;
intptr_t splitU_496; intptr_t splitL_516; intptr_t mergeU_536;
intptr_t mergeL_556; intptr_t msortU_576; intptr_t msortL_596;
intptr_t splitting_tree_616; intptr_t cmsort_640; intptr_t mklistU_665;
intptr_t mklistL_672; intptr_t list_lenU_679; intptr_t list_lenL_687;
intptr_t print_listU_695; intptr_t print_listL_713;

intptr_t fn0_idU_739(intptr_t A_2, intptr_t m_3) {
  
  
  return m_3;
}

intptr_t fn1_idU_740(intptr_t* env) {
  intptr_t A_2; intptr_t m_3; intptr_t x_741;
  A_2 = env[1];
  m_3 = env[2];
  x_741 = fn0_idU_739(A_2, m_3);
  return x_741;
}

intptr_t fn0_idL_742(intptr_t A_5, intptr_t m_6) {
  
  
  return m_6;
}

intptr_t fn1_idL_743(intptr_t* env) {
  intptr_t A_5; intptr_t m_6; intptr_t x_744;
  A_5 = env[1];
  m_6 = env[2];
  x_744 = fn0_idL_742(A_5, m_6);
  return x_744;
}

intptr_t fn0_rwlUU_745(intptr_t A_8, intptr_t m_9, intptr_t n_10, intptr_t B_11, intptr_t __12, intptr_t __13) {
  
  
  return __13;
}

intptr_t fn1_rwlUU_746(intptr_t* env) {
  intptr_t A_8; intptr_t m_9; intptr_t n_10; intptr_t B_11; intptr_t __12;
  intptr_t __13; intptr_t x_747;
  A_8 = env[1];
  m_9 = env[2];
  n_10 = env[3];
  B_11 = env[4];
  __12 = env[5];
  __13 = env[6];
  x_747 = fn0_rwlUU_745(A_8, m_9, n_10, B_11, __12, __13);
  return x_747;
}

intptr_t fn0_rwlUL_748(intptr_t A_15, intptr_t m_16, intptr_t n_17, intptr_t B_18, intptr_t __19, intptr_t __20) {
  
  
  return __20;
}

intptr_t fn1_rwlUL_749(intptr_t* env) {
  intptr_t A_15; intptr_t m_16; intptr_t n_17; intptr_t B_18; intptr_t __19;
  intptr_t __20; intptr_t x_750;
  A_15 = env[1];
  m_16 = env[2];
  n_17 = env[3];
  B_18 = env[4];
  __19 = env[5];
  __20 = env[6];
  x_750 = fn0_rwlUL_748(A_15, m_16, n_17, B_18, __19, __20);
  return x_750;
}

intptr_t fn0_rwlLU_751(intptr_t A_22, intptr_t m_23, intptr_t n_24, intptr_t B_25, intptr_t __26, intptr_t __27) {
  
  
  return __27;
}

intptr_t fn1_rwlLU_752(intptr_t* env) {
  intptr_t A_22; intptr_t m_23; intptr_t n_24; intptr_t B_25; intptr_t __26;
  intptr_t __27; intptr_t x_753;
  A_22 = env[1];
  m_23 = env[2];
  n_24 = env[3];
  B_25 = env[4];
  __26 = env[5];
  __27 = env[6];
  x_753 = fn0_rwlLU_751(A_22, m_23, n_24, B_25, __26, __27);
  return x_753;
}

intptr_t fn0_rwlLL_754(intptr_t A_29, intptr_t m_30, intptr_t n_31, intptr_t B_32, intptr_t __33, intptr_t __34) {
  
  
  return __34;
}

intptr_t fn1_rwlLL_755(intptr_t* env) {
  intptr_t A_29; intptr_t m_30; intptr_t n_31; intptr_t B_32; intptr_t __33;
  intptr_t __34; intptr_t x_756;
  A_29 = env[1];
  m_30 = env[2];
  n_31 = env[3];
  B_32 = env[4];
  __33 = env[5];
  __34 = env[6];
  x_756 = fn0_rwlLL_754(A_29, m_30, n_31, B_32, __33, __34);
  return x_756;
}

intptr_t fn0_rwrUU_757(intptr_t A_36, intptr_t m_37, intptr_t n_38, intptr_t B_39, intptr_t __40, intptr_t __41) {
  
  
  return __41;
}

intptr_t fn1_rwrUU_758(intptr_t* env) {
  intptr_t A_36; intptr_t m_37; intptr_t n_38; intptr_t B_39; intptr_t __40;
  intptr_t __41; intptr_t x_759;
  A_36 = env[1];
  m_37 = env[2];
  n_38 = env[3];
  B_39 = env[4];
  __40 = env[5];
  __41 = env[6];
  x_759 = fn0_rwrUU_757(A_36, m_37, n_38, B_39, __40, __41);
  return x_759;
}

intptr_t fn0_rwrUL_760(intptr_t A_43, intptr_t m_44, intptr_t n_45, intptr_t B_46, intptr_t __47, intptr_t __48) {
  
  
  return __48;
}

intptr_t fn1_rwrUL_761(intptr_t* env) {
  intptr_t A_43; intptr_t m_44; intptr_t n_45; intptr_t B_46; intptr_t __47;
  intptr_t __48; intptr_t x_762;
  A_43 = env[1];
  m_44 = env[2];
  n_45 = env[3];
  B_46 = env[4];
  __47 = env[5];
  __48 = env[6];
  x_762 = fn0_rwrUL_760(A_43, m_44, n_45, B_46, __47, __48);
  return x_762;
}

intptr_t fn0_rwrLU_763(intptr_t A_50, intptr_t m_51, intptr_t n_52, intptr_t B_53, intptr_t __54, intptr_t __55) {
  
  
  return __55;
}

intptr_t fn1_rwrLU_764(intptr_t* env) {
  intptr_t A_50; intptr_t m_51; intptr_t n_52; intptr_t B_53; intptr_t __54;
  intptr_t __55; intptr_t x_765;
  A_50 = env[1];
  m_51 = env[2];
  n_52 = env[3];
  B_53 = env[4];
  __54 = env[5];
  __55 = env[6];
  x_765 = fn0_rwrLU_763(A_50, m_51, n_52, B_53, __54, __55);
  return x_765;
}

intptr_t fn0_rwrLL_766(intptr_t A_57, intptr_t m_58, intptr_t n_59, intptr_t B_60, intptr_t __61, intptr_t __62) {
  
  
  return __62;
}

intptr_t fn1_rwrLL_767(intptr_t* env) {
  intptr_t A_57; intptr_t m_58; intptr_t n_59; intptr_t B_60; intptr_t __61;
  intptr_t __62; intptr_t x_768;
  A_57 = env[1];
  m_58 = env[2];
  n_59 = env[3];
  B_60 = env[4];
  __61 = env[5];
  __62 = env[6];
  x_768 = fn0_rwrLL_766(A_57, m_58, n_59, B_60, __61, __62);
  return x_768;
}

intptr_t fn0_sing_elimUU_769(intptr_t A_64, intptr_t x_65, intptr_t __66) {
  
  
  return __66;
}

intptr_t fn1_sing_elimUU_770(intptr_t* env) {
  intptr_t A_64; intptr_t x_65; intptr_t __66; intptr_t x_771;
  A_64 = env[1];
  x_65 = env[2];
  __66 = env[3];
  x_771 = fn0_sing_elimUU_769(A_64, x_65, __66);
  return x_771;
}

intptr_t fn0_sing_elimUL_772(intptr_t A_68, intptr_t x_69, intptr_t __70) {
  
  
  return __70;
}

intptr_t fn1_sing_elimUL_773(intptr_t* env) {
  intptr_t A_68; intptr_t x_69; intptr_t __70; intptr_t x_774;
  A_68 = env[1];
  x_69 = env[2];
  __70 = env[3];
  x_774 = fn0_sing_elimUL_772(A_68, x_69, __70);
  return x_774;
}

intptr_t fn0_sing_elimLU_775(intptr_t A_72, intptr_t x_73, intptr_t __74) {
  
  absurd();
  return nothing;
}

intptr_t fn1_sing_elimLU_776(intptr_t* env) {
  intptr_t A_72; intptr_t x_73; intptr_t __74; intptr_t x_777;
  A_72 = env[1];
  x_73 = env[2];
  __74 = env[3];
  x_777 = fn0_sing_elimLU_775(A_72, x_73, __74);
  return x_777;
}

intptr_t fn0_sing_elimLL_778(intptr_t A_76, intptr_t x_77, intptr_t __78) {
  
  
  return __78;
}

intptr_t fn1_sing_elimLL_779(intptr_t* env) {
  intptr_t A_76; intptr_t x_77; intptr_t __78; intptr_t x_780;
  A_76 = env[1];
  x_77 = env[2];
  __78 = env[3];
  x_780 = fn0_sing_elimLL_778(A_76, x_77, __78);
  return x_780;
}

intptr_t fn0_not_781(intptr_t __80) {
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

intptr_t fn1_not_782(intptr_t* env) {
  intptr_t __80; intptr_t x_783;
  __80 = env[1];
  x_783 = fn0_not_781(__80);
  return x_783;
}

intptr_t fn0_and_784(intptr_t __83, intptr_t __84) {
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

intptr_t fn1_and_785(intptr_t* env) {
  intptr_t __83; intptr_t __84; intptr_t x_786;
  __83 = env[1];
  __84 = env[2];
  x_786 = fn0_and_784(__83, __84);
  return x_786;
}

intptr_t fn0_or_787(intptr_t __88, intptr_t __89) {
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

intptr_t fn1_or_788(intptr_t* env) {
  intptr_t __88; intptr_t __89; intptr_t x_789;
  __88 = env[1];
  __89 = env[2];
  x_789 = fn0_or_787(__88, __89);
  return x_789;
}

intptr_t fn0_xor_790(intptr_t __93, intptr_t __94) {
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

intptr_t fn1_xor_791(intptr_t* env) {
  intptr_t __93; intptr_t __94; intptr_t x_792;
  __93 = env[1];
  __94 = env[2];
  x_792 = fn0_xor_790(__93, __94);
  return x_792;
}

intptr_t fn0_string_of_bool_793(intptr_t __99) {
  intptr_t x_100; intptr_t x_101; intptr_t x_102;
  switch(__99){
    case 4: //true_4
      x_101 = __str__("true");
      x_100 = x_101;
      break;
    case 5: //false_5
      x_102 = __str__("false");
      x_100 = x_102;
      break;
  }
  return x_100;
}

intptr_t fn1_string_of_bool_794(intptr_t* env) {
  intptr_t __99; intptr_t x_795;
  __99 = env[1];
  x_795 = fn0_string_of_bool_793(__99);
  return x_795;
}

intptr_t fn0_lte_796(intptr_t __104, intptr_t __105) {
  intptr_t x_106; intptr_t x_107; intptr_t n_108; intptr_t x_109;
  intptr_t x_110; intptr_t n_111; intptr_t x_112;
  switch(__104){
    case 6: //zero_6
      x_106 = 4;
      break;
    default:
      n_108 = getbox(__104, 0);
      switch(__105){
        case 6: //zero_6
          x_109 = 5;
          break;
        default:
          n_111 = getbox(__105, 0);
          x_112 = fn0_lte_796(n_108, n_111);
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

intptr_t fn1_lte_797(intptr_t* env) {
  intptr_t __104; intptr_t __105; intptr_t x_798;
  __104 = env[1];
  __105 = env[2];
  x_798 = fn0_lte_796(__104, __105);
  return x_798;
}

intptr_t fn0_lt_799(intptr_t x_114, intptr_t y_115) {
  intptr_t x_116; intptr_t x_117;
  x_117 = mkbox(7, 1); //succ_7
  setbox(x_117, x_114, 0);
  x_116 = fn0_lte_796(x_117, y_115);
  return x_116;
}

intptr_t fn1_lt_800(intptr_t* env) {
  intptr_t x_114; intptr_t y_115; intptr_t x_801;
  x_114 = env[1];
  y_115 = env[2];
  x_801 = fn0_lt_799(x_114, y_115);
  return x_801;
}

intptr_t fn0_pred_802(intptr_t __119) {
  intptr_t x_120; intptr_t x_121; intptr_t n_122;
  switch(__119){
    case 6: //zero_6
      x_120 = 6;
      break;
    default:
      n_122 = getbox(__119, 0);
      x_121 = n_122;
      x_120 = x_121;
      break;
  }
  return x_120;
}

intptr_t fn1_pred_803(intptr_t* env) {
  intptr_t __119; intptr_t x_804;
  __119 = env[1];
  x_804 = fn0_pred_802(__119);
  return x_804;
}

intptr_t fn0_add_805(intptr_t __124, intptr_t __125) {
  intptr_t x_126; intptr_t x_127; intptr_t n_128; intptr_t x_129;
  intptr_t x_130;
  switch(__124){
    case 6: //zero_6
      x_126 = __125;
      break;
    default:
      n_128 = getbox(__124, 0);
      x_129 = fn0_add_805(n_128, __125);
      x_130 = mkbox(7, 1); //succ_7
      setbox(x_130, x_129, 0);
      x_127 = x_130;
      x_126 = x_127;
      break;
  }
  return x_126;
}

intptr_t fn1_add_806(intptr_t* env) {
  intptr_t __124; intptr_t __125; intptr_t x_807;
  __124 = env[1];
  __125 = env[2];
  x_807 = fn0_add_805(__124, __125);
  return x_807;
}

intptr_t fn0_sub_808(intptr_t __132, intptr_t __133) {
  intptr_t x_134; intptr_t x_135; intptr_t n_136; intptr_t x_137;
  intptr_t x_138;
  switch(__133){
    case 6: //zero_6
      x_134 = __132;
      break;
    default:
      n_136 = getbox(__133, 0);
      x_138 = fn0_pred_802(__132);
      x_137 = fn0_sub_808(x_138, n_136);
      x_135 = x_137;
      x_134 = x_135;
      break;
  }
  return x_134;
}

intptr_t fn1_sub_809(intptr_t* env) {
  intptr_t __132; intptr_t __133; intptr_t x_810;
  __132 = env[1];
  __133 = env[2];
  x_810 = fn0_sub_808(__132, __133);
  return x_810;
}

intptr_t fn0_mul_811(intptr_t __140, intptr_t __141) {
  intptr_t x_142; intptr_t x_143; intptr_t n_144; intptr_t x_145;
  intptr_t x_146;
  switch(__140){
    case 6: //zero_6
      x_142 = 6;
      break;
    default:
      n_144 = getbox(__140, 0);
      x_146 = fn0_mul_811(n_144, __141);
      x_145 = fn0_add_805(__141, x_146);
      x_143 = x_145;
      x_142 = x_143;
      break;
  }
  return x_142;
}

intptr_t fn1_mul_812(intptr_t* env) {
  intptr_t __140; intptr_t __141; intptr_t x_813;
  __140 = env[1];
  __141 = env[2];
  x_813 = fn0_mul_811(__140, __141);
  return x_813;
}

intptr_t fn0_div_814(intptr_t x_148, intptr_t y_149) {
  intptr_t x_150; intptr_t x_151; intptr_t loop_152; intptr_t x_153;
  intptr_t x_166; intptr_t x_820; intptr_t x_821;
  x_151 = fn0_lt_799(x_148, y_149);
  switch(x_151){
    case 4: //true_4
      x_150 = 6;
      break;
    case 5: //false_5
      x_153 = mkclo(fn1_loop_816, 2, 2);
      setclo(x_153, pred_118, 1);
      setclo(x_153, sub_131, 2);
      loop_152 = x_153;
      x_820 = appc(loop_152, x_148);
      x_821 = appc(x_820, y_149);
      x_166 = x_821;
      x_150 = x_166;
      break;
  }
  return x_150;
}

intptr_t fn1_div_815(intptr_t* env) {
  intptr_t x_148; intptr_t y_149; intptr_t x_823;
  x_148 = env[1];
  y_149 = env[2];
  x_823 = fn0_div_814(x_148, y_149);
  return x_823;
}

intptr_t fn0_rem_824(intptr_t x_168, intptr_t y_169) {
  intptr_t x_170; intptr_t x_171; intptr_t x_172;
  x_172 = fn0_div_814(x_168, y_169);
  x_171 = fn0_mul_811(x_172, y_169);
  x_170 = fn0_sub_808(x_168, x_171);
  return x_170;
}

intptr_t fn1_rem_825(intptr_t* env) {
  intptr_t x_168; intptr_t y_169; intptr_t x_826;
  x_168 = env[1];
  y_169 = env[2];
  x_826 = fn0_rem_824(x_168, y_169);
  return x_826;
}

intptr_t fn0_rconsUU_827(intptr_t A_174, intptr_t __175, intptr_t __176) {
  intptr_t x_177; intptr_t x_178; intptr_t x_179; intptr_t hd_180;
  intptr_t tl_181; intptr_t x_182; intptr_t x_183;
  switch(__175){
    case 38: //nilUU_38
      x_178 = mkbox(39, 2); //consUU_39
      setbox(x_178, __176, 0);
      setbox(x_178, 38, 1);
      x_177 = x_178;
      break;
    default:
      hd_180 = getbox(__175, 0);
      tl_181 = getbox(__175, 1);
      x_182 = fn0_rconsUU_827(nothing, tl_181, __176);
      x_183 = mkbox(39, 2); //consUU_39
      setbox(x_183, hd_180, 0);
      setbox(x_183, x_182, 1);
      x_179 = x_183;
      x_177 = x_179;
      break;
  }
  return x_177;
}

intptr_t fn1_rconsUU_828(intptr_t* env) {
  intptr_t A_174; intptr_t __175; intptr_t __176; intptr_t x_829;
  A_174 = env[1];
  __175 = env[2];
  __176 = env[3];
  x_829 = fn0_rconsUU_827(A_174, __175, __176);
  return x_829;
}

intptr_t fn0_rconsUL_830(intptr_t A_185, intptr_t __186, intptr_t __187) {
  intptr_t x_188; intptr_t x_189; intptr_t x_190; intptr_t hd_191;
  intptr_t tl_192; intptr_t x_193; intptr_t x_194;
  switch(__186){
    case 36: //nilUL_36
      x_189 = mkbox(37, 2); //consUL_37
      setbox(x_189, __187, 0);
      setbox(x_189, 36, 1);
      x_188 = x_189;
      break;
    default:
      hd_191 = getbox(__186, 0);
      tl_192 = getbox(__186, 1);
      x_193 = fn0_rconsUL_830(nothing, tl_192, __187);
      x_194 = rebox(__186, 37); //consUL_37
      setbox(x_194, hd_191, 0);
      setbox(x_194, x_193, 1);
      x_190 = x_194;
      x_188 = x_190;
      break;
  }
  return x_188;
}

intptr_t fn1_rconsUL_831(intptr_t* env) {
  intptr_t A_185; intptr_t __186; intptr_t __187; intptr_t x_832;
  A_185 = env[1];
  __186 = env[2];
  __187 = env[3];
  x_832 = fn0_rconsUL_830(A_185, __186, __187);
  return x_832;
}

intptr_t fn0_rconsLL_833(intptr_t A_196, intptr_t __197, intptr_t __198) {
  intptr_t x_199; intptr_t x_200; intptr_t x_201; intptr_t hd_202;
  intptr_t tl_203; intptr_t x_204; intptr_t x_205;
  switch(__197){
    case 32: //nilLL_32
      x_200 = mkbox(33, 2); //consLL_33
      setbox(x_200, __198, 0);
      setbox(x_200, 32, 1);
      x_199 = x_200;
      break;
    default:
      hd_202 = getbox(__197, 0);
      tl_203 = getbox(__197, 1);
      x_204 = fn0_rconsLL_833(nothing, tl_203, __198);
      x_205 = rebox(__197, 33); //consLL_33
      setbox(x_205, hd_202, 0);
      setbox(x_205, x_204, 1);
      x_201 = x_205;
      x_199 = x_201;
      break;
  }
  return x_199;
}

intptr_t fn1_rconsLL_834(intptr_t* env) {
  intptr_t A_196; intptr_t __197; intptr_t __198; intptr_t x_835;
  A_196 = env[1];
  __197 = env[2];
  __198 = env[3];
  x_835 = fn0_rconsLL_833(A_196, __197, __198);
  return x_835;
}

intptr_t fn0_free_listUU_836(intptr_t A_207, intptr_t f_208, intptr_t __209) {
  intptr_t x_210; intptr_t x_211; intptr_t hd_212; intptr_t tl_213;
  intptr_t __214; intptr_t x_215; intptr_t x_216; intptr_t x_838;
  switch(__209){
    case 38: //nilUU_38
      x_210 = 27;
      break;
    default:
      hd_212 = getbox(__209, 0);
      tl_213 = getbox(__209, 1);
      x_838 = appc(f_208, hd_212);
      x_215 = x_838;
      __214 = x_215;
      x_216 = fn0_free_listUU_836(nothing, f_208, tl_213);
      x_211 = x_216;
      x_210 = x_211;
      break;
  }
  return x_210;
}

intptr_t fn1_free_listUU_837(intptr_t* env) {
  intptr_t A_207; intptr_t f_208; intptr_t __209; intptr_t x_840;
  A_207 = env[1];
  f_208 = env[2];
  __209 = env[3];
  x_840 = fn0_free_listUU_836(A_207, f_208, __209);
  return x_840;
}

intptr_t fn0_free_listUL_841(intptr_t A_218, intptr_t f_219, intptr_t __220) {
  intptr_t x_221; intptr_t x_222; intptr_t hd_223; intptr_t tl_224;
  intptr_t __225; intptr_t x_226; intptr_t x_227; intptr_t x_843;
  switch(__220){
    case 36: //nilUL_36
      x_221 = 27;
      break;
    default:
      hd_223 = getbox(__220, 0);
      tl_224 = getbox(__220, 1);
      x_843 = appc(f_219, hd_223);
      x_226 = x_843;
      __225 = x_226;
      x_227 = fn0_free_listUL_841(nothing, f_219, tl_224);
      x_222 = x_227;
      ffree(__220);
      x_221 = x_222;
      break;
  }
  return x_221;
}

intptr_t fn1_free_listUL_842(intptr_t* env) {
  intptr_t A_218; intptr_t f_219; intptr_t __220; intptr_t x_845;
  A_218 = env[1];
  f_219 = env[2];
  __220 = env[3];
  x_845 = fn0_free_listUL_841(A_218, f_219, __220);
  return x_845;
}

intptr_t fn0_free_listLL_846(intptr_t A_229, intptr_t f_230, intptr_t __231) {
  intptr_t x_232; intptr_t x_233; intptr_t hd_234; intptr_t tl_235;
  intptr_t __236; intptr_t x_237; intptr_t x_238; intptr_t x_848;
  switch(__231){
    case 32: //nilLL_32
      x_232 = 27;
      break;
    default:
      hd_234 = getbox(__231, 0);
      tl_235 = getbox(__231, 1);
      x_848 = appc(f_230, hd_234);
      x_237 = x_848;
      __236 = x_237;
      x_238 = fn0_free_listLL_846(nothing, f_230, tl_235);
      x_233 = x_238;
      ffree(__231);
      x_232 = x_233;
      break;
  }
  return x_232;
}

intptr_t fn1_free_listLL_847(intptr_t* env) {
  intptr_t A_229; intptr_t f_230; intptr_t __231; intptr_t x_850;
  A_229 = env[1];
  f_230 = env[2];
  __231 = env[3];
  x_850 = fn0_free_listLL_846(A_229, f_230, __231);
  return x_850;
}

intptr_t fn0_pow_851(intptr_t x_240, intptr_t y_241) {
  intptr_t loop_242; intptr_t x_243; intptr_t x_252; intptr_t x_857;
  intptr_t x_858;
  x_243 = mkclo(fn1_loop_853, 1, 2);
  setclo(x_243, x_240, 1);
  loop_242 = x_243;
  x_857 = appc(loop_242, 1);
  x_858 = appc(x_857, y_241);
  x_252 = x_858;
  return x_252;
}

intptr_t fn1_pow_852(intptr_t* env) {
  intptr_t x_240; intptr_t y_241; intptr_t x_860;
  x_240 = env[1];
  y_241 = env[2];
  x_860 = fn0_pow_851(x_240, y_241);
  return x_860;
}

intptr_t fn0_powm_861(intptr_t x_254, intptr_t y_255, intptr_t m_256) {
  intptr_t loop_257; intptr_t x_258; intptr_t x_268; intptr_t x_867;
  intptr_t x_868;
  x_258 = mkclo(fn1_loop_863, 2, 2);
  setclo(x_258, x_254, 1);
  setclo(x_258, m_256, 2);
  loop_257 = x_258;
  x_867 = appc(loop_257, 1);
  x_868 = appc(x_867, y_255);
  x_268 = x_868;
  return x_268;
}

intptr_t fn1_powm_862(intptr_t* env) {
  intptr_t x_254; intptr_t y_255; intptr_t m_256; intptr_t x_870;
  x_254 = env[1];
  y_255 = env[2];
  m_256 = env[3];
  x_870 = fn0_powm_861(x_254, y_255, m_256);
  return x_870;
}

intptr_t fn0_ord_871(intptr_t c_270) {
  intptr_t x_271;
  x_271 = __ord__(c_270);
  return x_271;
}

intptr_t fn1_ord_872(intptr_t* env) {
  intptr_t c_270; intptr_t x_873;
  c_270 = env[1];
  x_873 = fn0_ord_871(c_270);
  return x_873;
}

intptr_t fn0_chr_874(intptr_t i_273) {
  intptr_t x_274;
  x_274 = __chr__(i_273);
  return x_274;
}

intptr_t fn1_chr_875(intptr_t* env) {
  intptr_t i_273; intptr_t x_876;
  i_273 = env[1];
  x_876 = fn0_chr_874(i_273);
  return x_876;
}

intptr_t fn0_str_877(intptr_t c_276) {
  intptr_t x_277; intptr_t x_278;
  x_278 = __str__("");
  x_277 = __push__(x_278, c_276);
  return x_277;
}

intptr_t fn1_str_878(intptr_t* env) {
  intptr_t c_276; intptr_t x_879;
  c_276 = env[1];
  x_879 = fn0_str_877(c_276);
  return x_879;
}

intptr_t fn0_strlen_880(intptr_t s_280) {
  intptr_t x_281;
  x_281 = __size__(s_280);
  return x_281;
}

intptr_t fn1_strlen_881(intptr_t* env) {
  intptr_t s_280; intptr_t x_882;
  s_280 = env[1];
  x_882 = fn0_strlen_880(s_280);
  return x_882;
}

intptr_t fn0_string_of_int_883(intptr_t i_283) {
  intptr_t aux_284; intptr_t x_285; intptr_t x_303; intptr_t x_304;
  intptr_t x_305; intptr_t x_306; intptr_t x_307; intptr_t x_308;
  intptr_t x_309; intptr_t x_888; intptr_t x_890;
  x_285 = mkclo(fn1_aux_885, 3, 1);
  setclo(x_285, ord_269, 1);
  setclo(x_285, chr_272, 2);
  setclo(x_285, str_275, 3);
  aux_284 = x_285;
  x_304 = __lte__(0, i_283);
  switch(x_304){
    case 4: //true_4
      x_888 = appc(aux_284, i_283);
      x_305 = x_888;
      x_303 = x_305;
      break;
    case 5: //false_5
      x_307 = __str__("~");
      x_309 = __neg__(i_283);
      x_890 = appc(aux_284, x_309);
      x_308 = x_890;
      x_306 = __cat__(x_307, x_308);
      x_303 = x_306;
      break;
  }
  return x_303;
}

intptr_t fn1_string_of_int_884(intptr_t* env) {
  intptr_t i_283; intptr_t x_892;
  i_283 = env[1];
  x_892 = fn0_string_of_int_883(i_283);
  return x_892;
}

intptr_t fn0_map_893(intptr_t A_311, intptr_t B_312, intptr_t f_313, intptr_t __314) {
  intptr_t x_315; intptr_t x_316; intptr_t x_317; intptr_t x_318;
  intptr_t l_319; intptr_t r_320; intptr_t x_321; intptr_t x_322;
  intptr_t x_323; intptr_t x_895;
  switch(ctagof(__314)){
    case 15: //Leaf_15
      x_316 = getbox(__314, 0);
      x_895 = appc(f_313, x_316);
      x_317 = x_895;
      x_318 = mkbox(15, 1); //Leaf_15
      setbox(x_318, x_317, 0);
      x_315 = x_318;
      break;
    case 16: //Node_16
      l_319 = getbox(__314, 0);
      r_320 = getbox(__314, 1);
      x_321 = fn0_map_893(nothing, nothing, f_313, l_319);
      x_322 = fn0_map_893(nothing, nothing, f_313, r_320);
      x_323 = mkbox(16, 2); //Node_16
      setbox(x_323, x_321, 0);
      setbox(x_323, x_322, 1);
      x_315 = x_323;
      break;
  }
  return x_315;
}

intptr_t fn1_map_894(intptr_t* env) {
  intptr_t A_311; intptr_t B_312; intptr_t f_313; intptr_t __314;
  intptr_t x_897;
  A_311 = env[1];
  B_312 = env[2];
  f_313 = env[3];
  __314 = env[4];
  x_897 = fn0_map_893(A_311, B_312, f_313, __314);
  return x_897;
}

intptr_t fn0_reduce_898(intptr_t A_325, intptr_t B_326, intptr_t f_327, intptr_t g_328, intptr_t __329) {
  intptr_t x_330; intptr_t x_331; intptr_t x_332; intptr_t l_333;
  intptr_t r_334; intptr_t x_335; intptr_t x_336; intptr_t x_337;
  intptr_t x_900; intptr_t x_902; intptr_t x_903;
  switch(ctagof(__329)){
    case 15: //Leaf_15
      x_331 = getbox(__329, 0);
      x_900 = appc(f_327, x_331);
      x_332 = x_900;
      x_330 = x_332;
      break;
    case 16: //Node_16
      l_333 = getbox(__329, 0);
      r_334 = getbox(__329, 1);
      x_336 = fn0_reduce_898(nothing, nothing, f_327, g_328, l_333);
      x_337 = fn0_reduce_898(nothing, nothing, f_327, g_328, r_334);
      x_902 = appc(g_328, x_336);
      x_903 = appc(x_902, x_337);
      x_335 = x_903;
      x_330 = x_335;
      break;
  }
  return x_330;
}

intptr_t fn1_reduce_899(intptr_t* env) {
  intptr_t A_325; intptr_t B_326; intptr_t f_327; intptr_t g_328;
  intptr_t __329; intptr_t x_905;
  A_325 = env[1];
  B_326 = env[2];
  f_327 = env[3];
  g_328 = env[4];
  __329 = env[5];
  x_905 = fn0_reduce_898(A_325, B_326, f_327, g_328, __329);
  return x_905;
}

intptr_t fn0_leaf_worker_906(intptr_t A_339, intptr_t x_340, intptr_t c_341) {
  intptr_t x_342;
  x_342 = lazy(lazy__908, 3);
  setlazy(x_342, leaf_worker_338, 0);
  setlazy(x_342, x_340, 1);
  setlazy(x_342, c_341, 2);
  return x_342;
}

intptr_t fn1_leaf_worker_907(intptr_t* env) {
  intptr_t A_339; intptr_t x_340; intptr_t c_341; intptr_t x_913;
  A_339 = env[1];
  x_340 = env[2];
  c_341 = env[3];
  x_913 = fn0_leaf_worker_906(A_339, x_340, c_341);
  return x_913;
}

intptr_t fn0_node_worker_914(intptr_t A_363, intptr_t l_364, intptr_t r_365, intptr_t __366, intptr_t __367, intptr_t __368) {
  intptr_t x_369;
  x_369 = lazy(lazy__916, 4);
  setlazy(x_369, node_worker_362, 0);
  setlazy(x_369, __366, 1);
  setlazy(x_369, __367, 2);
  setlazy(x_369, __368, 3);
  return x_369;
}

intptr_t fn1_node_worker_915(intptr_t* env) {
  intptr_t A_363; intptr_t l_364; intptr_t r_365; intptr_t __366;
  intptr_t __367; intptr_t __368; intptr_t x_920;
  A_363 = env[1];
  l_364 = env[2];
  r_365 = env[3];
  __366 = env[4];
  __367 = env[5];
  __368 = env[6];
  x_920 = fn0_node_worker_914(A_363, l_364, r_365, __366, __367, __368);
  return x_920;
}

intptr_t fn0_cleaf_921(intptr_t A_419, intptr_t x_420) {
  intptr_t x_421;
  x_421 = lazy(lazy__923, 2);
  setlazy(x_421, leaf_worker_338, 0);
  setlazy(x_421, x_420, 1);
  return x_421;
}

intptr_t fn1_cleaf_922(intptr_t* env) {
  intptr_t A_419; intptr_t x_420; intptr_t x_925;
  A_419 = env[1];
  x_420 = env[2];
  x_925 = fn0_cleaf_921(A_419, x_420);
  return x_925;
}

intptr_t fn0_cnode_926(intptr_t A_428, intptr_t l_429, intptr_t r_430, intptr_t __431, intptr_t __432) {
  intptr_t x_433;
  x_433 = lazy(lazy__928, 3);
  setlazy(x_433, node_worker_362, 0);
  setlazy(x_433, __431, 1);
  setlazy(x_433, __432, 2);
  return x_433;
}

intptr_t fn1_cnode_927(intptr_t* env) {
  intptr_t A_428; intptr_t l_429; intptr_t r_430; intptr_t __431;
  intptr_t __432; intptr_t x_930;
  A_428 = env[1];
  l_429 = env[2];
  r_430 = env[3];
  __431 = env[4];
  __432 = env[5];
  x_930 = fn0_cnode_926(A_428, l_429, r_430, __431, __432);
  return x_930;
}

intptr_t fn0_ctree_of_tree_931(intptr_t A_444, intptr_t t_445) {
  intptr_t x_446; intptr_t x_447; intptr_t x_448; intptr_t l_449;
  intptr_t r_450; intptr_t x_451; intptr_t x_452; intptr_t x_453;
  switch(ctagof(t_445)){
    case 15: //Leaf_15
      x_447 = getbox(t_445, 0);
      x_448 = fn0_cleaf_921(nothing, x_447);
      x_446 = x_448;
      break;
    case 16: //Node_16
      l_449 = getbox(t_445, 0);
      r_450 = getbox(t_445, 1);
      x_452 = fn0_ctree_of_tree_931(nothing, l_449);
      x_453 = fn0_ctree_of_tree_931(nothing, r_450);
      x_451 = fn0_cnode_926(nothing, nothing, nothing, x_452, x_453);
      x_446 = x_451;
      break;
  }
  return x_446;
}

intptr_t fn1_ctree_of_tree_932(intptr_t* env) {
  intptr_t A_444; intptr_t t_445; intptr_t x_933;
  A_444 = env[1];
  t_445 = env[2];
  x_933 = fn0_ctree_of_tree_931(A_444, t_445);
  return x_933;
}

intptr_t fn0_cfree_934(intptr_t A_455, intptr_t t_456, intptr_t ct_457) {
  intptr_t x_458;
  x_458 = lazy(lazy__936, 1);
  setlazy(x_458, ct_457, 0);
  return x_458;
}

intptr_t fn1_cfree_935(intptr_t* env) {
  intptr_t A_455; intptr_t t_456; intptr_t ct_457; intptr_t x_937;
  A_455 = env[1];
  t_456 = env[2];
  ct_457 = env[3];
  x_937 = fn0_cfree_934(A_455, t_456, ct_457);
  return x_937;
}

intptr_t fn0_cmap_938(intptr_t A_465, intptr_t B_466, intptr_t t_467, intptr_t f_468, intptr_t ct_469) {
  intptr_t x_470;
  x_470 = lazy(lazy__940, 2);
  setlazy(x_470, f_468, 0);
  setlazy(x_470, ct_469, 1);
  return x_470;
}

intptr_t fn1_cmap_939(intptr_t* env) {
  intptr_t A_465; intptr_t B_466; intptr_t t_467; intptr_t f_468;
  intptr_t ct_469; intptr_t x_941;
  A_465 = env[1];
  B_466 = env[2];
  t_467 = env[3];
  f_468 = env[4];
  ct_469 = env[5];
  x_941 = fn0_cmap_938(A_465, B_466, t_467, f_468, ct_469);
  return x_941;
}

intptr_t fn0_creduce_942(intptr_t A_477, intptr_t B_478, intptr_t t_479, intptr_t f_480, intptr_t g_481, intptr_t ct_482) {
  intptr_t x_483;
  x_483 = lazy(lazy__944, 3);
  setlazy(x_483, f_480, 0);
  setlazy(x_483, g_481, 1);
  setlazy(x_483, ct_482, 2);
  return x_483;
}

intptr_t fn1_creduce_943(intptr_t* env) {
  intptr_t A_477; intptr_t B_478; intptr_t t_479; intptr_t f_480;
  intptr_t g_481; intptr_t ct_482; intptr_t x_946;
  A_477 = env[1];
  B_478 = env[2];
  t_479 = env[3];
  f_480 = env[4];
  g_481 = env[5];
  ct_482 = env[6];
  x_946 = fn0_creduce_942(A_477, B_478, t_479, f_480, g_481, ct_482);
  return x_946;
}

intptr_t fn0_splitU_947(intptr_t __497) {
  intptr_t x_498; intptr_t x_499; intptr_t x_500; intptr_t hd_501;
  intptr_t tl_502; intptr_t x_503; intptr_t x_504; intptr_t x_505;
  intptr_t x_506; intptr_t hd_507; intptr_t tl_508; intptr_t x_509;
  intptr_t x_510; intptr_t m_511; intptr_t n_512; intptr_t x_513;
  intptr_t x_514; intptr_t x_515;
  switch(__497){
    case 38: //nilUU_38
      x_499 = mkbox(51, 2); //ex1UU_51
      setbox(x_499, 38, 0);
      setbox(x_499, 38, 1);
      x_498 = x_499;
      break;
    default:
      hd_501 = getbox(__497, 0);
      tl_502 = getbox(__497, 1);
      switch(tl_502){
        case 38: //nilUU_38
          x_504 = mkbox(39, 2); //consUU_39
          setbox(x_504, hd_501, 0);
          setbox(x_504, 38, 1);
          x_505 = mkbox(51, 2); //ex1UU_51
          setbox(x_505, x_504, 0);
          setbox(x_505, 38, 1);
          x_503 = x_505;
          break;
        default:
          hd_507 = getbox(tl_502, 0);
          tl_508 = getbox(tl_502, 1);
          x_510 = fn0_splitU_947(tl_508);
          m_511 = getbox(x_510, 0);
          n_512 = getbox(x_510, 1);
          x_513 = rebox(x_510, 39); //consUU_39
          setbox(x_513, hd_501, 0);
          setbox(x_513, m_511, 1);
          x_514 = mkbox(39, 2); //consUU_39
          setbox(x_514, hd_507, 0);
          setbox(x_514, n_512, 1);
          x_515 = mkbox(51, 2); //ex1UU_51
          setbox(x_515, x_513, 0);
          setbox(x_515, x_514, 1);
          x_509 = x_515;
          x_506 = x_509;
          x_503 = x_506;
          break;
      }
      x_500 = x_503;
      x_498 = x_500;
      break;
  }
  return x_498;
}

intptr_t fn1_splitU_948(intptr_t* env) {
  intptr_t __497; intptr_t x_949;
  __497 = env[1];
  x_949 = fn0_splitU_947(__497);
  return x_949;
}

intptr_t fn0_splitL_950(intptr_t __517) {
  intptr_t x_518; intptr_t x_519; intptr_t x_520; intptr_t hd_521;
  intptr_t tl_522; intptr_t x_523; intptr_t x_524; intptr_t x_525;
  intptr_t x_526; intptr_t hd_527; intptr_t tl_528; intptr_t x_529;
  intptr_t x_530; intptr_t m_531; intptr_t n_532; intptr_t x_533;
  intptr_t x_534; intptr_t x_535;
  switch(__517){
    case 36: //nilUL_36
      x_519 = mkbox(48, 2); //ex1LL_48
      setbox(x_519, 36, 0);
      setbox(x_519, 36, 1);
      x_518 = x_519;
      break;
    default:
      hd_521 = getbox(__517, 0);
      tl_522 = getbox(__517, 1);
      switch(tl_522){
        case 36: //nilUL_36
          x_524 = rebox(__517, 37); //consUL_37
          setbox(x_524, hd_521, 0);
          setbox(x_524, 36, 1);
          x_525 = mkbox(48, 2); //ex1LL_48
          setbox(x_525, x_524, 0);
          setbox(x_525, 36, 1);
          x_523 = x_525;
          break;
        default:
          hd_527 = getbox(tl_522, 0);
          tl_528 = getbox(tl_522, 1);
          x_530 = fn0_splitL_950(tl_528);
          m_531 = getbox(x_530, 0);
          n_532 = getbox(x_530, 1);
          x_533 = rebox(x_530, 37); //consUL_37
          setbox(x_533, hd_521, 0);
          setbox(x_533, m_531, 1);
          x_534 = rebox(tl_522, 37); //consUL_37
          setbox(x_534, hd_527, 0);
          setbox(x_534, n_532, 1);
          x_535 = rebox(__517, 48); //ex1LL_48
          setbox(x_535, x_533, 0);
          setbox(x_535, x_534, 1);
          x_529 = x_535;
          x_526 = x_529;
          x_523 = x_526;
          break;
      }
      x_520 = x_523;
      x_518 = x_520;
      break;
  }
  return x_518;
}

intptr_t fn1_splitL_951(intptr_t* env) {
  intptr_t __517; intptr_t x_952;
  __517 = env[1];
  x_952 = fn0_splitL_950(__517);
  return x_952;
}

intptr_t fn0_mergeU_953(intptr_t __537, intptr_t __538) {
  intptr_t x_539; intptr_t x_540; intptr_t hd_541; intptr_t tl_542;
  intptr_t x_543; intptr_t x_544; intptr_t x_545; intptr_t hd_546;
  intptr_t tl_547; intptr_t x_548; intptr_t x_549; intptr_t x_550;
  intptr_t x_551; intptr_t x_552; intptr_t x_553; intptr_t x_554;
  intptr_t x_555;
  switch(__537){
    case 38: //nilUU_38
      x_539 = __538;
      break;
    default:
      hd_541 = getbox(__537, 0);
      tl_542 = getbox(__537, 1);
      switch(__538){
        case 38: //nilUU_38
          x_544 = mkbox(39, 2); //consUU_39
          setbox(x_544, hd_541, 0);
          setbox(x_544, tl_542, 1);
          x_543 = x_544;
          break;
        default:
          hd_546 = getbox(__538, 0);
          tl_547 = getbox(__538, 1);
          x_549 = __lte__(hd_541, hd_546);
          switch(x_549){
            case 4: //true_4
              x_551 = mkbox(39, 2); //consUU_39
              setbox(x_551, hd_546, 0);
              setbox(x_551, tl_547, 1);
              x_550 = fn0_mergeU_953(tl_542, x_551);
              x_552 = mkbox(39, 2); //consUU_39
              setbox(x_552, hd_541, 0);
              setbox(x_552, x_550, 1);
              x_548 = x_552;
              break;
            case 5: //false_5
              x_554 = mkbox(39, 2); //consUU_39
              setbox(x_554, hd_541, 0);
              setbox(x_554, tl_542, 1);
              x_553 = fn0_mergeU_953(x_554, tl_547);
              x_555 = mkbox(39, 2); //consUU_39
              setbox(x_555, hd_546, 0);
              setbox(x_555, x_553, 1);
              x_548 = x_555;
              break;
          }
          x_545 = x_548;
          x_543 = x_545;
          break;
      }
      x_540 = x_543;
      x_539 = x_540;
      break;
  }
  return x_539;
}

intptr_t fn1_mergeU_954(intptr_t* env) {
  intptr_t __537; intptr_t __538; intptr_t x_955;
  __537 = env[1];
  __538 = env[2];
  x_955 = fn0_mergeU_953(__537, __538);
  return x_955;
}

intptr_t fn0_mergeL_956(intptr_t __557, intptr_t __558) {
  intptr_t x_559; intptr_t x_560; intptr_t hd_561; intptr_t tl_562;
  intptr_t x_563; intptr_t x_564; intptr_t x_565; intptr_t hd_566;
  intptr_t tl_567; intptr_t x_568; intptr_t x_569; intptr_t x_570;
  intptr_t x_571; intptr_t x_572; intptr_t x_573; intptr_t x_574;
  intptr_t x_575;
  switch(__557){
    case 36: //nilUL_36
      x_559 = __558;
      break;
    default:
      hd_561 = getbox(__557, 0);
      tl_562 = getbox(__557, 1);
      switch(__558){
        case 36: //nilUL_36
          x_564 = rebox(__557, 37); //consUL_37
          setbox(x_564, hd_561, 0);
          setbox(x_564, tl_562, 1);
          x_563 = x_564;
          break;
        default:
          hd_566 = getbox(__558, 0);
          tl_567 = getbox(__558, 1);
          x_569 = __lte__(hd_561, hd_566);
          switch(x_569){
            case 4: //true_4
              x_571 = rebox(__558, 37); //consUL_37
              setbox(x_571, hd_566, 0);
              setbox(x_571, tl_567, 1);
              x_570 = fn0_mergeL_956(tl_562, x_571);
              x_572 = rebox(__557, 37); //consUL_37
              setbox(x_572, hd_561, 0);
              setbox(x_572, x_570, 1);
              x_568 = x_572;
              break;
            case 5: //false_5
              x_574 = rebox(__558, 37); //consUL_37
              setbox(x_574, hd_561, 0);
              setbox(x_574, tl_562, 1);
              x_573 = fn0_mergeL_956(x_574, tl_567);
              x_575 = rebox(__557, 37); //consUL_37
              setbox(x_575, hd_566, 0);
              setbox(x_575, x_573, 1);
              x_568 = x_575;
              break;
          }
          x_565 = x_568;
          x_563 = x_565;
          break;
      }
      x_560 = x_563;
      x_559 = x_560;
      break;
  }
  return x_559;
}

intptr_t fn1_mergeL_957(intptr_t* env) {
  intptr_t __557; intptr_t __558; intptr_t x_958;
  __557 = env[1];
  __558 = env[2];
  x_958 = fn0_mergeL_956(__557, __558);
  return x_958;
}

intptr_t fn0_msortU_959(intptr_t __577) {
  intptr_t x_578; intptr_t x_579; intptr_t hd_580; intptr_t tl_581;
  intptr_t x_582; intptr_t x_583; intptr_t x_584; intptr_t hd_585;
  intptr_t tl_586; intptr_t x_587; intptr_t x_588; intptr_t x_589;
  intptr_t x_590; intptr_t m_591; intptr_t n_592; intptr_t x_593;
  intptr_t x_594; intptr_t x_595;
  switch(__577){
    case 38: //nilUU_38
      x_578 = 38;
      break;
    default:
      hd_580 = getbox(__577, 0);
      tl_581 = getbox(__577, 1);
      switch(tl_581){
        case 38: //nilUU_38
          x_583 = mkbox(39, 2); //consUU_39
          setbox(x_583, hd_580, 0);
          setbox(x_583, 38, 1);
          x_582 = x_583;
          break;
        default:
          hd_585 = getbox(tl_581, 0);
          tl_586 = getbox(tl_581, 1);
          x_589 = mkbox(39, 2); //consUU_39
          setbox(x_589, hd_585, 0);
          setbox(x_589, tl_586, 1);
          x_590 = mkbox(39, 2); //consUU_39
          setbox(x_590, hd_580, 0);
          setbox(x_590, x_589, 1);
          x_588 = fn0_splitU_947(x_590);
          m_591 = getbox(x_588, 0);
          n_592 = getbox(x_588, 1);
          x_594 = fn0_msortU_959(m_591);
          x_595 = fn0_msortU_959(n_592);
          x_593 = fn0_mergeU_953(x_594, x_595);
          x_587 = x_593;
          ffree(x_588);
          x_584 = x_587;
          x_582 = x_584;
          break;
      }
      x_579 = x_582;
      x_578 = x_579;
      break;
  }
  return x_578;
}

intptr_t fn1_msortU_960(intptr_t* env) {
  intptr_t __577; intptr_t x_961;
  __577 = env[1];
  x_961 = fn0_msortU_959(__577);
  return x_961;
}

intptr_t fn0_msortL_962(intptr_t __597) {
  intptr_t x_598; intptr_t x_599; intptr_t hd_600; intptr_t tl_601;
  intptr_t x_602; intptr_t x_603; intptr_t x_604; intptr_t hd_605;
  intptr_t tl_606; intptr_t x_607; intptr_t x_608; intptr_t x_609;
  intptr_t x_610; intptr_t m_611; intptr_t n_612; intptr_t x_613;
  intptr_t x_614; intptr_t x_615;
  switch(__597){
    case 36: //nilUL_36
      x_598 = 36;
      break;
    default:
      hd_600 = getbox(__597, 0);
      tl_601 = getbox(__597, 1);
      switch(tl_601){
        case 36: //nilUL_36
          x_603 = rebox(__597, 37); //consUL_37
          setbox(x_603, hd_600, 0);
          setbox(x_603, 36, 1);
          x_602 = x_603;
          break;
        default:
          hd_605 = getbox(tl_601, 0);
          tl_606 = getbox(tl_601, 1);
          x_609 = rebox(tl_601, 37); //consUL_37
          setbox(x_609, hd_605, 0);
          setbox(x_609, tl_606, 1);
          x_610 = rebox(__597, 37); //consUL_37
          setbox(x_610, hd_600, 0);
          setbox(x_610, x_609, 1);
          x_608 = fn0_splitL_950(x_610);
          m_611 = getbox(x_608, 0);
          n_612 = getbox(x_608, 1);
          x_614 = fn0_msortL_962(m_611);
          x_615 = fn0_msortL_962(n_612);
          x_613 = fn0_mergeL_956(x_614, x_615);
          x_607 = x_613;
          ffree(x_608);
          x_604 = x_607;
          x_602 = x_604;
          break;
      }
      x_599 = x_602;
      x_598 = x_599;
      break;
  }
  return x_598;
}

intptr_t fn1_msortL_963(intptr_t* env) {
  intptr_t __597; intptr_t x_964;
  __597 = env[1];
  x_964 = fn0_msortL_962(__597);
  return x_964;
}

intptr_t fn0_splitting_tree_965(intptr_t __617) {
  intptr_t x_618; intptr_t x_619; intptr_t x_620; intptr_t hd_621;
  intptr_t tl_622; intptr_t x_623; intptr_t x_624; intptr_t x_625;
  intptr_t x_626; intptr_t hd_627; intptr_t tl_628; intptr_t x_629;
  intptr_t x_630; intptr_t x_631; intptr_t x_632; intptr_t m_633;
  intptr_t n_634; intptr_t l_635; intptr_t x_636; intptr_t r_637;
  intptr_t x_638; intptr_t x_639;
  switch(__617){
    case 38: //nilUU_38
      x_619 = mkbox(15, 1); //Leaf_15
      setbox(x_619, 38, 0);
      x_618 = x_619;
      break;
    default:
      hd_621 = getbox(__617, 0);
      tl_622 = getbox(__617, 1);
      switch(tl_622){
        case 38: //nilUU_38
          x_624 = mkbox(39, 2); //consUU_39
          setbox(x_624, hd_621, 0);
          setbox(x_624, 38, 1);
          x_625 = mkbox(15, 1); //Leaf_15
          setbox(x_625, x_624, 0);
          x_623 = x_625;
          break;
        default:
          hd_627 = getbox(tl_622, 0);
          tl_628 = getbox(tl_622, 1);
          x_631 = mkbox(39, 2); //consUU_39
          setbox(x_631, hd_627, 0);
          setbox(x_631, tl_628, 1);
          x_632 = mkbox(39, 2); //consUU_39
          setbox(x_632, hd_621, 0);
          setbox(x_632, x_631, 1);
          x_630 = fn0_splitU_947(x_632);
          m_633 = getbox(x_630, 0);
          n_634 = getbox(x_630, 1);
          x_636 = fn0_splitting_tree_965(m_633);
          l_635 = x_636;
          x_638 = fn0_splitting_tree_965(n_634);
          r_637 = x_638;
          x_639 = rebox(x_630, 16); //Node_16
          setbox(x_639, l_635, 0);
          setbox(x_639, r_637, 1);
          x_629 = x_639;
          x_626 = x_629;
          x_623 = x_626;
          break;
      }
      x_620 = x_623;
      x_618 = x_620;
      break;
  }
  return x_618;
}

intptr_t fn1_splitting_tree_966(intptr_t* env) {
  intptr_t __617; intptr_t x_967;
  __617 = env[1];
  x_967 = fn0_splitting_tree_965(__617);
  return x_967;
}

intptr_t fn0_cmsort_968(intptr_t xs_641) {
  intptr_t ct_642; intptr_t x_643; intptr_t x_644; intptr_t x_645;
  x_644 = fn0_splitting_tree_965(xs_641);
  x_643 = fn0_ctree_of_tree_931(nothing, x_644);
  ct_642 = x_643;
  x_645 = lazy(lazy__970, 5);
  setlazy(x_645, rwlUU_7, 0);
  setlazy(x_645, cfree_454, 1);
  setlazy(x_645, creduce_476, 2);
  setlazy(x_645, mergeU_536, 3);
  setlazy(x_645, ct_642, 4);
  return x_645;
}

intptr_t fn1_cmsort_969(intptr_t* env) {
  intptr_t xs_641; intptr_t x_973;
  xs_641 = env[1];
  x_973 = fn0_cmsort_968(xs_641);
  return x_973;
}

intptr_t fn0_mklistU_974(intptr_t n_666) {
  intptr_t x_667; intptr_t x_668; intptr_t x_669; intptr_t x_670;
  intptr_t x_671;
  x_668 = __lte__(n_666, 0);
  switch(x_668){
    case 4: //true_4
      x_667 = 38;
      break;
    case 5: //false_5
      x_670 = __sub__(n_666, 1);
      x_669 = fn0_mklistU_974(x_670);
      x_671 = mkbox(39, 2); //consUU_39
      setbox(x_671, n_666, 0);
      setbox(x_671, x_669, 1);
      x_667 = x_671;
      break;
  }
  return x_667;
}

intptr_t fn1_mklistU_975(intptr_t* env) {
  intptr_t n_666; intptr_t x_976;
  n_666 = env[1];
  x_976 = fn0_mklistU_974(n_666);
  return x_976;
}

intptr_t fn0_mklistL_977(intptr_t n_673) {
  intptr_t x_674; intptr_t x_675; intptr_t x_676; intptr_t x_677;
  intptr_t x_678;
  x_675 = __lte__(n_673, 0);
  switch(x_675){
    case 4: //true_4
      x_674 = 36;
      break;
    case 5: //false_5
      x_677 = __sub__(n_673, 1);
      x_676 = fn0_mklistL_977(x_677);
      x_678 = mkbox(37, 2); //consUL_37
      setbox(x_678, n_673, 0);
      setbox(x_678, x_676, 1);
      x_674 = x_678;
      break;
  }
  return x_674;
}

intptr_t fn1_mklistL_978(intptr_t* env) {
  intptr_t n_673; intptr_t x_979;
  n_673 = env[1];
  x_979 = fn0_mklistL_977(n_673);
  return x_979;
}

intptr_t fn0_list_lenU_980(intptr_t __680) {
  intptr_t x_681; intptr_t x_682; intptr_t tl_684; intptr_t x_685;
  intptr_t x_686;
  switch(__680){
    case 38: //nilUU_38
      x_681 = 0;
      break;
    default:
      tl_684 = getbox(__680, 1);
      x_686 = fn0_list_lenU_980(tl_684);
      x_685 = __add__(1, x_686);
      x_682 = x_685;
      x_681 = x_682;
      break;
  }
  return x_681;
}

intptr_t fn1_list_lenU_981(intptr_t* env) {
  intptr_t __680; intptr_t x_982;
  __680 = env[1];
  x_982 = fn0_list_lenU_980(__680);
  return x_982;
}

intptr_t fn0_list_lenL_983(intptr_t __688) {
  intptr_t x_689; intptr_t x_690; intptr_t tl_692; intptr_t x_693;
  intptr_t x_694;
  switch(__688){
    case 36: //nilUL_36
      x_689 = 0;
      break;
    default:
      tl_692 = getbox(__688, 1);
      x_694 = fn0_list_lenL_983(tl_692);
      x_693 = __add__(1, x_694);
      x_690 = x_693;
      ffree(__688);
      x_689 = x_690;
      break;
  }
  return x_689;
}

intptr_t fn1_list_lenL_984(intptr_t* env) {
  intptr_t __688; intptr_t x_985;
  __688 = env[1];
  x_985 = fn0_list_lenL_983(__688);
  return x_985;
}

intptr_t fn0_print_listU_986(intptr_t __696) {
  intptr_t x_697; intptr_t x_698; intptr_t x_701; intptr_t hd_702;
  intptr_t tl_703; intptr_t x_704;
  switch(__696){
    case 38: //nilUU_38
      x_698 = lazy(lazy__988, 0);
      x_697 = x_698;
      break;
    default:
      hd_702 = getbox(__696, 0);
      tl_703 = getbox(__696, 1);
      x_704 = lazy(lazy__989, 4);
      setlazy(x_704, string_of_int_282, 0);
      setlazy(x_704, print_listU_695, 1);
      setlazy(x_704, hd_702, 2);
      setlazy(x_704, tl_703, 3);
      x_701 = x_704;
      x_697 = x_701;
      break;
  }
  return x_697;
}

intptr_t fn1_print_listU_987(intptr_t* env) {
  intptr_t __696; intptr_t x_990;
  __696 = env[1];
  x_990 = fn0_print_listU_986(__696);
  return x_990;
}

intptr_t fn0_print_listL_991(intptr_t __714) {
  intptr_t x_715; intptr_t x_716; intptr_t x_719; intptr_t hd_720;
  intptr_t tl_721; intptr_t x_722;
  switch(__714){
    case 36: //nilUL_36
      x_716 = lazy(lazy__993, 0);
      x_715 = x_716;
      break;
    default:
      hd_720 = getbox(__714, 0);
      tl_721 = getbox(__714, 1);
      x_722 = lazy(lazy__994, 4);
      setlazy(x_722, string_of_int_282, 0);
      setlazy(x_722, print_listL_713, 1);
      setlazy(x_722, hd_720, 2);
      setlazy(x_722, tl_721, 3);
      x_719 = x_722;
      ffree(__714);
      x_715 = x_719;
      break;
  }
  return x_715;
}

intptr_t fn1_print_listL_992(intptr_t* env) {
  intptr_t __714; intptr_t x_995;
  __714 = env[1];
  x_995 = fn0_print_listL_991(__714);
  return x_995;
}

intptr_t lazy__997(intptr_t* env) {
  intptr_t cmsort_640; intptr_t print_listU_695; intptr_t test_731;
  intptr_t _734; intptr_t x_735; intptr_t x_736; intptr_t x_737;
  intptr_t x_738;
  cmsort_640 = env[0];
  print_listU_695 = env[1];
  test_731 = env[2];
  x_736 = fn0_cmsort_968(test_731);
  x_735 = force(x_736);
  ffree(x_736);
  _734 = x_735;
  x_738 = fn0_print_listU_986(_734);
  x_737 = force(x_738);
  ffree(x_738);
  return x_737;
}

intptr_t lazy__994(intptr_t* env) {
  intptr_t string_of_int_282; intptr_t print_listL_713; intptr_t hd_720;
  intptr_t tl_721; intptr_t __723; intptr_t x_724; intptr_t x_725;
  intptr_t __726; intptr_t x_727; intptr_t x_728; intptr_t x_729;
  intptr_t x_730;
  string_of_int_282 = env[0];
  print_listL_713 = env[1];
  hd_720 = env[2];
  tl_721 = env[3];
  x_725 = fn0_string_of_int_883(hd_720);
  x_724 = __print__(x_725);
  __723 = x_724;
  x_728 = __str__(" :: ");
  x_727 = __print__(x_728);
  __726 = x_727;
  x_730 = fn0_print_listL_991(tl_721);
  x_729 = force(x_730);
  ffree(x_730);
  return x_729;
}

intptr_t lazy__993(intptr_t* env) {
  intptr_t x_717; intptr_t x_718;
  x_718 = __str__("nil");
  x_717 = __print__(x_718);
  return x_717;
}

intptr_t lazy__989(intptr_t* env) {
  intptr_t string_of_int_282; intptr_t print_listU_695; intptr_t hd_702;
  intptr_t tl_703; intptr_t __705; intptr_t x_706; intptr_t x_707;
  intptr_t __708; intptr_t x_709; intptr_t x_710; intptr_t x_711;
  intptr_t x_712;
  string_of_int_282 = env[0];
  print_listU_695 = env[1];
  hd_702 = env[2];
  tl_703 = env[3];
  x_707 = fn0_string_of_int_883(hd_702);
  x_706 = __print__(x_707);
  __705 = x_706;
  x_710 = __str__(" :: ");
  x_709 = __print__(x_710);
  __708 = x_709;
  x_712 = fn0_print_listU_986(tl_703);
  x_711 = force(x_712);
  ffree(x_712);
  return x_711;
}

intptr_t lazy__988(intptr_t* env) {
  intptr_t x_699; intptr_t x_700;
  x_700 = __str__("nil");
  x_699 = __print__(x_700);
  return x_699;
}

intptr_t lazy__970(intptr_t* env) {
  intptr_t rwlUU_7; intptr_t cfree_454; intptr_t creduce_476;
  intptr_t mergeU_536; intptr_t ct_642; intptr_t _646; intptr_t x_647;
  intptr_t x_648; intptr_t x_649; intptr_t x_652; intptr_t x_657;
  intptr_t m_658; intptr_t n_659; intptr_t result_660; intptr_t x_661;
  intptr_t __662; intptr_t x_663; intptr_t x_664;
  rwlUU_7 = env[0];
  cfree_454 = env[1];
  creduce_476 = env[2];
  mergeU_536 = env[3];
  ct_642 = env[4];
  x_649 = mkclo(fn1_lam_971, 0, 1);
  x_652 = mkclo(fn1_lam_972, 1, 2);
  setclo(x_652, mergeU_536, 1);
  x_648 = fn0_creduce_942(nothing, nothing, nothing, x_649, x_652, ct_642);
  x_647 = force(x_648);
  ffree(x_648);
  _646 = x_647;
  m_658 = getbox(_646, 0);
  n_659 = getbox(_646, 1);
  x_661 = fn0_rwlUU_745(nothing, nothing, nothing, nothing, nothing, m_658);
  result_660 = x_661;
  x_664 = fn0_cfree_934(nothing, nothing, n_659);
  x_663 = force(x_664);
  ffree(x_664);
  __662 = x_663;
  x_657 = result_660;
  ffree(_646);
  return x_657;
}

intptr_t fn1_lam_971(intptr_t* env) {
  intptr_t lam_650; intptr_t x_651;
  lam_650 = env[0];
  x_651 = env[1];
  return x_651;
}

intptr_t fn1_lam_972(intptr_t* env) {
  intptr_t mergeU_536; intptr_t lam_653; intptr_t l_654; intptr_t r_655;
  intptr_t x_656;
  lam_653 = env[0];
  mergeU_536 = env[1];
  l_654 = env[2];
  r_655 = env[3];
  x_656 = fn0_mergeU_953(l_654, r_655);
  return x_656;
}

intptr_t lazy__944(intptr_t* env) {
  intptr_t f_480; intptr_t g_481; intptr_t ct_482; intptr_t c_484;
  intptr_t x_485; intptr_t c_486; intptr_t x_487; intptr_t x_488;
  intptr_t _489; intptr_t x_490; intptr_t x_491; intptr_t m_492;
  intptr_t n_493; intptr_t x_494; intptr_t x_495;
  f_480 = env[0];
  g_481 = env[1];
  ct_482 = env[2];
  x_485 = force(ct_482);
  ffree(ct_482);
  c_484 = x_485;
  x_488 = mkbox(19, 2); //Reduce_19
  setbox(x_488, f_480, 0);
  setbox(x_488, g_481, 1);
  x_487 = __send__(c_484, x_488);
  c_486 = x_487;
  x_490 = __recv0__(c_486);
  _489 = x_490;
  m_492 = getbox(_489, 0);
  n_493 = getbox(_489, 1);
  x_494 = lazy(lazy__945, 1);
  setlazy(x_494, n_493, 0);
  x_495 = rebox(_489, 50); //ex1UL_50
  setbox(x_495, m_492, 0);
  setbox(x_495, x_494, 1);
  x_491 = x_495;
  return x_491;
}

intptr_t lazy__945(intptr_t* env) {
  intptr_t n_493;
  n_493 = env[0];
  return n_493;
}

intptr_t lazy__940(intptr_t* env) {
  intptr_t f_468; intptr_t ct_469; intptr_t c_471; intptr_t x_472;
  intptr_t c_473; intptr_t x_474; intptr_t x_475;
  f_468 = env[0];
  ct_469 = env[1];
  x_472 = force(ct_469);
  ffree(ct_469);
  c_471 = x_472;
  x_475 = mkbox(18, 1); //Map_18
  setbox(x_475, f_468, 0);
  x_474 = __send__(c_471, x_475);
  c_473 = x_474;
  return c_473;
}

intptr_t lazy__936(intptr_t* env) {
  intptr_t ct_457; intptr_t c_459; intptr_t x_460; intptr_t c_461;
  intptr_t x_462; intptr_t x_463;
  ct_457 = env[0];
  x_460 = force(ct_457);
  ffree(ct_457);
  c_459 = x_460;
  x_462 = __send__(c_459, 17);
  c_461 = x_462;
  x_463 = __close1__(c_461);
  return x_463;
}

intptr_t lazy__928(intptr_t* env) {
  intptr_t node_worker_362; intptr_t __431; intptr_t __432;
  intptr_t l_ch_434; intptr_t x_435; intptr_t r_ch_436; intptr_t x_437;
  intptr_t x_438; intptr_t x_439;
  node_worker_362 = env[0];
  __431 = env[1];
  __432 = env[2];
  x_435 = force(__431);
  ffree(__431);
  l_ch_434 = x_435;
  x_437 = force(__432);
  ffree(__432);
  r_ch_436 = x_437;
  x_439 = mkclo(fn1_lam_929, 3, 1);
  setclo(x_439, node_worker_362, 1);
  setclo(x_439, l_ch_434, 2);
  setclo(x_439, r_ch_436, 3);
  x_438 = __fork__(x_439);
  return x_438;
}

intptr_t fn1_lam_929(intptr_t* env) {
  intptr_t node_worker_362; intptr_t l_ch_434; intptr_t r_ch_436;
  intptr_t lam_440; intptr_t _441; intptr_t x_442;
  lam_440 = env[0];
  node_worker_362 = env[1];
  l_ch_434 = env[2];
  r_ch_436 = env[3];
  _441 = env[4];
  x_442 = fn0_node_worker_914(nothing, nothing, nothing, l_ch_434, r_ch_436, _441);
  return x_442;
}

intptr_t lazy__923(intptr_t* env) {
  intptr_t leaf_worker_338; intptr_t x_420; intptr_t x_422; intptr_t x_423;
  leaf_worker_338 = env[0];
  x_420 = env[1];
  x_423 = mkclo(fn1_lam_924, 2, 1);
  setclo(x_423, leaf_worker_338, 1);
  setclo(x_423, x_420, 2);
  x_422 = __fork__(x_423);
  return x_422;
}

intptr_t fn1_lam_924(intptr_t* env) {
  intptr_t leaf_worker_338; intptr_t x_420; intptr_t lam_424; intptr_t _425;
  intptr_t x_426;
  lam_424 = env[0];
  leaf_worker_338 = env[1];
  x_420 = env[2];
  _425 = env[3];
  x_426 = fn0_leaf_worker_906(nothing, x_420, _425);
  return x_426;
}

intptr_t lazy__916(intptr_t* env) {
  intptr_t node_worker_362; intptr_t __366; intptr_t __367; intptr_t __368;
  intptr_t _370; intptr_t x_371; intptr_t x_372; intptr_t m_373;
  intptr_t n_374; intptr_t x_375; intptr_t l_ch_376; intptr_t x_377;
  intptr_t r_ch_378; intptr_t x_379; intptr_t __380; intptr_t x_381;
  intptr_t __382; intptr_t x_383; intptr_t x_384; intptr_t x_385;
  intptr_t f_386; intptr_t l_ch_387; intptr_t x_388; intptr_t x_389;
  intptr_t r_ch_390; intptr_t x_391; intptr_t x_392; intptr_t x_393;
  intptr_t x_394; intptr_t f_395; intptr_t g_396; intptr_t l_ch_397;
  intptr_t x_398; intptr_t x_399; intptr_t r_ch_400; intptr_t x_401;
  intptr_t x_402; intptr_t _403; intptr_t x_404; intptr_t x_405;
  intptr_t m_406; intptr_t n_407; intptr_t _408; intptr_t x_409;
  intptr_t x_410; intptr_t m_411; intptr_t n_412; intptr_t c_413;
  intptr_t x_414; intptr_t x_415; intptr_t x_416; intptr_t x_417;
  intptr_t x_917; intptr_t x_918;
  node_worker_362 = env[0];
  __366 = env[1];
  __367 = env[2];
  __368 = env[3];
  x_371 = __recv1__(__368);
  _370 = x_371;
  m_373 = getbox(_370, 0);
  n_374 = getbox(_370, 1);
  switch(m_373){
    case 17: //Free_17
      x_377 = __send__(__366, 17);
      l_ch_376 = x_377;
      x_379 = __send__(__367, 17);
      r_ch_378 = x_379;
      x_381 = __close1__(l_ch_376);
      __380 = x_381;
      x_383 = __close1__(r_ch_378);
      __382 = x_383;
      x_384 = __close0__(n_374);
      x_375 = x_384;
      break;
    default:
      switch(ctagof(m_373)){
        case 18: //Map_18
          f_386 = getbox(m_373, 0);
          x_389 = rebox(m_373, 18); //Map_18
          setbox(x_389, f_386, 0);
          x_388 = __send__(__366, x_389);
          l_ch_387 = x_388;
          x_392 = mkbox(18, 1); //Map_18
          setbox(x_392, f_386, 0);
          x_391 = __send__(__367, x_392);
          r_ch_390 = x_391;
          x_394 = fn0_node_worker_914(nothing, nothing, nothing, l_ch_387, r_ch_390, n_374);
          x_393 = force(x_394);
          ffree(x_394);
          x_385 = x_393;
          break;
        case 19: //Reduce_19
          f_395 = getbox(m_373, 0);
          g_396 = getbox(m_373, 1);
          x_399 = rebox(m_373, 19); //Reduce_19
          setbox(x_399, f_395, 0);
          setbox(x_399, g_396, 1);
          x_398 = __send__(__366, x_399);
          l_ch_397 = x_398;
          x_402 = mkbox(19, 2); //Reduce_19
          setbox(x_402, f_395, 0);
          setbox(x_402, g_396, 1);
          x_401 = __send__(__367, x_402);
          r_ch_400 = x_401;
          x_404 = __recv0__(l_ch_397);
          _403 = x_404;
          m_406 = getbox(_403, 0);
          n_407 = getbox(_403, 1);
          x_409 = __recv0__(r_ch_400);
          _408 = x_409;
          m_411 = getbox(_408, 0);
          n_412 = getbox(_408, 1);
          x_917 = appc(g_396, m_406);
          x_918 = appc(x_917, m_411);
          x_415 = x_918;
          x_414 = __send__(n_374, x_415);
          c_413 = x_414;
          x_417 = fn0_node_worker_914(nothing, nothing, nothing, n_407, n_412, c_413);
          x_416 = force(x_417);
          ffree(x_417);
          x_410 = x_416;
          ffree(_408);
          x_405 = x_410;
          ffree(_403);
          x_385 = x_405;
          break;
      }
      x_375 = x_385;
      break;
  }
  x_372 = x_375;
  ffree(_370);
  return x_372;
}

intptr_t lazy__908(intptr_t* env) {
  intptr_t leaf_worker_338; intptr_t x_340; intptr_t c_341; intptr_t _343;
  intptr_t x_344; intptr_t x_345; intptr_t m_346; intptr_t n_347;
  intptr_t x_348; intptr_t x_349; intptr_t x_350; intptr_t f_351;
  intptr_t x_352; intptr_t x_353; intptr_t x_354; intptr_t f_355;
  intptr_t c_357; intptr_t x_358; intptr_t x_359; intptr_t x_360;
  intptr_t x_361; intptr_t x_909; intptr_t x_911;
  leaf_worker_338 = env[0];
  x_340 = env[1];
  c_341 = env[2];
  x_344 = __recv1__(c_341);
  _343 = x_344;
  m_346 = getbox(_343, 0);
  n_347 = getbox(_343, 1);
  switch(m_346){
    case 17: //Free_17
      x_349 = __close0__(n_347);
      x_348 = x_349;
      break;
    default:
      switch(ctagof(m_346)){
        case 18: //Map_18
          f_351 = getbox(m_346, 0);
          x_909 = appc(f_351, x_340);
          x_354 = x_909;
          x_353 = fn0_leaf_worker_906(nothing, x_354, n_347);
          x_352 = force(x_353);
          ffree(x_353);
          x_350 = x_352;
          ffree(m_346);
          break;
        case 19: //Reduce_19
          f_355 = getbox(m_346, 0);
          x_911 = appc(f_355, x_340);
          x_359 = x_911;
          x_358 = __send__(n_347, x_359);
          c_357 = x_358;
          x_361 = fn0_leaf_worker_906(nothing, x_340, c_357);
          x_360 = force(x_361);
          ffree(x_361);
          x_350 = x_360;
          ffree(m_346);
          break;
      }
      x_348 = x_350;
      break;
  }
  x_345 = x_348;
  ffree(_343);
  return x_345;
}

intptr_t fn1_aux_885(intptr_t* env) {
  intptr_t ord_269; intptr_t chr_272; intptr_t str_275; intptr_t aux_286;
  intptr_t i_287; intptr_t x_288; intptr_t x_289; intptr_t r_290;
  intptr_t x_291; intptr_t i_292; intptr_t x_293; intptr_t x_294;
  intptr_t x_295; intptr_t x_296; intptr_t x_297; intptr_t x_298;
  intptr_t x_299; intptr_t x_300; intptr_t x_301; intptr_t x_302;
  intptr_t x_886;
  aux_286 = env[0];
  ord_269 = env[1];
  chr_272 = env[2];
  str_275 = env[3];
  i_287 = env[4];
  x_289 = __lte__(10, i_287);
  switch(x_289){
    case 4: //true_4
      x_291 = __mod__(i_287, 10);
      r_290 = x_291;
      x_293 = __div__(i_287, 10);
      i_292 = x_293;
      x_886 = appc(aux_286, i_292);
      x_295 = x_886;
      x_298 = fn0_ord_871('0');
      x_297 = __add__(r_290, x_298);
      x_296 = fn0_chr_874(x_297);
      x_294 = __push__(x_295, x_296);
      x_288 = x_294;
      break;
    case 5: //false_5
      x_302 = fn0_ord_871('0');
      x_301 = __add__(i_287, x_302);
      x_300 = fn0_chr_874(x_301);
      x_299 = fn0_str_877(x_300);
      x_288 = x_299;
      break;
  }
  return x_288;
}

intptr_t fn1_loop_863(intptr_t* env) {
  intptr_t x_254; intptr_t m_256; intptr_t loop_259; intptr_t acc_260;
  intptr_t y_261; intptr_t x_262; intptr_t x_263; intptr_t x_264;
  intptr_t x_265; intptr_t x_266; intptr_t x_267; intptr_t x_864;
  intptr_t x_865;
  loop_259 = env[0];
  x_254 = env[1];
  m_256 = env[2];
  acc_260 = env[3];
  y_261 = env[4];
  x_263 = __lte__(y_261, 0);
  switch(x_263){
    case 4: //true_4
      x_262 = acc_260;
      break;
    case 5: //false_5
      x_266 = __mul__(x_254, acc_260);
      x_265 = __mod__(x_266, m_256);
      x_267 = __sub__(y_261, 1);
      x_864 = appc(loop_259, x_265);
      x_865 = appc(x_864, x_267);
      x_264 = x_865;
      x_262 = x_264;
      break;
  }
  return x_262;
}

intptr_t fn1_loop_853(intptr_t* env) {
  intptr_t x_240; intptr_t loop_244; intptr_t acc_245; intptr_t y_246;
  intptr_t x_247; intptr_t x_248; intptr_t x_249; intptr_t x_250;
  intptr_t x_251; intptr_t x_854; intptr_t x_855;
  loop_244 = env[0];
  x_240 = env[1];
  acc_245 = env[2];
  y_246 = env[3];
  x_248 = __lte__(y_246, 0);
  switch(x_248){
    case 4: //true_4
      x_247 = acc_245;
      break;
    case 5: //false_5
      x_250 = __mul__(x_240, acc_245);
      x_251 = __sub__(y_246, 1);
      x_854 = appc(loop_244, x_250);
      x_855 = appc(x_854, x_251);
      x_249 = x_855;
      x_247 = x_249;
      break;
  }
  return x_247;
}

intptr_t fn1_loop_816(intptr_t* env) {
  intptr_t pred_118; intptr_t sub_131; intptr_t loop_154; intptr_t x_155;
  intptr_t y_156; intptr_t x_157; intptr_t x_158; intptr_t x_159;
  intptr_t x_160; intptr_t x_161; intptr_t x_162; intptr_t n_163;
  intptr_t x_164; intptr_t x_165; intptr_t x_817; intptr_t x_818;
  loop_154 = env[0];
  pred_118 = env[1];
  sub_131 = env[2];
  x_155 = env[3];
  y_156 = env[4];
  x_159 = fn0_pred_802(y_156);
  x_158 = fn0_sub_808(x_155, x_159);
  switch(x_158){
    case 6: //zero_6
      x_157 = 6;
      break;
    default:
      x_162 = fn0_pred_802(y_156);
      x_161 = fn0_sub_808(x_155, x_162);
      n_163 = getbox(x_161, 0);
      x_817 = appc(loop_154, n_163);
      x_818 = appc(x_817, y_156);
      x_164 = x_818;
      x_165 = mkbox(7, 1); //succ_7
      setbox(x_165, x_164, 0);
      x_160 = x_165;
      x_157 = x_160;
      break;
  }
  return x_157;
}

int main() {
  begin_run();
  intptr_t test_731; intptr_t x_732; intptr_t x_733; intptr_t x_996;
  idU_1 = mkclo(fn1_idU_740, 0, 2);
  idL_4 = mkclo(fn1_idL_743, 0, 2);
  rwlUU_7 = mkclo(fn1_rwlUU_746, 0, 6);
  rwlUL_14 = mkclo(fn1_rwlUL_749, 0, 6);
  rwlLU_21 = mkclo(fn1_rwlLU_752, 0, 6);
  rwlLL_28 = mkclo(fn1_rwlLL_755, 0, 6);
  rwrUU_35 = mkclo(fn1_rwrUU_758, 0, 6);
  rwrUL_42 = mkclo(fn1_rwrUL_761, 0, 6);
  rwrLU_49 = mkclo(fn1_rwrLU_764, 0, 6);
  rwrLL_56 = mkclo(fn1_rwrLL_767, 0, 6);
  sing_elimUU_63 = mkclo(fn1_sing_elimUU_770, 0, 3);
  sing_elimUL_67 = mkclo(fn1_sing_elimUL_773, 0, 3);
  sing_elimLU_71 = mkclo(fn1_sing_elimLU_776, 0, 3);
  sing_elimLL_75 = mkclo(fn1_sing_elimLL_779, 0, 3);
  not_79 = mkclo(fn1_not_782, 0, 1);
  and_82 = mkclo(fn1_and_785, 0, 2);
  or_87 = mkclo(fn1_or_788, 0, 2);
  xor_92 = mkclo(fn1_xor_791, 0, 2);
  string_of_bool_98 = mkclo(fn1_string_of_bool_794, 0, 1);
  lte_103 = mkclo(fn1_lte_797, 0, 2);
  lt_113 = mkclo(fn1_lt_800, 0, 2);
  pred_118 = mkclo(fn1_pred_803, 0, 1);
  add_123 = mkclo(fn1_add_806, 0, 2);
  sub_131 = mkclo(fn1_sub_809, 0, 2);
  mul_139 = mkclo(fn1_mul_812, 0, 2);
  div_147 = mkclo(fn1_div_815, 0, 2);
  rem_167 = mkclo(fn1_rem_825, 0, 2);
  rconsUU_173 = mkclo(fn1_rconsUU_828, 0, 3);
  rconsUL_184 = mkclo(fn1_rconsUL_831, 0, 3);
  rconsLL_195 = mkclo(fn1_rconsLL_834, 0, 3);
  free_listUU_206 = mkclo(fn1_free_listUU_837, 0, 3);
  free_listUL_217 = mkclo(fn1_free_listUL_842, 0, 3);
  free_listLL_228 = mkclo(fn1_free_listLL_847, 0, 3);
  pow_239 = mkclo(fn1_pow_852, 0, 2);
  powm_253 = mkclo(fn1_powm_862, 0, 3);
  ord_269 = mkclo(fn1_ord_872, 0, 1);
  chr_272 = mkclo(fn1_chr_875, 0, 1);
  str_275 = mkclo(fn1_str_878, 0, 1);
  strlen_279 = mkclo(fn1_strlen_881, 0, 1);
  string_of_int_282 = mkclo(fn1_string_of_int_884, 0, 1);
  map_310 = mkclo(fn1_map_894, 0, 4);
  reduce_324 = mkclo(fn1_reduce_899, 0, 5);
  leaf_worker_338 = mkclo(fn1_leaf_worker_907, 0, 3);
  node_worker_362 = mkclo(fn1_node_worker_915, 0, 6);
  cleaf_418 = mkclo(fn1_cleaf_922, 0, 2);
  cnode_427 = mkclo(fn1_cnode_927, 0, 5);
  ctree_of_tree_443 = mkclo(fn1_ctree_of_tree_932, 0, 2);
  cfree_454 = mkclo(fn1_cfree_935, 0, 3);
  cmap_464 = mkclo(fn1_cmap_939, 0, 5);
  creduce_476 = mkclo(fn1_creduce_943, 0, 6);
  splitU_496 = mkclo(fn1_splitU_948, 0, 1);
  splitL_516 = mkclo(fn1_splitL_951, 0, 1);
  mergeU_536 = mkclo(fn1_mergeU_954, 0, 2);
  mergeL_556 = mkclo(fn1_mergeL_957, 0, 2);
  msortU_576 = mkclo(fn1_msortU_960, 0, 1);
  msortL_596 = mkclo(fn1_msortL_963, 0, 1);
  splitting_tree_616 = mkclo(fn1_splitting_tree_966, 0, 1);
  cmsort_640 = mkclo(fn1_cmsort_969, 0, 1);
  mklistU_665 = mkclo(fn1_mklistU_975, 0, 1);
  mklistL_672 = mkclo(fn1_mklistL_978, 0, 1);
  list_lenU_679 = mkclo(fn1_list_lenU_981, 0, 1);
  list_lenL_687 = mkclo(fn1_list_lenL_984, 0, 1);
  print_listU_695 = mkclo(fn1_print_listU_987, 0, 1);
  print_listL_713 = mkclo(fn1_print_listL_992, 0, 1);
  x_732 = fn0_mklistU_974(100);
  test_731 = x_732;
  x_733 = lazy(lazy__997, 3);
  setlazy(x_733, cmsort_640, 0);
  setlazy(x_733, print_listU_695, 1);
  setlazy(x_733, test_731, 2);
  x_996 = force(x_733);
  end_run();
}

