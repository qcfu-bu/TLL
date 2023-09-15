#ifndef MAIN_H
#define MAIN_H

#include "runtime.h"

intptr_t fn0_idU_291(intptr_t A_2, intptr_t m_3);
intptr_t fn1_idU_292(intptr_t* env);
intptr_t fn0_idL_294(intptr_t A_5, intptr_t m_6);
intptr_t fn1_idL_295(intptr_t* env);
intptr_t fn0_rwlUU_297(intptr_t A_8, intptr_t m_9, intptr_t n_10, intptr_t B_11, intptr_t __12, intptr_t __13);
intptr_t fn1_rwlUU_298(intptr_t* env);
intptr_t fn0_rwlUL_300(intptr_t A_15, intptr_t m_16, intptr_t n_17, intptr_t B_18, intptr_t __19, intptr_t __20);
intptr_t fn1_rwlUL_301(intptr_t* env);
intptr_t fn0_rwlLU_303(intptr_t A_22, intptr_t m_23, intptr_t n_24, intptr_t B_25, intptr_t __26, intptr_t __27);
intptr_t fn1_rwlLU_304(intptr_t* env);
intptr_t fn0_rwlLL_306(intptr_t A_29, intptr_t m_30, intptr_t n_31, intptr_t B_32, intptr_t __33, intptr_t __34);
intptr_t fn1_rwlLL_307(intptr_t* env);
intptr_t fn0_rwrUU_309(intptr_t A_36, intptr_t m_37, intptr_t n_38, intptr_t B_39, intptr_t __40, intptr_t __41);
intptr_t fn1_rwrUU_310(intptr_t* env);
intptr_t fn0_rwrUL_312(intptr_t A_43, intptr_t m_44, intptr_t n_45, intptr_t B_46, intptr_t __47, intptr_t __48);
intptr_t fn1_rwrUL_313(intptr_t* env);
intptr_t fn0_rwrLU_315(intptr_t A_50, intptr_t m_51, intptr_t n_52, intptr_t B_53, intptr_t __54, intptr_t __55);
intptr_t fn1_rwrLU_316(intptr_t* env);
intptr_t fn0_rwrLL_318(intptr_t A_57, intptr_t m_58, intptr_t n_59, intptr_t B_60, intptr_t __61, intptr_t __62);
intptr_t fn1_rwrLL_319(intptr_t* env);
intptr_t fn0_sing_elimUU_321(intptr_t A_64, intptr_t x_65, intptr_t __66);
intptr_t fn1_sing_elimUU_322(intptr_t* env);
intptr_t fn0_sing_elimUL_324(intptr_t A_68, intptr_t x_69, intptr_t __70);
intptr_t fn1_sing_elimUL_325(intptr_t* env);
intptr_t fn0_sing_elimLU_327(intptr_t A_72, intptr_t x_73, intptr_t __74);
intptr_t fn1_sing_elimLU_328(intptr_t* env);
intptr_t fn0_sing_elimLL_330(intptr_t A_76, intptr_t x_77, intptr_t __78);
intptr_t fn1_sing_elimLL_331(intptr_t* env);
intptr_t fn0_not_333(intptr_t __80);
intptr_t fn1_not_334(intptr_t* env);
intptr_t fn0_and_336(intptr_t __83, intptr_t __84);
intptr_t fn1_and_337(intptr_t* env);
intptr_t fn0_or_339(intptr_t __88, intptr_t __89);
intptr_t fn1_or_340(intptr_t* env);
intptr_t fn0_xor_342(intptr_t __93, intptr_t __94);
intptr_t fn1_xor_343(intptr_t* env);
intptr_t fn0_lte_345(intptr_t __99, intptr_t __100);
intptr_t fn1_lte_346(intptr_t* env);
intptr_t fn0_lt_348(intptr_t x_107, intptr_t y_108);
intptr_t fn1_lt_349(intptr_t* env);
intptr_t fn0_pred_351(intptr_t __112);
intptr_t fn1_pred_352(intptr_t* env);
intptr_t fn0_add_354(intptr_t __117, intptr_t __118);
intptr_t fn1_add_355(intptr_t* env);
intptr_t fn0_sub_357(intptr_t __124, intptr_t __125);
intptr_t fn1_sub_358(intptr_t* env);
intptr_t fn0_mul_360(intptr_t __131, intptr_t __132);
intptr_t fn1_mul_361(intptr_t* env);
intptr_t fn0_div_363(intptr_t x_139, intptr_t y_140);
intptr_t fn1_div_364(intptr_t* env);
intptr_t fn0_rem_373(intptr_t x_158, intptr_t y_159);
intptr_t fn1_rem_374(intptr_t* env);
intptr_t fn0_free_listUU_376(intptr_t A_164, intptr_t f_165, intptr_t __166);
intptr_t fn1_free_listUU_377(intptr_t* env);
intptr_t fn0_free_listUL_381(intptr_t A_174, intptr_t f_175, intptr_t __176);
intptr_t fn1_free_listUL_382(intptr_t* env);
intptr_t fn0_free_listLL_386(intptr_t A_184, intptr_t f_185, intptr_t __186);
intptr_t fn1_free_listLL_387(intptr_t* env);
intptr_t fn0_pow_391(intptr_t x_194, intptr_t y_195);
intptr_t fn1_pow_392(intptr_t* env);
intptr_t fn0_powm_401(intptr_t x_208, intptr_t y_209, intptr_t m_210);
intptr_t fn1_powm_402(intptr_t* env);
intptr_t fn0_ord_411(intptr_t c_224);
intptr_t fn1_ord_412(intptr_t* env);
intptr_t fn0_chr_414(intptr_t i_227);
intptr_t fn1_chr_415(intptr_t* env);
intptr_t fn0_str_417(intptr_t c_230);
intptr_t fn1_str_418(intptr_t* env);
intptr_t fn0_strlen_420(intptr_t s_234);
intptr_t fn1_strlen_421(intptr_t* env);
intptr_t fn0_string_of_int_423(intptr_t i_237);
intptr_t fn1_string_of_int_424(intptr_t* env);
intptr_t fn0_appendUU_433(intptr_t A_265, intptr_t __266, intptr_t __267);
intptr_t fn1_appendUU_434(intptr_t* env);
intptr_t fn0_appendUL_436(intptr_t A_274, intptr_t __275, intptr_t __276);
intptr_t fn1_appendUL_437(intptr_t* env);
intptr_t fn0_appendLL_439(intptr_t A_283, intptr_t __284, intptr_t __285);
intptr_t fn1_appendLL_440(intptr_t* env);
intptr_t fn1_aux_425(intptr_t* env);
intptr_t fn1_loop_403(intptr_t* env);
intptr_t fn1_loop_393(intptr_t* env);
intptr_t fn1_loop_365(intptr_t* env);

#endif

