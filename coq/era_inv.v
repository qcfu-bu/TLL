From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_lam0_form Γ Δ m n X B s :
  Γ ; Δ ⊢ m ~ Lam0 X n s : B -> exists A n, m = Lam0 A n s.
Proof.
  move e:(Lam0 X n s)=>x er. elim: er X n s e=>//{Γ Δ m x B}.
  move=>Γ Δ A B m m' s k tym ih X n s0[e1 e2 e3]; subst.
  exists A. by exists m.
Qed.

Lemma era_lam1_form Γ Δ m n X B s :
  Γ ; Δ ⊢ m ~ Lam1 X n s : B -> exists A n, m = Lam1 A n s.
Proof.
  move e:(Lam1 X n s)=>x er. elim: er X n s e=>//{Γ Δ m x B}.
  move=>Γ Δ A B m m' s t k tym ih X n s0[e1 e2 e3]; subst.
  exists A. by exists m.
Qed.

Lemma era_box_form Γ Δ m A : ~Γ ; Δ ⊢ m ~ Box : A.
Proof. move e:(Box)=>m' ty. elim: ty e=>//{Γ Δ m m' A}. Qed.

Lemma era_lam0_invX Γ Δ A1 A2 A3 B C m1 m2 s1 s2 t :
  Γ ; Δ ⊢ Lam0 A1 m1 s1 ~ Lam0 A2 m2 s1 : C ->
  C === Pi0 A3 B s2 ->
  (A3 :: Γ) ⊢ B : Sort t ->
  (A3 :: Γ) ; _: Δ ⊢ m1 ~ m2 : B.
Proof with eauto.
  move e1:(Lam0 A1 m1 s1)=>n1.
  move e2:(Lam0 A2 m2 s1)=>n2 tyL.
  elim: tyL A1 A2 A3 B m1 m2 s1 s2 t e1 e2=>//{Γ Δ C n1 n2}.
  { move=>Γ Δ A B m m' s k tym ihm A1 A2 A3 B0 m1 m2
      s1 s2 t[e1 e2 e3][e5 e6 _]; subst.
    move=>/pi0_inj[eq1[eq2 e]]tyB0; subst.
    have wf:=sta_type_wf tyB0. inv wf.
    apply: era_conv...
    apply: era_ctx_conv0.
    exact: (conv_sym eq1).
    exact: H2.
    exact: tym. }
  { move=>Γ Δ A B m m' s eq1 tym ihm tyB A1 A2 A3 B0 m1 m2
      s1 s2 t e1 e2 eq tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma era_lam1_invX Γ Δ A1 A2 A3 B C m1 m2 s1 s2 t :
  Γ ; Δ ⊢ Lam1 A1 m1 s1 ~ Lam1 A2 m2 s1 : C ->
  C === Pi1 A3 B s2 ->
  (A3 :: Γ) ⊢ B : Sort t ->
  exists r, (A3 :: Γ) ; A3 :{r} Δ ⊢ m1 ~ m2 : B.
Proof with eauto.
  move e1:(Lam1 A1 m1 s1)=>n1.
  move e2:(Lam1 A2 m2 s1)=>n2 tyL.
  elim: tyL A1 A2 A3 B m1 m2 s1 s2 t e1 e2=>//{Γ Δ C n1 n2}.
  { move=>Γ Δ A B m m' s t k tym ihm A1 A2 A3 B0 m1 m2
      s1 s2 t0[e1 e2 e3][e5 e6 _]; subst.
    move=>/pi1_inj[eq1[eq2 e]]tyB0; subst.
    have wf:=dyn_type_wf (era_dyn_type tym). inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    have[A0 rd1 rd2]:=church_rosser eq1.
    have tyA0t:=sta_rd H4 rd1.
    have tyA0s:=sta_rd H3 rd2.
    have/sort_inj e:=sta_uniq tyA0t tyA0s. subst.
    exists s.
    apply: era_ctx_conv1.
    apply: conv_sym...
    exact: H3.
    apply: era_conv...
    apply: sta_ctx_conv... }
  { move=>Γ Δ A B m m' s eq1 tym ihm tyB A1 A2 A3 B0 m1 m2
      s1 s2 t e1 e2 eq tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma era_lam0_inv Γ Δ m m' A1 A2 A3 B s1 s2 :
  Γ ; Δ ⊢ Lam0 A2 m s2 ~ Lam0 A3 m' s2 : Pi0 A1 B s1 ->
  (A1 :: Γ) ; _: Δ ⊢ m ~ m' : B.
Proof with eauto.
  move=>ty.
  have[t/sta_pi0_inv[r[tyB _]]]:=dyn_valid (era_dyn_type ty).
  apply: era_lam0_invX...
Qed.

Lemma era_lam1_inv Γ Δ m m' A1 A2 A3 B s1 s2 :
  Γ ; Δ ⊢ Lam1 A2 m s2 ~ Lam1 A3 m' s2 : Pi1 A1 B s1 ->
  exists r, (A1 :: Γ) ; A1 :{r} Δ ⊢ m ~ m' : B.
Proof with eauto.
  move=>ty.
  have[t/sta_pi1_inv[r[tyB _]]]:=dyn_valid (era_dyn_type ty).
  apply: era_lam1_invX...
Qed.
