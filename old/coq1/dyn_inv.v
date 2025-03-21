From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_uniq sta_sr dyn_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_lam0_invX Γ Δ A1 A2 B C m s1 s2 t :
  Γ ; Δ ⊢ Lam0 A1 m s1 : C ->
  C === Pi0 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t ->
  (A2 :: Γ) ; _: Δ ⊢ m : B.
Proof with eauto.
  move e:(Lam0 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t e=>//{Γ Δ C n}.
  { move=>Γ Δ A B m s k tym _ A1 A2 B0 m0
      s1 s2 t[e1 e2 e3]/pi0_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=dyn_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    apply: dyn_ctx_conv0.
    apply: conv_sym...
    exact: H4.
    apply: dyn_conv...
    apply: sta_ctx_conv... }
  { move=>Γ Δ A B m s eq tym ihm tyB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_lam1_invX Γ Δ A1 A2 B C m s1 s2 t :
  Γ ; Δ ⊢ Lam1 A1 m s1 : C ->
  C === Pi1 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t ->
  exists r, (A2 :: Γ) ; A2 :{r} Δ ⊢ m : B.
Proof with eauto.
  move e:(Lam1 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t e=>//{Γ Δ C n}.
  { move=>Γ Δ A B m s t k tym _ A1 A2 B0 m0
      s1 s2 t0[e1 e2 e3]/pi1_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=dyn_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    have[A0 rd1 rd2]:=church_rosser eq1.
    have tyA0t:=sta_rd H4 rd1.
    have tyA0s:=sta_rd H3 rd2.
    have/sort_inj e:=sta_uniq tyA0t tyA0s. subst.
    exists s.
    apply: dyn_ctx_conv1.
    apply: conv_sym...
    exact: H3.
    apply: dyn_conv...
    apply: sta_ctx_conv... }
  { move=>Γ Δ A B m s eq tym ihm tyB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_lam0_inv Γ Δ m A1 A2 B s1 s2 :
  Γ ; Δ ⊢ Lam0 A2 m s2 : Pi0 A1 B s1 -> (A1 :: Γ) ; _: Δ ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t/sta_pi0_inv[r[tyB _]]]:=dyn_valid ty.
  apply: dyn_lam0_invX...
Qed.

Lemma dyn_lam1_inv Γ Δ m A1 A2 B s1 s2 :
  Γ ; Δ ⊢ Lam1 A2 m s2 : Pi1 A1 B s1 -> exists r, (A1 :: Γ) ; A1 :{r} Δ ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t/sta_pi1_inv[r[tyB _]]]:=dyn_valid ty.
  apply: dyn_lam1_invX...
Qed.
