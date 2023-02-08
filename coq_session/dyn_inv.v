From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_uniq sta_sr dyn_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_lam0_invX Θ Γ Δ A1 A2 B C m s1 s2 t :
  Θ ; Γ ; Δ ⊢ Lam0 A1 m s1 : C ->
  C === Pi0 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t ->
  Θ ; (A2 :: Γ) ; _: Δ ⊢ m : B.
Proof with eauto.
  move e:(Lam0 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t e=>//{Θ Γ Δ C n}.
  { move=>Θ Γ Δ A B m s k1 k2 tym _ A1 A2 B0 m0
           s1 s2 t[e1 e2 e3]/pi0_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=dyn_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    apply: dyn_ctx_conv0.
    apply: conv_sym...
    exact: H4.
    apply: dyn_conv...
    apply: sta_ctx_conv... }
  { move=>Θ Γ Δ A B m s eq tym ihm tyB A1 A2 B0 m0
           s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_lam1_invX Θ Γ Δ A1 A2 B C m s1 s2 t :
  Θ ; Γ ; Δ ⊢ Lam1 A1 m s1 : C ->
  C === Pi1 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t ->
  exists r, Θ ; (A2 :: Γ) ; A2 :{r} Δ ⊢ m : B.
Proof with eauto.
  move e:(Lam1 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t e=>//{Θ Γ Δ C n}.
  { move=>Θ Γ Δ A B m s t k1 k2 tym _ A1 A2 B0 m0
           s1 s2 t0[e1 e2 e3]/pi1_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=dyn_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    have[A0 rd1 rd2]:=church_rosser eq1.
    have tyA0t:=sta_rd H4 rd1.
    have tyA0s:=sta_rd H3 rd2.
    have e:=sta_unicity tyA0t tyA0s. subst.
    exists s.
    apply: dyn_ctx_conv1.
    apply: conv_sym...
    exact: H3.
    apply: dyn_conv...
    apply: sta_ctx_conv... }
  { move=>Θ Γ Δ A B m s eq tym ihm tyB A1 A2 B0 m0
           s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_lam0_inv Θ Γ Δ m A1 A2 B s1 s2 :
  Θ ; Γ ; Δ ⊢ Lam0 A2 m s2 : Pi0 A1 B s1 -> Θ ; (A1 :: Γ) ; _: Δ ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t/sta_pi0_inv[r[tyB _]]]:=dyn_valid ty.
  apply: dyn_lam0_invX...
Qed.

Lemma dyn_lam1_inv Θ Γ Δ m A1 A2 B s1 s2 :
  Θ ; Γ ; Δ ⊢ Lam1 A2 m s2 : Pi1 A1 B s1 -> exists r, Θ ; (A1 :: Γ) ; A1 :{r} Δ ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t/sta_pi1_inv[r[tyB _]]]:=dyn_valid ty.
  apply: dyn_lam1_invX...
Qed.

Lemma dyn_pair0_invX Θ Γ Δ A B m n s r t C :
  Θ ; Γ ; Δ ⊢ Pair0 m n s : C ->
  C === Sig0 A B r ->
  Γ ⊢ Sig0 A B r : Sort t ->
  s = r /\ Γ ⊢ m : A /\ Θ ; Γ ; Δ ⊢ n : B.[m/].
Proof with eauto.
  move e:(Pair0 m n s)=>x ty.
  elim: ty A B m n s r t e=>//{Θ Γ Δ x C}.
  { move=>Θ Γ Δ A B m n t ty1 tym ihm tyn A0 B0 m0 n0 s r t0[e1 e2 e3]
      /sig0_inj[e4[e5 e6]]ty2; subst.
    have[s[r0[ord[tyA0[tyB0/sort_inj e]]]]]:=sta_sig0_inv ty2. subst.
    have tym0: Γ ⊢ m : A0 by apply: sta_conv; eauto.
    repeat split...
    apply: dyn_conv.
    apply: sta_conv_subst.
    all: eauto.
    apply: sta_esubst...
    by autosubst. }
  { move=>Θ Γ Δ A B m s eq tym ihm tyB A0 B0 m0 n s0 r t e eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_pair1_invX Θ Γ Δ A B m n s r t C :
  Θ ; Γ ; Δ ⊢ Pair1 m n s : C ->
  C === Sig1 A B r ->
  Γ ⊢ Sig1 A B r : Sort t ->
  exists Θ1 Θ2 Δ1 Δ2,
    s = r /\
    Θ1 ∘ Θ2 => Θ /\
    Δ1 ∘ Δ2 => Δ /\
    Θ1 ; Γ ; Δ1 ⊢ m : A /\
    Θ2 ; Γ ; Δ2 ⊢ n : B.[m/].
Proof with eauto.
  move e:(Pair1 m n s)=>x ty.
  elim: ty A B m n s r t e=>//{Θ Γ Δ x C}.
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 ty1 tym _ tyn _ A0 B0 m0 n0 s r t0
      [e1 e2 e3]/sig1_inj[e4[e5 e6]]ty2; subst.
    exists Θ1. exists Θ2. exists Δ1. exists Δ2.
    have[s[r0[ord1[ord2[tyA0[tyB0/sort_inj e]]]]]]:=sta_sig1_inv ty2. subst.
    have tym0:Θ1; Γ ; Δ1 ⊢ m : A0 by apply: dyn_conv; eauto.
    repeat split...
    apply: dyn_conv.
    apply: sta_conv_subst.
    all: eauto.
    apply: sta_esubst...
    by autosubst. }
  { move=>Θ Γ Δ A B m s eq tym ihm tyB A0 B0 m0 n s0 r t e eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_pair0_inv Θ Γ Δ A B m n s r :
  Θ ; Γ ; Δ ⊢ Pair0 m n s : Sig0 A B r ->
  s = r /\ Γ ⊢ m : A /\ Θ ; Γ ; Δ ⊢ n : B.[m/].
Proof with eauto.
  move=>ty.
  have[t tyS]:=dyn_valid ty.
  apply: dyn_pair0_invX...
Qed.

Lemma dyn_pair1_inv Θ Γ Δ A B m n s r :
  Θ ; Γ ; Δ ⊢ Pair1 m n s : Sig1 A B r ->
  exists Θ1 Θ2 Δ1 Δ2,
    s = r /\
    Θ1 ∘ Θ2 => Θ /\ 
    Δ1 ∘ Δ2 => Δ /\ 
    Θ1 ; Γ ; Δ1 ⊢ m : A /\
    Θ2 ; Γ ; Δ2 ⊢ n : B.[m/].
Proof with eauto.
  move=>ty.
  have[t tyS]:=dyn_valid ty.
  apply: dyn_pair1_invX...
Qed.

Lemma dyn_return_inv Θ Γ Δ m B :
  Θ ; Γ ; Δ ⊢ Return m : B ->
  exists A, Θ ; Γ ; Δ ⊢ m : A /\ B === IO A.
Proof with eauto.
  move e:(Return m)=>x ty.
  elim: ty m e=>//{Θ Γ Δ B x}.
  { move=>Θ Γ Δ m A tym ihm m0[e]; subst. exists A... }
  { move=>Θ Γ Δ A B m s eq1 tym ihm tyB m0 e; subst.
    have[A0[tym0 eq2]]:=ihm _ erefl.
    exists A0. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma dyn_app_inv Θ Γ Δ m n C :
  Θ ; Γ ; Δ ⊢ App m n : C ->
  exists A B s,
    (Θ ; Γ ; Δ ⊢ m : Pi0 A B s /\ Γ ⊢ n : A /\ C === B.[n/]) \/
    (exists Θ1 Θ2 Δ1 Δ2,
        Θ1 ∘ Θ2 => Θ /\
        Δ1 ∘ Δ2 => Δ /\
        Θ1 ; Γ ; Δ1 ⊢ m : Pi1 A B s /\ Θ2 ; Γ ; Δ2 ⊢ n : A /\ C === B.[n/]).
Proof with eauto.
  move e:(App m n)=>x ty.
  elim: ty m n e=>//{Θ Γ Δ x C}.
  { move=>Θ Γ Δ A B m n s tym ihm tyn m0 n0[e1 e2]; subst.
    exists A. exists B. exists s. left. split... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn m0 n0[e1 e2]; subst.
    exists A. exists B. exists s. right. exists Θ1. exists Θ2. exists Δ1. exists Δ2. split... }
  { move=>Θ Γ Δ A B m s eq1 tym ihm tyB m0 n0 e; subst.
    have [A0[B0[s0[[tym0[tyn0 eq2]]
                  |[Θ1[Θ2[Δ1[Δ2[mrg1[mrg2[tym0[tyn0 eq2]]]]]]]]]]]]:=ihm _ _ erefl.
    { exists A0. exists B0. exists s0. left. repeat split...
      apply: conv_trans.
      apply: conv_sym...
      exact: eq2. }
    { exists A0. exists B0. exists s0. right. exists Θ1. exists Θ2. exists Δ1. exists Δ2. repeat split...
      apply: conv_trans.
      apply: conv_sym...
      exact: eq2. } }
Qed.

Lemma dyn_tt_inv Θ Γ Δ A : Θ ; Γ ; Δ ⊢ TT : A -> dyn_empty Θ.
Proof with eauto. move e:(TT)=>m ty. elim: ty e=>//{Θ Γ Δ A}. Qed.

Lemma dyn_ff_inv Θ Γ Δ A : Θ ; Γ ; Δ ⊢ FF : A -> dyn_empty Θ.
Proof with eauto. move e:(FF)=>m ty. elim: ty e=>//{Θ Γ Δ A}. Qed.
  
