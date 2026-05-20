From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_var_form Γ Δ m x B :
  Γ ; Δ ⊢ m ~ Var x : B -> exists x, m = Var x.
Proof.
  move e:(Var x)=>n er. elim: er x e=>//{Γ Δ m n B}.
  move=>Γ Δ x s A wf shs dhs x0[e]; subst.
  by exists x.
Qed.

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

Lemma era_pair0_form Γ Δ m m1' m2' A s :
  Γ ; Δ ⊢ m ~ Pair0 m1' m2' s : A -> exists m1 m2, m = Pair0 m1 m2 s.
Proof.
  move e:(Pair0 m1' m2' s)=>x er. elim: er m1' m2' s e=>//{Γ Δ m x A}.
  move=>Γ Δ A B m m' n t l tyS tym ihm tyn m1' m2' s[e1 e2 e3]; subst.
  exists m. by exists n.
Qed.

Lemma era_pair1_form Γ Δ m m1' m2' A s :
  Γ ; Δ ⊢ m ~ Pair1 m1' m2' s : A -> exists m1 m2, m = Pair1 m1 m2 s.
Proof.
  move e:(Pair1 m1' m2' s)=>x er. elim: er m1' m2' s e=>//{Γ Δ m x A}.
  move=>Γ Δ1 Δ2 Δ A B m m' n n' t l mrg tyS tym ihm tyn ihn m1' m2' s[e1 e2 e3]; subst.
  exists m. by exists n.
Qed.

Lemma era_tt_form Γ Δ m A : Γ ; Δ ⊢ m ~ TT : A -> m = TT.
Proof. move e:(TT)=>x er. elim: er e=>//. Qed.

Lemma era_ff_form Γ Δ m A : Γ ; Δ ⊢ m ~ FF : A -> m = FF.
Proof. move e:(FF)=>x er. elim: er e=>//. Qed.

Lemma era_box_form Γ Δ m A : ~Γ ; Δ ⊢ m ~ Box : A.
Proof. move e:(Box)=>m' ty. elim: ty e=>//{Γ Δ m m' A}. Qed.

Lemma era_lam0_invX Γ Δ A1 A2 A3 B C m1 m2 s1 s2 t l :
  Γ ; Δ ⊢ Lam0 A1 m1 s1 ~ Lam0 A2 m2 s1 : C ->
  C ≃ Pi0 A3 B s2 ->
  (A3 :: Γ) ⊢ B : Sort t l ->
  (A3 :: Γ) ; _: Δ ⊢ m1 ~ m2 : B /\ A1 ≃ A3.
Proof with eauto.
  move e1:(Lam0 A1 m1 s1)=>n1.
  move e2:(Lam0 A2 m2 s1)=>n2 tyL.
  elim: tyL A1 A2 A3 B m1 m2 s1 s2 t l e1 e2=>//{Γ Δ C n1 n2}.
  { move=>Γ Δ A B m m' s k tym ihm A1 A2 A3 B0 m1 m2
      s1 s2 t l[e1 e2 e3][e5 e6 _]; subst.
    move=>/pi0_inj[eq1[eq2 e]]tyB0; subst.
    have wf:=sta_type_wf tyB0. inv wf. split...
    apply: era_conv...
    apply: era_ctx_conv0.
    exact: (conv_sym eq1).
    exact: H2.
    exact: tym. }
  { move=>Γ Δ A B m m' s l eq1 tym ihm tyB A1 A2 A3 B0 m1 m2
      s1 s2 t l0 e1 e2 eq tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma era_lam1_invX Γ Δ A1 A2 A3 B C m1 m2 s1 s2 t l :
  Γ ; Δ ⊢ Lam1 A1 m1 s1 ~ Lam1 A2 m2 s1 : C ->
  C ≃ Pi1 A3 B s2 ->
  (A3 :: Γ) ⊢ B : Sort t l ->
  exists r, (A3 :: Γ) ; A3 .{r} Δ ⊢ m1 ~ m2 : B /\ A1 ≃ A3.
Proof with eauto.
  move e1:(Lam1 A1 m1 s1)=>n1.
  move e2:(Lam1 A2 m2 s1)=>n2 tyL.
  elim: tyL A1 A2 A3 B m1 m2 s1 s2 t l e1 e2=>//{Γ Δ C n1 n2}.
  { move=>Γ Δ A B m m' s t k tym ihm A1 A2 A3 B0 m1 m2
      s1 s2 t0 l0[e1 e2 e3][e5 e6 _]; subst.
    move=>/pi1_inj[eq1[eq2 e]]tyB0; subst.
    have wf:=dyn_type_wf (era_dyn_type tym). inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    have[A0 rd1 rd2]:=church_rosser eq1.
    have tyA0t:=sta_rd H4 rd1.
    have tyA0s:=sta_rd H3 rd2.
    have e:=sta_unicity tyA0t tyA0s. subst.
    exists s. split...
    apply: era_ctx_conv1.
    apply: conv_sym...
    exact: H3.
    apply: era_conv...
    apply: sta_ctx_conv... }
  { move=>Γ Δ A B m m' s l eq1 tym ihm tyB A1 A2 A3 B0 m1 m2
      s1 s2 t l0 e1 e2 eq tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma era_lam0_inv Γ Δ m m' A1 A2 A3 B s1 s2 :
  Γ ; Δ ⊢ Lam0 A1 m s2 ~ Lam0 A2 m' s2 : Pi0 A3 B s1 ->
  (A3 :: Γ) ; _: Δ ⊢ m ~ m' : B /\ A1 ≃ A3.
Proof with eauto.
  move=>ty.
  have[t[l/sta_pi0_inv[r[l1[l2[tyB _]]]]]]:=dyn_valid (era_dyn_type ty).
  apply: era_lam0_invX...
Qed.

Lemma era_lam1_inv Γ Δ m m' A1 A2 A3 B s1 s2 :
  Γ ; Δ ⊢ Lam1 A1 m s2 ~ Lam1 A2 m' s2 : Pi1 A3 B s1 ->
  exists r, (A3 :: Γ) ; A3 .{r} Δ ⊢ m ~ m' : B /\ A1 ≃ A3.
Proof with eauto.
  move=>ty.
  have[t[l/sta_pi1_inv[r[l1[l2[tyB _]]]]]]:=dyn_valid (era_dyn_type ty).
  apply: era_lam1_invX...
Qed.

Lemma era_pair0_invX Γ Δ A B m m' n n' s r t l C :
  Γ ; Δ ⊢ Pair0 m n s ~ Pair0 m' n' s : C ->
  C ≃ Sig0 A B r ->
  Γ ⊢ Sig0 A B r : Sort t l ->
  s = r /\ n' = Box /\ Γ ; Δ ⊢ m ~ m' : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move e1:(Pair0 m n s)=>x.
  move e2:(Pair0 m' n' s)=>y ty.
  elim: ty A B m m' n n' s r t l e1 e2=>//{Γ Δ x y C}.
  { move=>Γ Δ A B m m' n t l ty1 tym ihm tyn A0 B0 m0 m0' n0 n'
      s r t0 l0[e1 e2 e3][e4 e5 e6]/sig0_inj[e7[e8 e9]]ty2; subst.
    have[s[r0[l1[l2[ord[tyA0[tyB0/sort_inj[e1 e2]]]]]]]]:=sta_sig0_inv ty2. subst.
    have tym0:Γ ; Δ ⊢ m ~ m' : A0 by apply: era_conv; eauto.
    repeat split...
    apply: sta_conv.
    apply: sta_conv_subst.
    all: eauto.
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ Δ A B m m' s l eq tym ihm tyB A0 B0 m0 m0' n n' s0 r t l0 e1 e2 eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma era_pair1_invX Γ Δ A B m m' n n' s r t l C :
  Γ ; Δ ⊢ Pair1 m n s ~ Pair1 m' n' s : C ->
  C ≃ Sig1 A B r ->
  Γ ⊢ Sig1 A B r : Sort t l ->
  exists Δ1 Δ2,
    Δ1 ∘ Δ2 => Δ /\ s = r /\
    Γ ; Δ1 ⊢ m ~ m' : A /\ Γ ; Δ2 ⊢ n ~ n' : B.[m/].
Proof with eauto.
  move e1:(Pair1 m n s)=>x.
  move e2:(Pair1 m' n' s)=>y ty.
  elim: ty A B m m' n n' s r t l e1 e2=>//{Γ Δ x y C}.
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t l mrg ty1 tym ihm tyn ihn A0 B0
      m0 m0' n0 n0' s r t0 l0[e1 e2 e3][e4 e5 e6]/sig1_inj[e7[e8 e9]]ty2; subst.
    exists Δ1. exists Δ2.
    have[s[r0[l1[l2[ord1[ord2[tyA0[tyB0/sort_inj[e1 e2]]]]]]]]]:=sta_sig1_inv ty2. subst.
    have tym0:Γ ; Δ1 ⊢ m ~ m' : A0 by apply: era_conv; eauto.
    repeat split...
    apply: era_conv.
    apply: sta_conv_subst.
    all: eauto.
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ Δ A B m m' s l eq tym ihm tyB A0 B0 m0 m0' n n' s0 r t l0 e1 e2 eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma era_pair0_inv Γ Δ A B m m' n n' s r :
  Γ ; Δ ⊢ Pair0 m n s ~ Pair0 m' n' s : Sig0 A B r ->
  s = r /\ n' = Box /\ Γ ; Δ ⊢ m ~ m' : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move=>ty.
  have[t[lS tyS]]:=dyn_valid (era_dyn_type ty).
  apply: era_pair0_invX...
Qed.

Lemma era_pair1_inv Γ Δ A B m m' n n' s r :
  Γ ; Δ ⊢ Pair1 m n s ~ Pair1 m' n' s : Sig1 A B r ->
  exists Δ1 Δ2,
    Δ1 ∘ Δ2 => Δ /\ s = r /\
    Γ ; Δ1 ⊢ m ~ m' : A /\ Γ ; Δ2 ⊢ n ~ n' : B.[m/].
Proof with eauto.
  move=>ty.
  have[t[lS tyS]]:=dyn_valid (era_dyn_type ty).
  apply: era_pair1_invX...
Qed.
