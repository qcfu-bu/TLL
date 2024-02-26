From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_var_form Θ Γ Δ m x B :
  Θ ; Γ ; Δ ⊢ Var x ~ m : B -> exists x, m = Var x.
Proof.
  move e:(Var x)=>n er. elim: er x e=>//{Θ Γ Δ m n B}.
  move=>Θ Γ Δ x s A emp wf shs dhs x0[e]. subst. by exists x.
Qed.

Lemma era_lam0_form Θ Γ Δ m n X B s :
  Θ ; Γ ; Δ ⊢ Lam0 X n s ~ m : B -> exists n, m = Lam0 Box n s.
Proof.
  move e:(Lam0 X n s)=>x er. elim: er X n s e=>//{Θ Γ Δ m x B}.
  move=>Θ Γ Δ A B m m' s k1 k2 erm ihm X n s0[e1 e2 e3]. subst.
  exists m'. by [].
Qed.

Lemma era_lam1_form Θ Γ Δ m n X B s :
  Θ ; Γ ; Δ ⊢ Lam1 X n s ~ m : B -> exists n, m = Lam1 Box n s.
Proof.
  move e:(Lam1 X n s)=>x er. elim: er X n s e=>//{Θ Γ Δ m x B}.
  move=>Θ Γ Δ A B m m' s t k1 k2 erm ihm X n s0[e1 e2 e3]. subst.
  exists m'. by [].
Qed.

Lemma era_app0_form Θ Γ Δ m n1 n2 B :
  Θ ; Γ ; Δ ⊢ App0 n1 n2 ~ m : B -> exists n1, m = App0 n1 Box.
Proof.
  move e:(App0 n1 n2)=>x er. elim: er n1 n2 e=>//{Θ Γ Δ m x B}.
  move=>Θ Γ Δ A B m m' n s erm ihm tyn n1 n2[e1 e2]. subst.
  exists m'. by [].
Qed.

Lemma era_app1_form Θ Γ Δ m n1 n2 B :
  Θ ; Γ ; Δ ⊢ App1 n1 n2 ~ m : B -> exists n1 n2, m = App1 n1 n2.
Proof.
  move e:(App1 n1 n2)=>x er. elim: er n1 n2 e=>//{Θ Γ Δ m x B}.
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2 erm ihm ern ihn n1 n2[e1 e2]. subst.
  exists m'. exists n'. by [].
Qed.

Lemma era_pair0_form Θ Γ Δ m n1 n2 A s :
  Θ ; Γ ; Δ ⊢ Pair0 n1 n2 s ~ m : A -> exists n2, m = Pair0 Box n2 s.
Proof.
  move e:(Pair0 n1 n2 s)=>x er. elim: er n1 n2 s e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ A B m n n' t tyS tym ern ihn n1 n2 s[e1 e2 e3]. subst.
  exists n'. by [].
Qed.

Lemma era_pair1_form Θ Γ Δ m n1 n2 A s :
  Θ ; Γ ; Δ ⊢ Pair1 n1 n2 s ~ m : A -> exists n1 n2, m = Pair1 n1 n2 s.
Proof.
  move e:(Pair1 n1 n2 s)=>x er. elim: er n1 n2 s e=>//{Θ Γ Δ m x A}.
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2 tyS erm ihm ern ihn n1 n2 s[e1 e2 e3]. subst.
  exists m'. exists n'. by [].
Qed.

Lemma era_letin_form Θ Γ Δ m n1 n2 X A :
  Θ ; Γ ; Δ ⊢ LetIn X n1 n2 ~ m : A -> exists n1 n2, m = LetIn Box n1 n2.
Proof.
  move e:(LetIn X n1 n2)=>x er. elim: er X n1 n2 e=>//{Θ Γ Δ m x A}.
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2
         tyC erm ihm ern ihn X n1 n2[e1 e2 e3]. subst.
  exists m'. exists n'. by [].
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2
         tyC erm ihm ern ihn X n1 n2[e1 e2 e3]. subst.
  exists m'. exists n'. by [].
Qed.

Lemma era_fix_form Θ Γ Δ m n X A :
  Θ ; Γ ; Δ ⊢ Fix X n ~ m : A -> exists n, m = Fix Box n.
Proof.
  move e:(Fix X n)=>x er. elim: er X n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ A m m' k1 k2 erm ihm X n[e1 e2]. subst.
  exists m'. by [].
Qed.

Lemma era_ii_form Θ Γ Δ m A :
  Θ ; Γ ; Δ ⊢ II ~ m : A -> m = II.
Proof. move e:(II)=>x er. elim: er e=>//. Qed.

Lemma era_tt_form Θ Γ Δ m A :
  Θ ; Γ ; Δ ⊢ TT ~ m : A -> m = TT.
Proof. move e:(TT)=>x er. elim: er e=>//. Qed.

Lemma era_ff_form Θ Γ Δ m A :
  Θ ; Γ ; Δ ⊢ FF ~ m : A -> m = FF.
Proof. move e:(FF)=>x er. elim: er e=>//. Qed.

Lemma era_ifte_form Θ Γ Δ m n1 n2 n3 X A :
  Θ ; Γ ; Δ ⊢ Ifte X n1 n2 n3 ~ m : A -> exists n1 n2 n3, m = Ifte Box n1 n2 n3.
Proof.
  move e:(Ifte X n1 n2 n3)=>x er. elim: er X n1 n2 n3 e=>//{Θ Γ Δ m x A}.
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2
         tyA erm ihm ern1 ihn1 ern2 ihn2 X m1 m2 m3[e1 e2 e3 e4]. subst.
  exists m'. exists n1'. exists n2'. by [].
Qed.

Lemma era_return_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ Return n ~ m : A -> exists n, m = Return n.
Proof.
  move e:(Return n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ m m' A erm ihm n[e]. subst. exists m'. by [].
Qed.

Lemma era_bind_form Θ Γ Δ m n1 n2 A :
  Θ ; Γ ; Δ ⊢ Bind n1 n2 ~ m : A -> exists n1 n2, m = Bind n1 n2.
Proof.
  move e:(Bind n1 n2)=>x er. elim: er n1 n2 e=>//{Θ Γ Δ m x A}.
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2 tyB erm ihm ern ihn n1 n2[e1 e2]. subst.
  exists m'. exists n'. by [].
Qed.

Lemma era_cvar_form Θ Γ Δ m x A :
  Θ ; Γ ; Δ ⊢ CVar x ~ m : A -> m = CVar x.
Proof. move e:(CVar x)=>n er. elim: er x e=>//{Θ Γ Δ m n A}. Qed.

Lemma era_fork_form Θ Γ Δ m n X A :
  Θ ; Γ ; Δ ⊢ Fork X n ~ m : A -> exists n, m = Fork Box n.
Proof.
  move e:(Fork X n)=>x er. elim: er X n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ m m' A erm ihm X n[e1 e2]. subst.
  exists m'. by [].
Qed.

Lemma era_recv0_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ Recv0 n ~ m : A -> exists n, m = Recv0 n.
Proof.
  move e:(Recv0 n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm n[e]. subst.
  exists m'. by [].
Qed.

Lemma era_recv1_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ Recv1 n ~ m : A -> exists n, m = Recv1 n.
Proof.
  move e:(Recv1 n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm n[e]. subst.
  exists m'. by [].
Qed.

Lemma era_send0_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ Send0 n ~ m : A -> exists n, m = Send0 n.
Proof.
  move e:(Send0 n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm n[e]. subst.
  exists m'. by [].
Qed.

Lemma era_send1_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ Send1 n ~ m : A -> exists n, m = Send1 n.
Proof.
  move e:(Send1 n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm n[e]. subst.
  exists m'. by [].
Qed.

Lemma era_wait_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ Wait n ~ m : A -> exists n, m = Wait n.
Proof.
  move e:(Wait n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ m m' erm ihm n[e]. subst.
  exists m'. by [].
Qed.

Lemma era_close_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ Close n ~ m : A -> exists n, m = Close n.
Proof.
  move e:(Close n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ m m' erm ihm n[e]. subst.
  exists m'. by [].
Qed.

Lemma era_box_form Θ Γ Δ m A : ~Θ ; Γ ; Δ ⊢ m ~ Box : A. 
Proof. move e:(Box)=>n er. elim: er e=>//{Θ Γ Δ m n A}. Qed.

Lemma era_lam0_invX Θ Γ Δ A1 A2 A3 B C m1 m2 s1 s2 t :
  Θ ; Γ ; Δ ⊢ Lam0 A1 m1 s1 ~ Lam0 A2 m2 s1 : C ->
  C ≃ Pi0 A3 B s2 ->
  (A3 :: Γ) ⊢ B : Sort t ->
  Θ ; (A3 :: Γ) ; _: Δ ⊢ m1 ~ m2 : B.
Proof with eauto.
  move e1:(Lam0 A1 m1 s1)=>n1.
  move e2:(Lam0 A2 m2 s1)=>n2 er.
  elim: er A1 A2 A3 B m1 m2 s1 s2 t e1 e2=>//{Θ Γ Δ n1 n2 C}.
  { move=>Θ Γ Δ A B1 m m' s k1 k2 erm ihm A1 A2 A3 B2 m1 m2 s1 s2 t
           [e1 e2 e3][e4 e5 e6]. subst.
    move=>/pi0_inj[eq1[eq2 e]]tyB. subst.
    have wf:=sta_type_wf tyB. inv wf.
    apply: era_conv...
    apply: era_ctx_conv0.
    exact: (conv_sym eq1).
    exact: H2.
    exact: erm. }
  { move=>Θ Γ Δ A B m m' s eq1 erm ihm tyB A1 A2 A3 B0 m1 m2
           s1 s2 t e1 e2 eq tyB0. subst.
    apply: ihm...
    apply: conv_trans... }
Qed.
       
Lemma era_lam1_invX Θ Γ Δ A1 A2 A3 B C m1 m2 s1 s2 t :
  Θ ; Γ ; Δ ⊢ Lam1 A1 m1 s1 ~ Lam1 A2 m2 s1 : C ->
  C ≃ Pi1 A3 B s2 ->
  (A3 :: Γ) ⊢ B : Sort t ->
  exists r, Θ ; (A3 :: Γ) ; A3 .{r} Δ ⊢ m1 ~ m2 : B.
Proof with eauto.
  move e1:(Lam1 A1 m1 s1)=>n1.
  move e2:(Lam1 A2 m2 s1)=>n2 er.
  elim: er A1 A2 A3 B m1 m2 s1 s2 t e1 e2=>//{Θ Γ Δ n1 n2 C}.
  { move=>Θ Γ Δ A B1 m m' s t k1 k2 erm ihm A1 A2 A3 B2 m1 m2 s1 s2 t1
           [e1 e2 e3][e4 e5 e6]. subst.
    move=>/pi1_inj[eq1[eq2 e]]tyB. subst.
    have wf:=era_type_wf erm. inv wf.
    have wf:=sta_type_wf tyB. inv wf.
    have[A0 rd1 rd2]:=church_rosser eq1.
    have tyA0t:=sta_prd H4 rd1.
    have tyA0s:=sta_prd H3 rd2.
    have e:=sta_unicity tyA0t tyA0s. subst.
    exists s.
    apply: era_conv...
    apply: era_ctx_conv1.
    exact: (conv_sym eq1).
    exact: H3.
    exact: erm. }
  { move=>Θ Γ Δ A B m m' s eq1 erm ihm tyB A1 A2 A3 B0 m1 m2
           s1 s2 t e1 e2 eq tyB0. subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma era_lam0_inv Θ Γ Δ m1 m2 A1 A2 A3 B s1 s2 :
  Θ ; Γ ; Δ ⊢ Lam0 A1 m1 s1 ~ Lam0 A2 m2 s1 : Pi0 A3 B s2 ->
  Θ ; (A3 :: Γ) ; _: Δ ⊢ m1 ~ m2 : B.
Proof with eauto.
  move=>er.
  have[t/sta_pi0_inv[r[tyB _]]]:=era_valid er.
  apply: era_lam0_invX...
Qed.

Lemma era_lam1_inv Θ Γ Δ m1 m2 A1 A2 A3 B s1 s2 :
  Θ ; Γ ; Δ ⊢ Lam1 A1 m1 s1 ~ Lam1 A2 m2 s1 : Pi1 A3 B s2 ->
  exists r, Θ ; (A3 :: Γ) ; A3 .{r} Δ ⊢ m1 ~ m2 : B.
Proof with eauto.
  move=>er.
  have[t/sta_pi1_inv[r[tyB _]]]:=era_valid er.
  apply: era_lam1_invX...
Qed.

Lemma era_pair0_invX Θ Γ Δ A B m1 m2 n1 n2 s r t C :
  Θ ; Γ ; Δ ⊢ Pair0 m1 n1 s ~ Pair0 m2 n2 s  : C ->
  C ≃ Sig0 A B r ->
  Γ ⊢ Sig0 A B r : Sort t ->
  s = r /\ m2 = Box /\ Γ ⊢ m1 : A /\ Θ ; Γ ; Δ ⊢ n1 ~ n2 : B.[m1/].
Proof with eauto.
  move e1:(Pair0 m1 n1 s)=>x.
  move e2:(Pair0 m2 n2 s)=>y er.
  elim: er A B m1 m2 n1 n2 s r t e1 e2=>//{Θ Γ Δ x y C}.
  { move=>Θ Γ Δ A B m n n' t tyS tym tyn _ A0 B0 m1 m2 n1 n2
           s r t0[e1 e2 e3][e4 e5 e6]/sig0_inj[e7[e8 e9]]ty2; subst.
    have[s[r0[ord[tyA0[tyB0/sort_inj e]]]]]:=sta_sig0_inv ty2. subst.
    have tym0: Γ ⊢ m : A0 by apply: sta_conv; eauto.
    repeat split...
    apply: era_conv.
    apply: sta_conv_subst.
    all: eauto.
    apply: sta_esubst...
    by autosubst. }
  { move=>Θ Γ Δ A B m m' s eq tym ihm tyB A0 B0 m1 m2 n1 n2
           s0 r t e1 e2 eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma era_pair1_invX Θ Γ Δ A B m1 m2 n1 n2 s r t C :
  Θ ; Γ ; Δ ⊢ Pair1 m1 n1 s ~ Pair1 m2 n2 s  : C ->
  C ≃ Sig1 A B r ->
  Γ ⊢ Sig1 A B r : Sort t ->
  exists Θ1 Θ2 Δ1 Δ2,
    s = r /\
    Θ1 ∘ Θ2 => Θ /\
    Δ1 ∘ Δ2 => Δ /\
    Θ1 ; Γ ; Δ1 ⊢ m1 ~ m2 : A /\
    Θ2 ; Γ ; Δ2 ⊢ n1 ~ n2 : B.[m1/].
Proof with eauto.
  move e1:(Pair1 m1 n1 s)=>x.
  move e2:(Pair1 m2 n2 s)=>y er.
  elim: er A B m1 m2 n1 n2 s r t e1 e2=>//{Θ Γ Δ x y C}.
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2
           tyS erm _ ern _ A0 B0 m1 m2 n1 n2 s r t0
           [e1 e2 e3][e4 e5 e6]/sig1_inj[e7[e8 e9]]ty2; subst.
    exists Θ1. exists Θ2. exists Δ1. exists Δ2.
    have[s[r0[ord1[ord2[tyA0[tyB0/sort_inj e]]]]]]:=sta_sig1_inv ty2. subst.
    have tym0:Θ1; Γ ; Δ1 ⊢ m ~ m' : A0 by apply: era_conv; eauto.
    repeat split...
    apply: era_conv.
    apply: sta_conv_subst.
    all: eauto.
    apply: sta_esubst...
    by autosubst. }
  { move=>Θ Γ Δ A B m m' s eq erm ihm tyB A0 B0 m1 m2 n1 n2 s0 r t e1 e2 eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma era_pair0_inv Θ Γ Δ A B m1 m2 n1 n2 s r :
  Θ ; Γ ; Δ ⊢ Pair0 m1 n1 s ~ Pair0 m2 n2 s : Sig0 A B r ->
  s = r /\ m2 = Box /\ Γ ⊢ m1 : A /\ Θ ; Γ ; Δ ⊢ n1 ~ n2 : B.[m1/].
Proof with eauto.
  move=>ty.
  have[t tyS]:=era_valid ty.
  apply: era_pair0_invX...
Qed.

Lemma era_pair1_inv Θ Γ Δ A B m1 m2 n1 n2 s r :
  Θ ; Γ ; Δ ⊢ Pair1 m1 n1 s ~ Pair1 m2 n2 s : Sig1 A B r ->
  exists Θ1 Θ2 Δ1 Δ2,
    s = r /\
    Θ1 ∘ Θ2 => Θ /\ 
    Δ1 ∘ Δ2 => Δ /\ 
    Θ1 ; Γ ; Δ1 ⊢ m1 ~ m2 : A /\
    Θ2 ; Γ ; Δ2 ⊢ n1 ~ n2 : B.[m1/].
Proof with eauto.
  move=>ty.
  have[t tyS]:=era_valid ty.
  apply: era_pair1_invX...
Qed.

Lemma era_app0_inv Θ Γ Δ m1 m2 n1 n2 C :
  Θ ; Γ ; Δ ⊢ App0 m1 n1 ~ App0 m2 n2 : C ->
  exists A B s,
    n2 = Box /\
    Θ ; Γ ; Δ ⊢ m1 ~ m2 : Pi0 A B s /\
    Γ ⊢ n1 : A /\ C ≃ B.[n1/].
Proof with eauto.
  move e1:(App0 m1 n1)=>x.
  move e2:(App0 m2 n2)=>y er.
  elim: er m1 m2 n1 n2 e1 e2=>//{Θ Γ Δ x y C}.
  { move=>Θ Γ Δ A B m m' n s erm ihm tyn m1 m2 n1 n2[e1 e2][e3 e4]; subst.
    exists A. exists B. exists s. split... }
  { move=>Θ Γ Δ A B m m' s eq1 erm ihm tyB m1 m2 n1 n2 e1 e2; subst.
    have [A0[B0[s0[e[tym0[tyn0 eq2]]]]]]:=ihm _ _ _ _ erefl erefl.
    exists A0. exists B0. exists s0. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma era_app1_inv Θ Γ Δ m1 m2 n1 n2 C :
  Θ ; Γ ; Δ ⊢ App1 m1 n1 ~ App1 m2 n2 : C ->
  exists A B s Θ1 Θ2 Δ1 Δ2,
    Θ1 ∘ Θ2 => Θ /\
    Δ1 ∘ Δ2 => Δ /\
    Θ1 ; Γ ; Δ1 ⊢ m1 ~ m2 : Pi1 A B s /\
    Θ2 ; Γ ; Δ2 ⊢ n1 ~ n2 : A /\
    C ≃ B.[n1/].
Proof with eauto.
  move e1:(App1 m1 n1)=>x.
  move e2:(App1 m2 n2)=>y er.
  elim: er m1 m2 n1 n2 e1 e2=>//{Θ Γ Δ x y C}.
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2
           erm ihm ern ihn m1 m2 n1 n2[e1 e2][e3 e4]; subst.
    exists A. exists B. exists s. exists Θ1. exists Θ2. exists Δ1. exists Δ2. split... }
  { move=>Θ Γ Δ A B m m' s eq1 erm ihm tyB m1 m2 n1 n2 e1 e2; subst.
    have [A0[B0[s0[Θ1[Θ2[Δ1[Δ2[mrg1[mrg2[tym0[tyn0 eq2]]]]]]]]]]]:=ihm _ _ _ _ erefl erefl.
    exists A0. exists B0. exists s0. exists Θ1. exists Θ2. exists Δ1. exists Δ2. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma era_ii_inv Θ Γ Δ A : Θ ; Γ ; Δ ⊢ II ~ II : A -> dyn_empty Θ.
Proof with eauto. move e:(II)=>m er. elim: er e=>//{Θ Γ Δ A}. Qed.

Lemma era_tt_inv Θ Γ Δ A : Θ ; Γ ; Δ ⊢ TT ~ TT : A -> dyn_empty Θ.
Proof with eauto. move e:(TT)=>m er. elim: er e=>//{Θ Γ Δ A}. Qed.

Lemma era_ff_inv Θ Γ Δ A : Θ ; Γ ; Δ ⊢ FF ~ FF : A -> dyn_empty Θ.
Proof with eauto. move e:(FF)=>m er. elim: er e=>//{Θ Γ Δ A}. Qed.

Lemma era_return_invX Θ Γ Δ m1 m2 B :
  Θ ; Γ ; Δ ⊢ Return m1 ~ Return m2 : B ->
  exists A, Θ ; Γ ; Δ ⊢ m1 ~ m2 : A /\ B ≃ IO A.
Proof with eauto.
  move e1:(Return m1)=>x.
  move e2:(Return m2)=>y ty.
  elim: ty m1 m2 e1 e2=>//{Θ Γ Δ x y B}.
  { move=>Θ Γ Δ m m' A tym ihm m1 m2[e1][e2]; subst. exists A... }
  { move=>Θ Γ Δ A B m m' s eq1 tym ihm tyB m1 m2 e1 e2; subst.
    have[A0[tym0 eq2]]:=ihm _ _ erefl erefl.
    exists A0. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma era_return_inv Θ Γ Δ m1 m2 A :
  Θ ; Γ ; Δ ⊢ Return m1 ~ Return m2 : IO A -> Θ ; Γ ; Δ ⊢ m1 ~ m2 : A.
Proof with eauto.
  move=>ty.
  have[B[erm/io_inj eq]]:=era_return_invX ty.
  have[s tyIO]:=era_valid ty.
  have[r[tyA/sort_inj e]]:=sta_io_inv tyIO. subst.
  apply: era_conv.
  apply: conv_sym...
  apply: erm. apply: tyA.
Qed.

Lemma era_bind_invX Θ Γ Δ m1 m2 n1 n2 C :
  Θ ; Γ ; Δ ⊢ Bind m1 n1 ~ Bind m2 n2 : C ->
  exists Θ1 Θ2 Δ1 Δ2 A B s t,
    Θ1 ∘ Θ2 => Θ /\
    Δ1 ∘ Δ2 => Δ /\
    Γ ⊢ B : Sort t /\
    Θ1 ; Γ ; Δ1 ⊢ m1 ~ m2 : IO A /\
    Θ2 ; (A :: Γ) ; (A .{s} Δ2) ⊢ n1 ~ n2 : IO B.[ren (+1)] /\
    C ≃ IO B.
Proof with eauto.
  move e1:(Bind m1 n1)=>x.
  move e2:(Bind m2 n2)=>y er.
  elim: er m1 m2 n1 n2 e1 e2=>//{Θ Γ Δ x y C}.
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2 tyB
           tym _ tyn _ m1 m2 n1 n2[e1 e2][e3 e4]. subst.
    exists Θ1. exists Θ2. exists Δ1. exists Δ2. exists A. exists B. exists s. exists t.
    repeat split... }
  { move=>Θ Γ Δ A B m m' s eq tym ihm tyB m1 m2 n1 n2 e1 e2. subst.
    have[Θ1[Θ2[Δ1[Δ2[A0[B0[s0[t[mrg1[mrg2[tyB0[tym0[tyn eq']]]]]]]]]]]]]:=
      ihm _ _ _ _ erefl erefl.
    exists Θ1. exists Θ2. exists Δ1. exists Δ2. exists A0. exists B0. exists s0. exists t.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq'. }
Qed.

Lemma era_bind_inv Θ Γ Δ m1 m2 n1 n2 B :
  Θ ; Γ ; Δ ⊢ Bind m1 n1 ~ Bind m2 n2 : IO B ->
  exists Θ1 Θ2 Δ1 Δ2 A s,
    Θ1 ∘ Θ2 => Θ /\
    Δ1 ∘ Δ2 => Δ /\
    Θ1 ; Γ ; Δ1 ⊢ m1 ~ m2 : IO A /\
    Θ2 ; (A :: Γ) ; (A .{s} Δ2) ⊢ n1 ~ n2 : IO B.[ren (+1)].
Proof with eauto.
  move=>ty.
  have[Θ1[Θ2[Δ1[Δ2[A0[B0[s[t[mrg1[mrg2[tyB0[tym[tyn/io_inj eq]]]]]]]]]]]]]:=
    era_bind_invX ty.
  have[s0 tyIO]:=era_valid ty.
  have wf:=era_type_wf tyn. inv wf.
  have/={}tyIO:=sta_weaken tyIO H4.
  exists Θ1. exists Θ2. exists Δ1. exists Δ2. exists A0. exists s.
  repeat split...
  apply: era_conv.
  apply: sta_conv_io.
  apply: sta_conv_subst.
  apply: conv_sym...
  apply: tyn.
  apply: tyIO.
Qed.

Lemma era_cvar_inv Θ Γ Δ x1 x2 B :
  Θ ; Γ ; Δ ⊢ CVar x1 ~ CVar x2 : B ->
  exists r A,
    x1 = x2 /\
    dyn_just Θ x1 (Ch r A) /\
    nil ⊢ A : Proto /\
    B ≃ Ch r A.[ren (+size Γ)].
Proof with eauto.
  move e1:(CVar x1)=>m1.
  move e2:(CVar x2)=>m2 ty.
  elim: ty x1 x2 e1 e2=>//{Θ Γ Δ m1 m2 B}.
  { move=>Θ Γ Δ r x A js _ _ tyA x1 x2[e1][e2]. subst.
    exists r. exists A... }
  { move=>Θ Γ Δ A B m m' s eq1 tym ihm tyB x1 x2 e1 e2. subst.
    have[r[A0[e[js[tyA0 eq2]]]]]:=ihm _ _ erefl erefl. subst.
    exists r. exists A0.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    apply: eq2. }
Qed.

Lemma era_fork_inv Θ Γ Δ A1 A2 m1 m2 B :
  Θ ; Γ ; Δ ⊢ Fork A1 m1 ~ Fork A2 m2 : B ->
  A2 = Box /\
  Θ ; (Ch true A1 :: Γ) ; Ch true A1 :L Δ ⊢ m1 ~ m2 : IO Unit /\
  B ≃ IO (Ch false A1).
Proof with eauto.
  move e1:(Fork A1 m1)=>x.
  move e2:(Fork A2 m2)=>y er.
  elim: er A1 A2 m1 m2 e1 e2=>//{Θ Γ Δ x y B}.
  { move=>Θ Γ Δ m m' A tym ihm A1 A2 m1 m2[e1 e2][e3 e4]. subst... }
  { move=>Θ Γ Δ A B m m' s eq1 tym ihm tyB A1 A2 m1 m2 e1 e2. subst.
    have[e[tym0 eq2]]:=ihm _ _ _ _ erefl erefl. subst.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma era_recv0_inv Θ Γ Δ m1 m2 C :
  Θ ; Γ ; Δ ⊢ Recv0 m1 ~ Recv0 m2 : C ->
  exists r1 r2 A B,
    r1 (+) r2 = false /\
    C ≃ IO (Sig0 A (Ch r1 B) L) /\
    Θ ; Γ ; Δ ⊢ m1 ~ m2 : Ch r1 (Act0 r2 A B).
Proof with eauto.
  move e1:(Recv0 m1)=>x.
  move e2:(Recv0 m2)=>y er.
  elim: er m1 m2 e1 e2=>//{Θ Γ Δ x y C}.
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm m1 m2[e1][e2]. subst.
    exists r1. exists r2. exists A. exists B... }
  { move=>Θ Γ Δ A B m m' s eq1 tym ihm tyB m1 m2 e1 e2. subst.
    have[r1[r2[A0[B0[xor[eq2 tym0]]]]]]:=ihm _ _ erefl erefl.
    exists r1. exists r2. exists A0. exists B0.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    apply: eq2. }
Qed.

Lemma era_recv1_inv Θ Γ Δ m1 m2 C :
  Θ ; Γ ; Δ ⊢ Recv1 m1 ~ Recv1 m2 : C ->
  exists r1 r2 A B,
    r1 (+) r2 = false /\
    C ≃ IO (Sig1 A (Ch r1 B) L) /\
    Θ ; Γ ; Δ ⊢ m1 ~ m2 : Ch r1 (Act1 r2 A B).
Proof with eauto.
  move e1:(Recv1 m1)=>x.
  move e2:(Recv1 m2)=>y ty.
  elim: ty m1 m2 e1 e2=>//{Θ Γ Δ x y C}.
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm m1 m2[e1][e2]. subst.
    exists r1. exists r2. exists A. exists B... }
  { move=>Θ Γ Δ A B m m' s eq1 tym ihm tyB m1 m2 e1 e2. subst.
    have[r1[r2[A0[B0[xor[eq2 tym0]]]]]]:=ihm _ _ erefl erefl.
    exists r1. exists r2. exists A0. exists B0.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    apply: eq2. }
Qed.

Lemma era_send0_inv Θ Γ Δ m1 m2 C :
  Θ ; Γ ; Δ ⊢ Send0 m1 ~ Send0 m2 : C ->
  exists r1 r2 A B,
    r1 (+) r2 = true /\
    C ≃ Pi0 A (IO (Ch r1 B)) L /\
    Θ ; Γ ; Δ ⊢ m1 ~ m2 : Ch r1 (Act0 r2 A B).
Proof with eauto.
  move e1:(Send0 m1)=>x.
  move e2:(Send0 m2)=>y ty.
  elim: ty m1 m2 e1 e2=>//{Θ Γ Δ x y C}.
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm m1 m2[e1][e2]. subst.
    exists r1. exists r2. exists A. exists B.
    repeat split... }
  { move=>Θ Γ Δ A B m m' s eq1 tym ihm tyB m1 m2 e1 e2. subst.
    have[r1[r2[A0[B0[xor[eq2 tym0]]]]]]:=ihm _ _ erefl erefl.
    exists r1. exists r2. exists A0. exists B0.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    apply: eq2. }
Qed.

Lemma era_send1_inv Θ Γ Δ m1 m2 C :
  Θ ; Γ ; Δ ⊢ Send1 m1 ~ Send1 m2 : C ->
  exists r1 r2 A B,
    r1 (+) r2 = true /\
    C ≃ Pi1 A (IO (Ch r1 B)) L /\
    Θ ; Γ ; Δ ⊢ m1 ~ m2 : Ch r1 (Act1 r2 A B).
Proof with eauto.
  move e1:(Send1 m1)=>x.
  move e2:(Send1 m2)=>y ty.
  elim: ty m1 m2 e1 e2=>//{Θ Γ Δ x y C}.
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm m1 m2[e1][e2]. subst.
    exists r1. exists r2. exists A. exists B.
    repeat split... }
  { move=>Θ Γ Δ A B m m' s eq1 tym ihm tyB m1 m2 e1 e2. subst.
    have[r1[r2[A0[B0[xor[eq2 tym0]]]]]]:=ihm _ _ erefl erefl.
    exists r1. exists r2. exists A0. exists B0.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    apply: eq2. }
Qed.

Lemma era_wait_inv Θ Γ Δ m1 m2 C :
  Θ ; Γ ; Δ ⊢ Wait m1 ~ Wait m2 : C ->
  C ≃ IO Unit /\
  Θ ; Γ ; Δ ⊢ m1 ~ m2 : Ch false Stop.
 Proof with eauto. 
   move e1:(Wait m1)=>x.
   move e2:(Wait m2)=>y ty.
   elim: ty m1 m2 e1 e2=>//{Θ Γ Δ x y C}.
   { move=>Θ Γ Δ m m' tym ihm m1 m2[e1][e2]. subst.
     repeat split... }
   { move=>Θ Γ Δ A B m m' s eq1 tym ihm tyB m1 m2 e1 e2. subst.
     have[eq2 tym0]:=ihm _ _ erefl erefl.
     repeat split...
     apply: conv_trans.
     apply: conv_sym...
     apply: eq2. }
 Qed.

Lemma era_close_inv Θ Γ Δ m1 m2 C :
  Θ ; Γ ; Δ ⊢ Close m1 ~ Close m2 : C ->
  C ≃ IO Unit /\
  Θ ; Γ ; Δ ⊢ m1 ~ m2 : Ch true Stop.
 Proof with eauto. 
   move e1:(Close m1)=>x.
   move e2:(Close m2)=>y ty.
   elim: ty m1 m2 e1 e2=>//{Θ Γ Δ x y C}.
   { move=>Θ Γ Δ m m' tym ihm m1 m2[e1][e2]. subst.
     repeat split... }
   { move=>Θ Γ Δ A B m m' s eq1 tym ihm tyB m1 m2 e1 e2. subst.
     have[eq2 tym0]:=ihm _ _ erefl erefl.
     repeat split...
     apply: conv_trans.
     apply: conv_sym...
     apply: eq2. }
 Qed.
