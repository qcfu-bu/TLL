From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_var_form Θ Γ Δ m x B :
  Θ ; Γ ; Δ ⊢ m ~ Var x : B -> exists x, m = Var x.
Proof.
  move e:(Var x)=>n er. elim: er x e=>//{Θ Γ Δ m n B}.
  move=>Θ Γ Δ x s A emp wf shs dhs x0[e]. subst. by exists x.
Qed.

Lemma era_lam0_form Θ Γ Δ m n X B s :
  Θ ; Γ ; Δ ⊢ m ~ Lam0 X n s : B -> exists A n, m = Lam0 A n s.
Proof.
  move e:(Lam0 X n s)=>x er. elim: er X n s e=>//{Θ Γ Δ m x B}.
  move=>Θ Γ Δ A B m m' s k1 k2 erm ihm X n s0[e1 e2 e3]. subst.
  exists A. exists m. by [].
Qed.

Lemma era_lam1_form Θ Γ Δ m n X B s :
  Θ ; Γ ; Δ ⊢ m ~ Lam1 X n s : B -> exists A n, m = Lam1 A n s.
Proof.
  move e:(Lam1 X n s)=>x er. elim: er X n s e=>//{Θ Γ Δ m x B}.
  move=>Θ Γ Δ A B m m' s t k1 k2 erm ihm X n s0[e1 e2 e3]. subst.
  exists A. exists m. by [].
Qed.

Lemma era_app0_form Θ Γ Δ m n1 n2 B :
  Θ ; Γ ; Δ ⊢ m ~ App0 n1 n2 : B -> exists n1 n2, m = App0 n1 n2.
Proof.
  move e:(App0 n1 n2)=>x er. elim: er n1 n2 e=>//{Θ Γ Δ m x B}.
  move=>Θ Γ Δ A B m m' n s erm ihm tyn n1 n2[e1 e2]. subst.
  exists m. exists n. by [].
Qed.

Lemma era_app1_form Θ Γ Δ m n1 n2 B :
  Θ ; Γ ; Δ ⊢ m ~ App1 n1 n2 : B -> exists n1 n2, m = App1 n1 n2.
Proof.
  move e:(App1 n1 n2)=>x er. elim: er n1 n2 e=>//{Θ Γ Δ m x B}.
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2 erm ihm ern ihn n1 n2[e1 e2]. subst.
  exists m. exists n. by [].
Qed.

Lemma era_pair0_form Θ Γ Δ m n1 n2 A s :
  Θ ; Γ ; Δ ⊢ m ~ Pair0 n1 n2 s : A -> exists n1 n2, m = Pair0 n1 n2 s.
Proof.
  move e:(Pair0 n1 n2 s)=>x er. elim: er n1 n2 s e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ A B m n n' t tyS tym ern ihn n1 n2 s[e1 e2 e3]. subst.
  exists m. exists n. by [].
Qed.

Lemma era_pair1_form Θ Γ Δ m n1 n2 A s :
  Θ ; Γ ; Δ ⊢ m ~ Pair1 n1 n2 s : A -> exists n1 n2, m = Pair1 n1 n2 s.
Proof.
  move e:(Pair1 n1 n2 s)=>x er. elim: er n1 n2 s e=>//{Θ Γ Δ m x A}.
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2 tyS erm ihm ern ihn n1 n2 s[e1 e2 e3]. subst.
  exists m. exists n. by [].
Qed.

Lemma era_letin_form Θ Γ Δ m n1 n2 X A :
  Θ ; Γ ; Δ ⊢ m ~ LetIn X n1 n2 : A -> exists X n1 n2, m = LetIn X n1 n2.
Proof.
  move e:(LetIn X n1 n2)=>x er. elim: er X n1 n2 e=>//{Θ Γ Δ m x A}.
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2
         tyC erm ihm ern ihn X n1 n2[e1 e2 e3]. subst.
  exists C. exists m. exists n. by [].
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2
         tyC erm ihm ern ihn X n1 n2[e1 e2 e3]. subst.
  exists C. exists m. exists n. by [].
Qed.

Lemma era_fix_form Θ Γ Δ m n X A :
  Θ ; Γ ; Δ ⊢ m ~ Fix X n : A -> exists X n, m = Fix X n.
Proof.
  move e:(Fix X n)=>x er. elim: er X n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ A m m' k1 k2 erm ihm X n[e1 e2]. subst.
  exists A. exists m. by [].
Qed.

Lemma era_ii_form Θ Γ Δ m A :
  Θ ; Γ ; Δ ⊢ m ~ II : A -> m = II.
Proof. move e:(II)=>x er. elim: er e=>//. Qed.

Lemma era_tt_form Θ Γ Δ m A :
  Θ ; Γ ; Δ ⊢ m ~ TT : A -> m = TT.
Proof. move e:(TT)=>x er. elim: er e=>//. Qed.

Lemma era_ff_form Θ Γ Δ m A :
  Θ ; Γ ; Δ ⊢ m ~ FF : A -> m = FF.
Proof. move e:(FF)=>x er. elim: er e=>//. Qed.

Lemma era_ifte_form Θ Γ Δ m n1 n2 n3 X A :
  Θ ; Γ ; Δ ⊢ m ~ Ifte X n1 n2 n3 : A -> exists X n1 n2 n3, m = Ifte X n1 n2 n3.
Proof.
  move e:(Ifte X n1 n2 n3)=>x er. elim: er X n1 n2 n3 e=>//{Θ Γ Δ m x A}.
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2
         tyA erm ihm ern1 ihn1 ern2 ihn2 X m1 m2 m3[e1 e2 e3 e4]. subst.
  exists A. exists m. exists n1. exists n2. by [].
Qed.

Lemma era_return_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ m ~ Return n : A -> exists n, m = Return n.
Proof.
  move e:(Return n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ m m' A erm ihm n[e]. subst. exists m. by [].
Qed.

Lemma era_bind_form Θ Γ Δ m n1 n2 A :
  Θ ; Γ ; Δ ⊢ m ~ Bind n1 n2 : A -> exists n1 n2, m = Bind n1 n2.
Proof.
  move e:(Bind n1 n2)=>x er. elim: er n1 n2 e=>//{Θ Γ Δ m x A}.
  move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2 tyB erm ihm ern ihn n1 n2[e1 e2]. subst.
  exists m. exists n. by [].
Qed.

Lemma era_cvar_form Θ Γ Δ m x A :
  Θ ; Γ ; Δ ⊢ m ~ CVar x : A -> exists x, m = CVar x.
Proof.
  move e:(CVar x)=>n er. elim: er x e=>//{Θ Γ Δ m n A}.
  move=>Θ Γ Δ r x A js wf k tyA x0[e]. subst.
  exists x. by [].
Qed.

Lemma era_fork_form Θ Γ Δ m n X A :
  Θ ; Γ ; Δ ⊢ m ~ Fork X n : A -> exists X n, m = Fork X n.
Proof.
  move e:(Fork X n)=>x er. elim: er X n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ m m' A erm ihm X n[e1 e2]. subst.
  exists A. exists m. by [].
Qed.

Lemma era_recv0_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ m ~ Recv0 n : A -> exists n, m = Recv0 n.
Proof.
  move e:(Recv0 n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm n[e]. subst.
  exists m. by [].
Qed.

Lemma era_recv1_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ m ~ Recv1 n : A -> exists n, m = Recv1 n.
Proof.
  move e:(Recv1 n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm n[e]. subst.
  exists m. by [].
Qed.

Lemma era_send0_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ m ~ Send0 n : A -> exists n, m = Send0 n.
Proof.
  move e:(Send0 n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm n[e]. subst.
  exists m. by [].
Qed.

Lemma era_send1_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ m ~ Send1 n : A -> exists n, m = Send1 n.
Proof.
  move e:(Send1 n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm n[e]. subst.
  exists m. by [].
Qed.

Lemma era_wait_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ m ~ Wait n : A -> exists n, m = Wait n.
Proof.
  move e:(Wait n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ m m' erm ihm n[e]. subst.
  exists m. by [].
Qed.

Lemma era_close_form Θ Γ Δ m n A :
  Θ ; Γ ; Δ ⊢ m ~ Close n : A -> exists n, m = Close n.
Proof.
  move e:(Close n)=>x er. elim: er n e=>//{Θ Γ Δ m x A}.
  move=>Θ Γ Δ m m' erm ihm n[e]. subst.
  exists m. by [].
Qed.

Lemma era_box_form Θ Γ Δ m A : ~Θ ; Γ ; Δ ⊢ m ~ Box : A. 
Proof. move e:(Box)=>n er. elim: er e=>//{Θ Γ Δ m n A}. Qed.

Lemma era_lam0_invX Θ Γ Δ A1 A2 A3 B C m1 m2 s1 s2 t :
  Θ ; Γ ; Δ ⊢ Lam0 A1 m1 s1 ~ Lam0 A2 m2 s1 : C ->
  C === Pi0 A3 B s2 ->
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
  C === Pi1 A3 B s2 ->
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
  C === Sig0 A B r ->
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
  C === Sig1 A B r ->
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



