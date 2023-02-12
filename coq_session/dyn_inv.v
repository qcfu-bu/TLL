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
  exists r, Θ ; (A2 :: Γ) ; A2 .{r} Δ ⊢ m : B.
Proof with eauto.
  move e:(Lam1 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t e=>//{Θ Γ Δ C n}.
  { move=>Θ Γ Δ A B m s t k1 k2 tym _ A1 A2 B0 m0
           s1 s2 t0[e1 e2 e3]/pi1_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=dyn_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    have[A0 rd1 rd2]:=church_rosser eq1.
    have tyA0t:=sta_prd H4 rd1.
    have tyA0s:=sta_prd H3 rd2.
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
  Θ ; Γ ; Δ ⊢ Lam1 A2 m s2 : Pi1 A1 B s1 -> exists r, Θ ; (A1 :: Γ) ; A1 .{r} Δ ⊢ m : B.
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

Lemma dyn_return_invX Θ Γ Δ m B :
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

Lemma dyn_return_inv Θ Γ Δ m A :
  Θ ; Γ ; Δ ⊢ Return m : IO A -> Θ ; Γ ; Δ ⊢ m : A.
Proof with eauto.
  move=>ty.
  have[B[tym/io_inj eq]]:=dyn_return_invX ty.
  have[s tyIO]:=dyn_valid ty.
  have[r[tyA/sort_inj e]]:=sta_io_inv tyIO. subst.
  apply: dyn_conv.
  apply: conv_sym...
  apply: tym.
  apply: tyA.
Qed.

Lemma dyn_bind_invX Θ Γ Δ m n C :
  Θ ; Γ ; Δ ⊢ Bind m n : C ->
  exists Θ1 Θ2 Δ1 Δ2 A B s t,
    Θ1 ∘ Θ2 => Θ /\
    Δ1 ∘ Δ2 => Δ /\
    Γ ⊢ B : Sort t /\
    Θ1 ; Γ ; Δ1 ⊢ m : IO A /\
    Θ2 ; (A :: Γ) ; (A .{s} Δ2) ⊢ n : IO B.[ren (+1)] /\
    C === IO B.                    
Proof with eauto.
  move e:(Bind m n)=>x ty. elim: ty m n e=>//{Θ Γ Δ x C}.
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB
           tym _ tyn _ m0 n0[e1 e2]. subst.
    exists Θ1. exists Θ2. exists Δ1. exists Δ2. exists A. exists B. exists s. exists t.
    repeat split... }
  { move=>Θ Γ Δ A B m s eq tym ihm tyB m0 n e. subst.
    have[Θ1[Θ2[Δ1[Δ2[A0[B0[s0[t[mrg1[mrg2[tyB0[tym0[tyn eq']]]]]]]]]]]]]:=
      ihm _ _ erefl.
    exists Θ1. exists Θ2. exists Δ1. exists Δ2. exists A0. exists B0. exists s0. exists t.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq'. }
Qed.

Lemma dyn_bind_inv Θ Γ Δ m n B :
  Θ ; Γ ; Δ ⊢ Bind m n : IO B ->
  exists Θ1 Θ2 Δ1 Δ2 A s,
    Θ1 ∘ Θ2 => Θ /\
    Δ1 ∘ Δ2 => Δ /\
    Θ1 ; Γ ; Δ1 ⊢ m : IO A /\
    Θ2 ; (A :: Γ) ; (A .{s} Δ2) ⊢ n : IO B.[ren (+1)].
Proof with eauto.
  move=>ty.
  have[Θ1[Θ2[Δ1[Δ2[A0[B0[s[t[mrg1[mrg2[tyB0[tym[tyn/io_inj eq]]]]]]]]]]]]]:=
    dyn_bind_invX ty.
  have[s0 tyIO]:=dyn_valid ty.
  have wf:=dyn_type_wf tyn. inv wf.
  have/={}tyIO:=sta_weaken tyIO H4.
  exists Θ1. exists Θ2. exists Δ1. exists Δ2. exists A0. exists s.
  repeat split...
  apply: dyn_conv.
  apply: sta_conv_io.
  apply: sta_conv_subst.
  apply: conv_sym...
  apply: tyn.
  apply: tyIO.
Qed.

Lemma dyn_cvar_inv Θ Γ Δ x B :
  Θ ; Γ ; Δ ⊢ CVar x : B ->
  exists r A,
    dyn_just Θ x (Ch r A) /\
    nil ⊢ A : Proto /\
    B === Ch r A.[ren (+size Γ)].
Proof with eauto.
  move e:(CVar x)=>m ty. elim: ty x e=>//{Θ Γ Δ m B}.
  { move=>Θ Γ Δ r x A js _ _ tyA x0[e]. subst.
    exists r. exists A... }
  { move=>Θ Γ Δ A B m s eq1 tym ihm tyB x e. subst.
    have[r[A0[js[tyA0 eq2]]]]:=ihm _ erefl.
    exists r. exists A0.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    apply: eq2. }
Qed.

Lemma dyn_fork_inv Θ Γ Δ A m B :
  Θ ; Γ ; Δ ⊢ Fork A m : B ->
  Θ ; (Ch true A :: Γ) ; Ch true A :L Δ ⊢ m : IO Unit /\
  B === IO (Ch false A).
Proof with eauto.
  move e:(Fork A m)=>x ty. elim: ty A m e=>//{Θ Γ Δ x B}.
  { move=>Θ Γ Δ m A tym ihm A0 m0[e1 e2]. subst... }
  { move=>Θ Γ Δ A B m s eq1 tym ihm tyB A0 m0 e. subst.
    have[tym0 eq2]:=ihm _ _ erefl.
    split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma dyn_recv0_inv Θ Γ Δ m C :
  Θ ; Γ ; Δ ⊢ Recv0 m : C ->
  exists r1 r2 A B,
    r1 (+) r2 = false /\
    C === IO (Sig0 A (Ch r1 B) L) /\
    Θ ; Γ ; Δ ⊢ m : Ch r1 (Act0 r2 A B).
Proof with eauto.
  move e:(Recv0 m)=>n ty. elim: ty m e=>//{Θ Γ Δ n C}.
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0[e]. subst.
    exists r1. exists r2. exists A. exists B... }
  { move=>Θ Γ Δ A B m s eq1 tym ihm tyB m0 e. subst.
    have[r1[r2[A0[B0[xor[eq2 tym0]]]]]]:=ihm _ erefl.
    exists r1. exists r2. exists A0. exists B0.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    apply: eq2. }
Qed.

Lemma dyn_recv1_inv Θ Γ Δ m C :
  Θ ; Γ ; Δ ⊢ Recv1 m : C ->
  exists r1 r2 A B,
    r1 (+) r2 = false /\
    C === IO (Sig1 A (Ch r1 B) L) /\
    Θ ; Γ ; Δ ⊢ m : Ch r1 (Act1 r2 A B).
Proof with eauto.
  move e:(Recv1 m)=>n ty. elim: ty m e=>//{Θ Γ Δ n C}.
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0[e]. subst.
    exists r1. exists r2. exists A. exists B... }
  { move=>Θ Γ Δ A B m s eq1 tym ihm tyB m0 e. subst.
    have[r1[r2[A0[B0[xor[eq2 tym0]]]]]]:=ihm _ erefl.
    exists r1. exists r2. exists A0. exists B0.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    apply: eq2. }
Qed.

Lemma dyn_send0_inv Θ Γ Δ m C :
  Θ ; Γ ; Δ ⊢ Send0 m : C ->
  exists r1 r2 A B,
    r1 (+) r2 = true /\
    C === Pi0 A (IO (Ch r1 B)) L /\
    Θ ; Γ ; Δ ⊢ m : Ch r1 (Act0 r2 A B).
Proof with eauto.
  move e:(Send0 m)=>n ty. elim: ty m e=>//{Θ Γ Δ n C}.
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0[e]. subst.
    exists r1. exists r2. exists A. exists B.
    repeat split... }
  { move=>Θ Γ Δ A B m s eq1 tym ihm tyB m0 e. subst.
    have[r1[r2[A0[B0[xor[eq2 tym0]]]]]]:=ihm _ erefl.
    exists r1. exists r2. exists A0. exists B0.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    apply: eq2. }
Qed.
  
Lemma dyn_send1_inv Θ Γ Δ m C :
  Θ ; Γ ; Δ ⊢ Send1 m : C ->
  exists r1 r2 A B,
    r1 (+) r2 = true /\
    C === Pi1 A (IO (Ch r1 B)) L /\
    Θ ; Γ ; Δ ⊢ m : Ch r1 (Act1 r2 A B).
Proof with eauto.
  move e:(Send1 m)=>n ty. elim: ty m e=>//{Θ Γ Δ n C}.
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0[e]. subst.
    exists r1. exists r2. exists A. exists B.
    repeat split... }
  { move=>Θ Γ Δ A B m s eq1 tym ihm tyB m0 e. subst.
    have[r1[r2[A0[B0[xor[eq2 tym0]]]]]]:=ihm _ erefl.
    exists r1. exists r2. exists A0. exists B0.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    apply: eq2. }
Qed.

Lemma dyn_wait_inv Θ Γ Δ m C :
  Θ ; Γ ; Δ ⊢ Wait m : C ->
  exists r1 r2,
    r1 (+) r2 = false /\
    C === IO Unit /\
    Θ ; Γ ; Δ ⊢ m : Ch r1 (Stop r2).
 Proof with eauto. 
   move e:(Wait m)=>x ty. elim: ty m e=>//{Θ Γ Δ x C}.
   { move=>Θ Γ Δ r1 r2 m xor tym ihm m0[e]. subst.
     exists r1. exists r2. repeat split... }
   { move=>Θ Γ Δ A B m s eq1 tym ihm tyB m0 e. subst.
     have[r1[r2[xor[eq2 tym0]]]]:=ihm _ erefl.
     exists r1. exists r2.
     repeat split...
     apply: conv_trans.
     apply: conv_sym...
     apply: eq2. }
 Qed.

Lemma dyn_close_inv Θ Γ Δ m C :
  Θ ; Γ ; Δ ⊢ Close m : C ->
  exists r1 r2,
    r1 (+) r2 = true /\
    C === IO Unit /\
    Θ ; Γ ; Δ ⊢ m : Ch r1 (Stop r2).
 Proof with eauto. 
   move e:(Close m)=>x ty. elim: ty m e=>//{Θ Γ Δ x C}.
   { move=>Θ Γ Δ r1 r2 m xor tym ihm m0[e]. subst.
     exists r1. exists r2. repeat split... }
   { move=>Θ Γ Δ A B m s eq1 tym ihm tyB m0 e. subst.
     have[r1[r2[xor[eq2 tym0]]]]:=ihm _ erefl.
     exists r1. exists r2.
     repeat split...
     apply: conv_trans.
     apply: conv_sym...
     apply: eq2. }
 Qed.
