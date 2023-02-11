From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  sta_cren sta_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma decide_act X ξ :
  ((forall r A B, ~term_cren X ξ = Act0 r A B) /\
   (forall r A B, ~term_cren X ξ = Act1 r A B)) \/
  (exists r A B, X = Act0 r A B) \/
  (exists r A B, X = Act1 r A B).
Proof with eauto.
  destruct X.
  all: try solve[
           left; split; intros; intro;
           match goal with
           | [ H : term_cren (_) _ = _ |- _ ] => inv H
           end].
  right. left. exists r. exists X. exists B...
  right. right. exists r. exists X. exists B...
Qed.

Ltac destruct_ren :=
  repeat match goal with
  | [ H : term_cren (?X) _ = _ |- _ ] =>
    destruct X; inv H
  end.

Definition can_cancel (f : var -> var) :=
  exists g, f >>> g = id.

Lemma can_cancel_up f :
  can_cancel f -> can_cancel (upren f).
Proof.
  move=>[g h].
  exists (upren g).
  asimpl.
  rewrite h.
  by asimpl.
Qed.

Lemma can_cancel1 : can_cancel (+1).
Proof. exists (-1). f_ext. move=>[|x]; asimpl=>//. Qed.

Lemma can_cancel2 : can_cancel (+2).
Proof. exists (-2). f_ext. move=>[|x]; asimpl=>//. Qed.

Lemma sta_step_cren_cancel X Y ξ :
  term_cren X ξ ~> term_cren Y ξ -> can_cancel ξ -> X ~> Y.
Proof.
  move=>st [g h].
  have st':=term_cren_sta_step g st.
  rewrite<-!term_cren_comp in st'.
  rewrite h in st'.
  by rewrite!term_cren_id in st'.
Qed.

Lemma sta_red_cren_cancel X Y ξ :
  term_cren X ξ ~>* term_cren Y ξ -> can_cancel ξ -> X ~>* Y.
Proof.
  move=>rd [g h].
  have rd':=term_cren_sta_red g rd.
  rewrite<-!term_cren_comp in rd'.
  rewrite h in rd'.
  by rewrite!term_cren_id in rd'.
Qed.

Lemma sta_step_cren_inv X Y ξ :
  term_cren X ξ ~> Y ->
  (exists Z, Y = term_cren Z ξ /\
          ((forall r A B, ~Y = Act0 r A B) /\ (forall r A B, ~Y = Act1 r A B))) \/
  (exists r A B, Y = term_cren (Act0 r A B) ξ) \/
  (exists r A B, Y = term_cren (Act1 r A B) ξ).
Proof with eauto.
  elim: X Y ξ.
  all: try solve[
           intros;
           match goal with
           | [ H : _ ~> _ |- _ ] => inv H
           end].
  { move=>A ihA B ihB s Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Pi0 z B s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pi0 (Act0 r A0 B0) B s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pi0 (Act1 r A0 B0) B s). } }
    { have[|[|]]:=ihB _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Pi0 A z s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pi0 A (Act0 r A0 B0) s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pi0 A (Act1 r A0 B0) s). } } }
  { move=>A ihA B ihB s Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Pi1 z B s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pi1 (Act0 r A0 B0) B s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pi1 (Act1 r A0 B0) B s). } }
    { have[|[|]]:=ihB _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Pi1 A z s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pi1 A (Act0 r A0 B0) s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pi1 A (Act1 r A0 B0) s). } } }
  { move=>A ihA m ihm s Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Lam0 z m s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Lam0 (Act0 r A0 B0) m s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Lam0 (Act1 r A0 B0) m s). } }
    { have[|[|]]:=ihm _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Lam0 A z s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Lam0 A (Act0 r A0 B0) s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Lam0 A (Act1 r A0 B0) s). } } }
  { move=>A ihA m ihm s Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Lam1 z m s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Lam1 (Act0 r A0 B0) m s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Lam1 (Act1 r A0 B0) m s). } }
    { have[|[|]]:=ihm _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Lam1 A z s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Lam1 A (Act0 r A0 B0) s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Lam1 A (Act1 r A0 B0) s). } } }
  { move=>m ihm n ihn Y ξ st. inv st.
    { have[|[|]]:=ihm _ _ H2.
      { move=>[z[e _]]. subst. left. by exists (App z n). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (App (Act0 r A0 B0) n). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (App (Act1 r A0 B0) n). } }
    { have[|[|]]:=ihn _ _ H2.
      { move=>[z[e _]]. subst. left. by exists (App m z). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (App m (Act0 r A0 B0)). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (App m (Act1 r A0 B0)). } }
    { destruct m; inv H0. rewrite<-term_cren_beta1.
      have[|[|]]:=decide_act m1.[n/] ξ.
      { move=>[h1 h2]. left. by exists m1.[n/]. }
      { move=>[r[A[B e]]]. right. left. exists r. exists A. exists B. by rewrite e. }
      { move=>[r[A[B e]]]. right. right. exists r. exists A. exists B. by rewrite e. } }
    { destruct m; inv H0. rewrite<-term_cren_beta1.
      have[|[|]]:=decide_act m1.[n/] ξ.
      { move=>[h1 h2]. left. by exists m1.[n/]. }
      { move=>[r[A[B e]]]. right. left. exists r. exists A. exists B. by rewrite e. }
      { move=>[r[A[B e]]]. right. right. exists r. exists A. exists B. by rewrite e. } } }
  { move=>A ihA B ihB s Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Sig0 z B s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Sig0 (Act0 r A0 B0) B s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Sig0 (Act1 r A0 B0) B s). } }
    { have[|[|]]:=ihB _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Sig0 A z s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Sig0 A (Act0 r A0 B0) s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Sig0 A (Act1 r A0 B0) s). } } }
  { move=>A ihA B ihB s Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Sig1 z B s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Sig1 (Act0 r A0 B0) B s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Sig1 (Act1 r A0 B0) B s). } }
    { have[|[|]]:=ihB _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Sig1 A z s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Sig1 A (Act0 r A0 B0) s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Sig1 A (Act1 r A0 B0) s). } } }
  { move=>m ihm n ihn s Y ξ st. inv st.
    { have[|[|]]:=ihm _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Pair0 z n s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pair0 (Act0 r A0 B0) n s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pair0 (Act1 r A0 B0) n s). } }
    { have[|[|]]:=ihn _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Pair0 m z s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pair0 m (Act0 r A0 B0) s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pair0 m (Act1 r A0 B0) s). } } }
  { move=>m ihm n ihn s Y ξ st. inv st.
    { have[|[|]]:=ihm _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Pair1 z n s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pair1 (Act0 r A0 B0) n s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pair1 (Act1 r A0 B0) n s). } }
    { have[|[|]]:=ihn _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (Pair1 m z s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pair1 m (Act0 r A0 B0) s). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Pair1 m (Act1 r A0 B0) s). } } }
  { move=>A ihA m ihm n ihn Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (LetIn z m n). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (LetIn (Act0 r A0 B0) m n). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (LetIn (Act1 r A0 B0) m n). } }
    { have[|[|]]:=ihm _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (LetIn A z n). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (LetIn A (Act0 r A0 B0) n). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (LetIn A (Act1 r A0 B0) n). } }
    { have[|[|]]:=ihn _ _ H3.
      { move=>[z[e _]]. subst. left. by exists (LetIn A m z). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (LetIn A m (Act0 r A0 B0)). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (LetIn A m (Act1 r A0 B0)). } }
    { destruct m; inv H1. rewrite<-term_cren_beta2.
      have[|[|]]:=decide_act n.[m4,m3/] ξ.
      { move=>[h1 h2]. left. by exists n.[m4,m3/]. }
      { move=>[r[A0[B0 e]]]. right. left. exists r. exists A0. exists B0. by rewrite e. }
      { move=>[r[A0[B0 e]]]. right. right. exists r. exists A0. exists B0. by rewrite e. } }
    { destruct m; inv H1. rewrite<-term_cren_beta2.
      have[|[|]]:=decide_act n.[m4,m3/] ξ.
      { move=>[h1 h2]. left. by exists n.[m4,m3/]. }
      { move=>[r[A0[B0 e]]]. right. left. exists r. exists A0. exists B0. by rewrite e. }
      { move=>[r[A0[B0 e]]]. right. right. exists r. exists A0. exists B0. by rewrite e. } } }
  { move=>A ihA m ihm Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H2.
      { move=>[z[e _]]. subst. left. by exists (Fix z m). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Fix (Act0 r A0 B0) m). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Fix (Act1 r A0 B0) m). } }
    { have[|[|]]:=ihm _ _ H2.
      { move=>[z[e _]]. subst. left. by exists (Fix A z). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Fix A (Act0 r A0 B0)). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Fix A (Act1 r A0 B0)). } }
    { replace (Fix (term_cren A ξ) (term_cren m ξ))
        with (term_cren (Fix A m) ξ) by autosubst.
      rewrite<-term_cren_beta1.
      have[|[|]]:=decide_act m.[Fix A m/] ξ.
      { move=>[h1 h2]. left. by exists m.[Fix A m/]. }
      { move=>[r[A0[B0 e]]]. right. left. exists r. exists A0. exists B0. by rewrite e. }
      { move=>[r[A0[B0 e]]]. right. right. exists r. exists A0. exists B0. by rewrite e. } } }
  { move=>A ihA m ihm n1 ihn1 n2 ihn2 Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H4.
      { move=>[z[e _]]. subst. left. by exists (Ifte z m n1 n2). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Ifte (Act0 r A0 B0) m n1 n2). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Ifte (Act1 r A0 B0) m n1 n2). } }
    { have[|[|]]:=ihm _ _ H4.
      { move=>[z[e _]]. subst. left. by exists (Ifte A z n1 n2). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Ifte A (Act0 r A0 B0) n1 n2). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Ifte A (Act1 r A0 B0) n1 n2). } }
    { have[|[|]]:=ihn1 _ _ H4.
      { move=>[z[e _]]. subst. left. by exists (Ifte A m z n2). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Ifte A m (Act0 r A0 B0) n2). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Ifte A m (Act1 r A0 B0) n2). } }
    { have[|[|]]:=ihn2 _ _ H4.
      { move=>[z[e _]]. subst. left. by exists (Ifte A m n1 z). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Ifte A m n1 (Act0 r A0 B0)). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Ifte A m n1 (Act1 r A0 B0)). } }
    { destruct m; inv H1.
      have[|[|]]:=decide_act n1 ξ.
      { move=>[h1 h2]. left. by exists n1. }
      { move=>[r[A0[B0 e]]]. right. left. exists r. exists A0. exists B0. by rewrite e. }
      { move=>[r[A0[B0 e]]]. right. right. exists r. exists A0. exists B0. by rewrite e. } }
    { destruct m; inv H1.
      have[|[|]]:=decide_act n2 ξ.
      { move=>[h1 h2]. left. by exists n2. }
      { move=>[r[A0[B0 e]]]. right. left. exists r. exists A0. exists B0. by rewrite e. }
      { move=>[r[A0[B0 e]]]. right. right. exists r. exists A0. exists B0. by rewrite e. } } }
  { move=>A ihA Y ξ st. inv st.
    have[|[|]]:=ihA _ _ H0.
    { move=>[z[e _]]. subst. left. by exists (IO z). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (IO (Act0 r A0 B0)). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (IO (Act1 r A0 B0)). } }
  { move=>m ihm Y ξ st. inv st.
    have[|[|]]:=ihm _ _ H0.
    { move=>[z[e _]]. subst. left. by exists (Return z). }
    { move=>[r[A[B e]]]. subst. left. by exists (Return (Act0 r A B)). }
    { move=>[r[A[B e]]]. subst. left. by exists (Return (Act1 r A B)). } }
  { move=>m ihm n ihn Y ξ st. inv st.
    { have[|[|]]:=ihm _ _ H2.
      { move=>[z[e _]]. subst. left. by exists (Bind z n). }
      { move=>[r[A[B e]]]. subst. left. by exists (Bind (Act0 r A B) n). }
      { move=>[r[A[B e]]]. subst. left. by exists (Bind (Act1 r A B) n). } }
    { have[|[|]]:=ihn _ _ H2.
      { move=>[z[e _]]. subst. left. by exists (Bind m z). }
      { move=>[r[A[B e]]]. subst. left. by exists (Bind m (Act0 r A B)). }
      { move=>[r[A[B e]]]. subst. left. by exists (Bind m (Act1 r A B)). } }
    { destruct m; inv H0. rewrite<-term_cren_beta1.
      have[|[|]]:=decide_act n.[m/] ξ.
      { move=>[h1 h2]. left. by exists n.[m/]. }
      { move=>[r[A[B e]]]. right. left. exists r. exists A. exists B. by rewrite e. }
      { move=>[r[A[B e]]]. right. right. exists r. exists A. exists B. by rewrite e. } } }
  { move=>r A ihA B ihB Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H3.
      { move=>[z[e _]]. subst. right. left. exists r. exists z. by exists B. }
      { move=>[r0[A0[B0 e]]]. subst. right. left.
        exists r. exists (Act0 r0 A0 B0). by exists B. }
      { move=>[r0[A0[B0 e]]]. subst. right. left.
        exists r. exists (Act1 r0 A0 B0). by exists B. } }
    { have[|[|]]:=ihB _ _ H3.
      { move=>[z[e _]]. subst. right. left. exists r. exists A. by exists z. }
      { move=>[r0[A0[B0 e]]]. subst. right. left.
        exists r. exists A. by exists (Act0 r0 A0 B0). }
      { move=>[r0[A0[B0 e]]]. subst. right. left.
        exists r. exists A. by exists (Act1 r0 A0 B0). } } }
  { move=>r A ihA B ihB Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H3.
      { move=>[z[e _]]. subst. right. right. exists r. exists z. by exists B. }
      { move=>[r0[A0[B0 e]]]. subst. right. right.
        exists r. exists (Act0 r0 A0 B0). by exists B. }
      { move=>[r0[A0[B0 e]]]. subst. right. right.
        exists r. exists (Act1 r0 A0 B0). by exists B. } }
    { have[|[|]]:=ihB _ _ H3.
      { move=>[z[e _]]. subst. right. right. exists r. exists A. by exists z. }
      { move=>[r0[A0[B0 e]]]. subst. right. right.
        exists r. exists A. by exists (Act0 r0 A0 B0). }
      { move=>[r0[A0[B0 e]]]. subst. right. right.
        exists r. exists A. by exists (Act1 r0 A0 B0). } } }
  { move=>r A ihA Y ξ st. inv st.
    have[|[|]]:=ihA _ _ H2.
    { move=>[z[e _]]. subst. left. by exists (Ch r z). }
    { move=>[r0[A0[B0 e]]]. subst. left. by exists (Ch r (Act0 r0 A0 B0)). }
    { move=>[r0[A0[B0 e]]]. subst. left. by exists (Ch r (Act1 r0 A0 B0)). } }
  { move=>A ihA m ihm Y ξ st. inv st.
    { have[|[|]]:=ihA _ _ H2.
      { move=>[z[e _]]. subst. left. by exists (Fork z m). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Fork (Act0 r A0 B0) m). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Fork (Act1 r A0 B0) m). } }
    { have[|[|]]:=ihm _ _ H2.
      { move=>[z[e _]]. subst. left. by exists (Fork A z). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Fork A (Act0 r A0 B0)). }
      { move=>[r[A0[B0 e]]]. subst. left. by exists (Fork A (Act1 r A0 B0)). } } }
  { move=>m ihm Y ξ st. inv st.
    have[|[|]]:=ihm _ _ H0.
    { move=>[z[e _]]. subst. left. by exists (Recv0 z). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Recv0 (Act0 r A0 B0)). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Recv0 (Act1 r A0 B0)). } }
  { move=>m ihm Y ξ st. inv st.
    have[|[|]]:=ihm _ _ H0.
    { move=>[z[e _]]. subst. left. by exists (Recv1 z). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Recv1 (Act0 r A0 B0)). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Recv1 (Act1 r A0 B0)). } }
  { move=>m ihm Y ξ st. inv st.
    have[|[|]]:=ihm _ _ H0.
    { move=>[z[e _]]. subst. left. by exists (Send0 z). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Send0 (Act0 r A0 B0)). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Send0 (Act1 r A0 B0)). } }
  { move=>m ihm Y ξ st. inv st.
    have[|[|]]:=ihm _ _ H0.
    { move=>[z[e _]]. subst. left. by exists (Send1 z). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Send1 (Act0 r A0 B0)). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Send1 (Act1 r A0 B0)). } }
  { move=>m ihm Y ξ st. inv st.
    have[|[|]]:=ihm _ _ H0.
    { move=>[z[e _]]. subst. left. by exists (Close z). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Close (Act0 r A0 B0)). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Close (Act1 r A0 B0)). } }
  { move=>m ihm Y ξ st. inv st.
    have[|[|]]:=ihm _ _ H0.
    { move=>[z[e _]]. subst. left. by exists (Wait z). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Wait (Act0 r A0 B0)). }
    { move=>[r[A0[B0 e]]]. subst. left. by exists (Wait (Act1 r A0 B0)). } }
Qed.

Lemma sta_red_cren_inv X Y ξ :
  term_cren X ξ ~>* Y ->
  (exists Z, Y = term_cren Z ξ /\
          ((forall r A B, ~Y = Act0 r A B) /\ (forall r A B, ~Y = Act1 r A B))) \/
  (exists r A B, Y = term_cren (Act0 r A B) ξ) \/
  (exists r A B, Y = term_cren (Act1 r A B) ξ).
Proof with eauto.
  move e:(term_cren X ξ)=>n rd.
  elim: rd e.
  { move=>e; subst.
    destruct X.
    all: try solve[match goal with
                   | [ |- (exists _, term_cren ?n _ = _ /\ _ ) \/ _ ] =>
                       left; exists n;
                       repeat split; eauto;
                       intros; asimpl=>H; inv H
                   end].
    { right. left. exists r. exists X. by exists B. }
    { right. right. exists r. exists X. by exists B. } }
  { move=>y z rd ih st e. subst.
    have[|[|]]:=ih erefl.
    { move=>[z1[e[h1 h2]]]. subst.
      have[|[|]]:=sta_step_cren_inv st.
      { move=>[z2[e[h3 h4]]]. subst. left. by exists z2. }
      { move=>[r[A[B e]]]. subst. right. left. exists r. exists A. by exists B. }
      { move=>[r[A[B e]]]. subst. right. right. exists r. exists A. by exists B. } }
    { move=>[r[A[B e]]]. subst. simpl in st. inv st.
      { have[|[|]]:=sta_step_cren_inv H3.
        { move=>[z2[e[h3 h4]]]. subst. right. left.
          exists r. exists z2. by exists B. }
        { move=>[r0[A0[B0 e]]]. subst. right. left.
          exists r. exists (Act0 r0 A0 B0). by exists B. }
        { move=>[r0[A0[B0 e]]]. subst. right. left.
          exists r. exists (Act1 r0 A0 B0). by exists B. } }
      { have[|[|]]:=sta_step_cren_inv H3.
        { move=>[z2[e[h3 h4]]]. subst. right. left.
          exists r. exists A. by exists z2. }
        { move=>[r0[A0[B0 e]]]. subst. right. left.
          exists r. exists A. by exists (Act0 r0 A0 B0). }
        { move=>[r0[A0[B0 e]]]. subst. right. left.
          exists r. exists A. by exists (Act1 r0 A0 B0). } } }
    { move=>[r[A[B e]]]. subst. simpl in st. inv st.
      { have[|[|]]:=sta_step_cren_inv H3.
        { move=>[z2[e[h3 h4]]]. subst. right. right.
          exists r. exists z2. by exists B. }
        { move=>[r0[A0[B0 e]]]. subst. right. right.
          exists r. exists (Act0 r0 A0 B0). by exists B. }
        { move=>[r0[A0[B0 e]]]. subst. right. right.
          exists r. exists (Act1 r0 A0 B0). by exists B. } }
      { have[|[|]]:=sta_step_cren_inv H3.
        { move=>[z2[e[h3 h4]]]. subst. right. right.
          exists r. exists A. by exists z2. }
        { move=>[r0[A0[B0 e]]]. subst. right. right.
          exists r. exists A. by exists (Act0 r0 A0 B0). }
        { move=>[r0[A0[B0 e]]]. subst. right. right.
          exists r. exists A. by exists (Act1 r0 A0 B0). } } } }
Qed.

Lemma sta_conv_act0_inv Γ X r A B C ξ :
  term_cren X ξ === Act0 r A B ->
  Γ ⊢ X : C ->
  can_cancel ξ ->
  exists A' B',
    Γ ⊢ Act0 r A' B' : C /\
    term_cren (Act0 r A' B') ξ === term_cren X ξ /\
    term_cren (Act0 r A' B') ξ === Act0 r A B.
Proof with eauto.
  move=>/church_rosser[x rd1 rd2]tyX cc.
  have[A'[B'[rA[rB e]]]]:=sta_red_act0_inv rd2. subst.
  have[|[|]]:=sta_red_cren_inv rd1.
  { move=>[z[e[h1 h2]]]. exfalso. apply: h1... }
  { move=>[r0[A0[B0 e]]]. inv e.
    replace (Act0 r0 (term_cren A0 ξ) (term_cren B0 ξ))
      with (term_cren (Act0 r0 A0 B0) ξ) in rd1 by eauto.
    have rd:=sta_red_cren_cancel rd1 cc.
    exists A0. exists B0.
    repeat split...
    apply: sta_rd...
    apply: conv_sym.
    apply: star_conv...
    apply: conv_sym.
    apply: star_conv... }
  { move=>[r0[A0[B0 e]]]. inv e. }
Qed.

Lemma sta_conv_act1_inv Γ X r A B C ξ :
  term_cren X ξ === Act1 r A B ->
  Γ ⊢ X : C ->
  can_cancel ξ ->
  exists A' B',
    Γ ⊢ Act1 r A' B' : C /\
    term_cren (Act1 r A' B') ξ === term_cren X ξ /\
    term_cren (Act1 r A' B') ξ === Act1 r A B.
Proof with eauto.
  move=>/church_rosser[x rd1 rd2]tyX cc.
  have[A'[B'[rA[rB e]]]]:=sta_red_act1_inv rd2. subst.
  have[|[|]]:=sta_red_cren_inv rd1.
  { move=>[z[e[h1 h2]]]. exfalso. apply: h2... }
  { move=>[r0[A0[B0 e]]]. inv e. }
  { move=>[r0[A0[B0 e]]]. inv e.
    replace (Act1 r0 (term_cren A0 ξ) (term_cren B0 ξ))
      with (term_cren (Act1 r0 A0 B0) ξ) in rd1 by eauto.
    have rd:=sta_red_cren_cancel rd1 cc.
    exists A0. exists B0.
    repeat split...
    apply: sta_rd...
    apply: conv_sym.
    apply: star_conv...
    apply: conv_sym.
    apply: star_conv... }
Qed.
