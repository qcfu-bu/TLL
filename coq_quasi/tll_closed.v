From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive closed : nat -> term -> Prop :=
| closed_var i x :
  x < i ->
  closed i (Var x)
| closed_sort i s :
  closed i (Sort s)
| closed_pi0 i A B t :
  closed i A ->
  closed i.+1 B ->
  closed i (Pi0 A B t)
| closed_pi1 i A B t :
  closed i A ->
  closed i.+1 B ->
  closed i (Pi1 A B t)
| closed_lam0 i A m t :
  closed i A ->
  closed i.+1 m ->
  closed i (Lam0 A m t)
| closed_lam1 i A m t :
  closed i A ->
  closed i.+1 m ->
  closed i (Lam1 A m t)
| closed_app i m n :
  closed i m ->
  closed i n ->
  closed i (App m n)
| closed_sig0 i A B t :
  closed i A ->
  closed i.+1 B ->
  closed i (Sig0 A B t)
| closed_sig1 i A B t :
  closed i A ->
  closed i.+1 B ->
  closed i (Sig1 A B t)
| closed_pair0 i m n t :
  closed i m ->
  closed i n ->
  closed i (Pair0 m n t)
| closed_pair1 i m n t :
  closed i m ->
  closed i n ->
  closed i (Pair1 m n t)
| closed_letin i A m n :
  closed i.+1 A ->
  closed i m ->
  closed i.+2 n ->
  closed i (LetIn A m n)
| closed_with i A B t :
  closed i A ->
  closed i B ->
  closed i (With A B t)
| closed_apair i m n t :
  closed i m ->
  closed i n ->
  closed i (APair m n t)
| closed_fst i m :
  closed i m ->
  closed i (Fst m)
| closed_snd i m :
  closed i m ->
  closed i (Snd m)
| closed_id i A m n :
  closed i A ->
  closed i m ->
  closed i n ->
  closed i (Id A m n)
| closed_refl i m :
  closed i m ->
  closed i (Refl m)
| closed_rw i A H P :
  closed i.+2 A ->
  closed i H ->
  closed i P ->
  closed i (Rw A H P)
| closed_box i :
  closed i Box
| closed_ptr i l :
  closed i (Ptr l).

Definition iren i j (ξ : var -> var) :=
  (forall x, x < i -> ξ x < (j + i)) /\
  (forall x, i <= x -> ξ x = (j + x)).

Lemma iren0 i j : iren i j (+j).
Proof.
  constructor.
  move=>x lt. simpl. lia.
  by move=>x lte.
Qed.

Lemma iren_upren i j ξ : iren i j ξ -> iren i.+1 j (upren ξ).
Proof.
  move=>[h1 h2]. constructor.
  move=>[|x]lt; asimpl; eauto.
  move=>[|x]lt; asimpl. inv lt.
  rewrite h2; eauto.
Qed.

Lemma closed_iren i j m ξ : closed i m -> iren i j ξ -> closed (i + j) m.[ren ξ].
Proof with eauto using closed, iren_upren.
  move=>c. elim: c j ξ=>{i m}.
  all: try solve[intros; asimpl; eauto using closed, iren_upren].
  { move=>i x lt j ξ[h1 h2]. asimpl.
    constructor. have:=h1 _ lt. lia. }
  { move=>i A m n hA ihA hm ihm hn ihn j ξ h. asimpl.
    constructor...
    have:=ihn _ _ (iren_upren (iren_upren h)).
    by asimpl. }
  { move=>i A H P hA ihA hH ihH hP ihP j ξ h. asimpl.
    constructor...
    have:=ihA _ _ (iren_upren (iren_upren h)).
    by asimpl. }
Qed.

Definition isubst i σ := forall x, x < i -> σ x = Var x.

Lemma isubst0 σ : isubst 0 σ.
Proof. move=>x lt. lia. Qed.

Lemma isubst_up i σ : isubst i σ -> isubst i.+1 (up σ).
Proof with eauto.
  move=>h[|x]lt.
  by asimpl.
  asimpl. rewrite h...
Qed.

Lemma isubst_upn i n σ : isubst i σ -> isubst (n + i) (upn n σ).
Proof with eauto.
  elim: n i σ=>//=.
  move=>n ih i σ h x lt.
  have->: upn n.+1 σ = upn n (up σ) by asimpl.
  have->//:=ih _ _ (isubst_up h).
  lia.
Qed.

Lemma closed_isubst i m σ : closed i m -> isubst i σ -> m = m.[σ].
Proof with eauto using isubst_up, isubst_upn, f_equal.
  move=>h. elim: h σ=>//{i m}.
  all: try solve[intros; asimpl; f_equal;
                 eauto using isubst_up, isubst_upn].
  { move=>i x lt σ h. simpl. rewrite h... }
Qed.

Definition csubst i j σ := forall x, x < i + j -> closed i (σ x).

Lemma csubst1 i m : closed i m -> csubst i 1 (m .: ids).
Proof.
  move=>h[|x]//.
  move=> lt. asimpl. constructor. lia.
Qed.

Lemma csubst2 i m n : closed i m -> closed i n -> csubst i 2 (m .: n .: ids).
Proof.
  move=>h1 h2[|[|x]]//.
  move=>lt. asimpl. constructor. lia.
Qed.

Lemma csubst_up i j σ : csubst i j σ -> csubst i.+1 j (up σ).
Proof.
  move=>h[|x]lt; unfold csubst in h.
  asimpl. constructor. lia.
  asimpl.
  have/h{}h: x < i + j by lia.
  have:=closed_iren h (iren0 i 1).
  by rewrite addnC.
Qed.

Lemma closed_csubst i j m σ : closed (i + j) m ->  csubst i j σ -> closed i m.[σ].
Proof with eauto using closed, csubst_up.
  move e:(i + j)=>x c. elim: c i j e σ=>{m x}.
  all: try solve
         [intros; subst; asimpl; constructor;
          eauto using closed, csubst_up].
  { move=>i x lt i0 j e σ h. subst. asimpl. by apply: h. }
  { move=>i A B t hA ihA hB ihB i0 j e σ h. subst. asimpl.
    constructor... apply: ihB _ _ _ _ (csubst_up h). lia. }
  { move=>i A B t hA ihA hB ihB i0 j e σ h. subst. asimpl.
    constructor... apply: ihB _ _ _ _ (csubst_up h). lia. }
  { move=>i A m t hA ihA hm ihm i0 j e σ h. subst. asimpl.
    constructor... apply: ihm _ _ _ _ (csubst_up h). lia. }
  { move=>i A m t hA ihA hm ihm i0 j e σ h. subst. asimpl.
    constructor... apply: ihm _ _ _ _ (csubst_up h). lia. }
  { move=>i A B t hA ihA hB ihB i0 j e σ h. subst. asimpl.
    constructor... apply: ihB _ _ _ _ (csubst_up h). lia. }
  { move=>i A B t hA ihA hB ihB i0 j e σ h. subst. asimpl.
    constructor... apply: ihB _ _ _ _ (csubst_up h). lia. }
  { move=>i A m n hA ihA hm ihm hn ihn i0 j e σ h. subst. asimpl.
    constructor...
    apply: ihA _ _ _ _ (csubst_up h). lia.
    apply: ihn _ _ _ _ (csubst_up (csubst_up h)). lia. }
  { move=>i A H P hA ihA hH ihH hP ihP i0 j e σ h. subst. asimpl.
    constructor... apply: ihA _ _ _ _ (csubst_up (csubst_up h)). lia. }
Qed.

Lemma closed_subst1 i m n :
  closed i.+1 m -> closed i n -> closed i m.[n/].
Proof with eauto using csubst1.
  move=>h1 h2.
  have e: i.+1 = i + 1 by lia.
  rewrite e in h1.
  apply: closed_csubst...
Qed.

Lemma closed_subst2 i m n1 n2 :
  closed i.+2 m -> closed i n1 -> closed i n2 -> closed i m.[n1,n2/].
Proof with eauto using csubst2.
  move=>h1 h2 h3.
  have e: i.+2 = i + 2 by lia.
  rewrite e in h1.
  apply: closed_csubst...
Qed.
