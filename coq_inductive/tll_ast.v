From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope sort_scope.
Delimit Scope sort_scope with srt.
Open Scope sort_scope.

Inductive sort : Type := U | L.
Bind Scope term_scope with sort.

Inductive relv : Type := R | N.
Bind Scope term_scope with relv.

Inductive sort_leq : sort -> sort -> Prop :=
| sort_leqU s :
  sort_leq U s
| sort_leqL :
  sort_leq L L.
Notation "s ⊑ t" := (sort_leq s t) (at level 30) : sort_scope.

Inductive term : Type :=
| Var  (x : var)
| Srt (s : sort)
| Pi   (A : term) (B : {bind term}) (s : sort) (r : relv)
| Lam  (A : term) (m : {bind term}) (s : sort) (r : relv)
| App  (m n : term) (r : relv)
| Ind  (A : term) (Cs : list term) (s : sort) (r : relv)
| Cons (i : nat) (I : term) (s : sort) (r : relv)
| Case (m Q : term) (Fs : list term) (r : relv)
| Fix  (A : term) (m : {bind term})
| Ptr  (l : nat).

#[global] Instance Ids_term : Ids term. derive. Defined.
#[global] Instance Rename_term : Rename term. derive. Defined.
#[global] Instance Subst_term : Subst term. derive. Defined.
#[global] Instance substLemmas_term : SubstLemmas term. derive. Qed.

Section term_ind_nested.
  Variable P : term -> Prop.
  Hypothesis ih_Var : forall x, P (Var x).
  Hypothesis ih_Srt : forall s, P (Srt s).
  Hypothesis ih_Pi : forall A B s r, P A -> P B -> P (Pi A B s r).
  Hypothesis ih_Lam : forall A m s r, P A -> P m -> P (Lam A m s r).
  Hypothesis ih_App : forall m n r, P m -> P n -> P (App m n r).
  Hypothesis ih_Ind : forall A Cs s r, P A -> {∀ C ∈ Cs, P C} -> P (Ind A Cs s r).
  Hypothesis ih_Cons : forall i I s r, P I -> P (Cons i I s r).
  Hypothesis ih_Case : forall m Q Fs r, P m -> P Q -> {∀ F ∈ Fs, P F} -> P (Case m Q Fs r).
  Hypothesis ih_Fix : forall A m, P A -> P m -> P (Fix A m).
  Hypothesis ih_Ptr : forall l, P (Ptr l).

  Fixpoint term_ind_nested m : P m. 
  Proof with eauto.
    have ih_nested :=
      fix fold xs : {∀ x ∈ xs, P x} :=
        match xs with
        | nil => Forall1_nil _
        | x :: xs => Forall1_cons (term_ind_nested x) (fold xs)
        end.
    case m; move=>*.
    apply: ih_Var.
    apply: ih_Srt.
    apply: ih_Pi...
    apply: ih_Lam...
    apply: ih_App...
    apply: ih_Ind...
    apply: ih_Cons...
    apply: ih_Case...
    apply: ih_Fix...
    apply: ih_Ptr...
  Qed.
End term_ind_nested.
