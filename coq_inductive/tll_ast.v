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
Bind Scope sort_scope with sort.

Inductive sort_leq : sort -> sort -> Prop :=
| sort_leqU s :
  sort_leq U s
| sort_leqL :
  sort_leq L L.
Notation "s ⊑ t" := (sort_leq s t) (at level 30) : sort_scope.

Inductive term : Type :=
| Var (x : var)
| Sort (s : sort)
| Pi0 (A : term) (B : {bind term}) (s : sort)
| Pi1 (A : term) (B : {bind term}) (s : sort)
| Lam0 (A : term) (m : {bind term}) (s : sort)
| Lam1 (A : term) (m : {bind term}) (s : sort)
| App0 (m n : term)
| App1 (m n : term)
| Ind0 (A : term) (Cs : list term) (s : sort)
| Ind1 (A : term) (Cs : list term) (s : sort)
| Constr0 (i : nat) (I : term) (s : sort)
| Constr1 (i : nat) (I : term) (s : sort)
| Case0 (m Q : term) (Fs : list term)
| Case1 (m Q : term) (Fs : list term)
| Fix (A : term) (m : {bind term})
| Ptr (l : nat).

#[global] Instance Ids_term : Ids term. derive. Defined.
#[global] Instance Rename_term : Rename term. derive. Defined.
#[global] Instance Subst_term : Subst term. derive. Defined.
#[global] Instance substLemmas_term : SubstLemmas term. derive. Qed.

Section term_ind_nested.
  Variable P : term -> Prop.
  Hypothesis ih_Var : forall x, P (Var x).
  Hypothesis ih_Sort : forall s, P (Sort s).
  Hypothesis ih_Pi0 : forall A B s, P A -> P B -> P (Pi0 A B s).
  Hypothesis ih_Pi1 : forall A B s, P A -> P B -> P (Pi1 A B s).
  Hypothesis ih_Lam0 : forall A m s, P A -> P m -> P (Lam0 A m s).
  Hypothesis ih_Lam1 : forall A m s, P A -> P m -> P (Lam1 A m s).
  Hypothesis ih_App0 : forall m n, P m -> P n -> P (App0 m n).
  Hypothesis ih_App1 : forall m n, P m -> P n -> P (App1 m n).
  Hypothesis ih_Ind0 : forall A Cs s, P A -> All1 P Cs -> P (Ind0 A Cs s).
  Hypothesis ih_Ind1 : forall A Cs s, P A -> All1 P Cs -> P (Ind1 A Cs s).
  Hypothesis ih_Constr0 : forall i I s, P I -> P (Constr0 i I s).
  Hypothesis ih_Constr1 : forall i I s, P I -> P (Constr1 i I s).
  Hypothesis ih_Case0 : forall m Q Fs, P m -> P Q -> All1 P Fs -> P (Case0 m Q Fs).
  Hypothesis ih_Case1 : forall m Q Fs, P m -> P Q -> All1 P Fs -> P (Case1 m Q Fs).
  Hypothesis ih_Fix : forall A m, P A -> P m -> P (Fix A m).
  Hypothesis ih_Ptr : forall l, P (Ptr l).

  Fixpoint term_ind_nested m : P m. 
  Proof with eauto.
    have ih_nested :=
      fix fold xs : All1 P xs :=
        match xs with
        | nil => All1_nil _
        | x :: xs => All1_cons (term_ind_nested x) (fold xs)
        end.
    case m; move=>*.
    apply: ih_Var.
    apply: ih_Sort.
    apply: ih_Pi0...
    apply: ih_Pi1...
    apply: ih_Lam0...
    apply: ih_Lam1...
    apply: ih_App0...
    apply: ih_App1...
    apply: ih_Ind0...
    apply: ih_Ind1...
    apply: ih_Constr0...
    apply: ih_Constr1...
    apply: ih_Case0...
    apply: ih_Case1...
    apply: ih_Fix...
    apply: ih_Ptr...
  Qed.
End term_ind_nested.
