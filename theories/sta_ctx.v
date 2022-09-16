From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition sta_ctx T := seq T.

Inductive sta_has {T} `{Ids T} `{Subst T} :
  sta_ctx T -> var -> T -> Prop :=
| sta_has_O Γ A :
  sta_has (A :: Γ) 0 A.[ren (+1)]
| sta_has_S Γ A B x :
  sta_has Γ x A ->
  sta_has (B :: Γ) x.+1 A.[ren (+1)].

