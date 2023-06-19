From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint mkApps (h : term) (ls : list (term * relv)%type) : term :=
  match ls with
  | nil => h
  | (m, r) :: ls => mkApps (App h m r) ls
  end.

Reserved Notation "m ~> n" (at level 50).
Inductive sta_step : term -> term -> Prop :=
| sta_step_piL A A' B s r :
  A ~> A' ->
  Pi A B s r ~> Pi A' B s r

| sta_step_piR A B B' s r :
  B ~> B' ->
  Pi A B s r ~> Pi A B' s r

| sta_step_lamL A A' m s r :
  A ~> A' ->
  Lam A m s r ~> Lam A' m s r

| sta_step_lamR A m m' s r :
  m ~> m' ->
  Lam A m s r ~> Lam A m' s r

| sta_step_appL m m' n r :
  m ~> m' ->
  App m n r ~> App m' n r

| sta_step_appR m n n' r :
  n ~> n' ->
  App m n r ~> App m n' r

| sta_step_beta A m n s r :
  App (Lam A m s r) n r ~> m.[n/]

| sta_step_indA A A' Cs s r :
  A ~> A' ->
  Ind A Cs s r ~> Ind A' Cs s r

| sta_step_indCs A Cs Cs' s r :
  {∃ C C' ∈ Cs & Cs', C ~> C'} ->
  Ind A Cs s r ~> Ind A Cs' s r

| sta_step_cons i I I' s r :
  I ~> I' ->
  Cons i I s r ~> Cons i I' s r

| sta_step_caseM m m' Q Fs r :
  m ~> m' ->
  Case m Q Fs r ~> Case m' Q Fs r

| sta_step_caseQ m Q Q' Fs r :
  Q ~> Q' ->
  Case m Q Fs r ~> Case m Q' Fs r

| sta_step_caseFs m Q Fs Fs' r :
  {∃ F F' ∈ Fs & Fs, F ~> F'} ->
  Case m Q Fs r ~> Case m Q Fs' r

| sta_step_iota i I ms Q Fs F s r :
  nth i Fs F ->
  Case (mkApps (Cons i I s r) ms) Q Fs r ~> mkApps F ms

where "m ~> n" := (sta_step m n).
