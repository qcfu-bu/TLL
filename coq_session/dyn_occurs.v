From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  sta_conf sta_uniq dyn_type dyn_cren dyn_valid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive cvar_pos : dyn_ctx -> cvar -> bool -> Prop :=
| cvar_pos_nil i :
  cvar_pos nil i false
| cvar_pos_ty Θ A :
  cvar_pos (A :L Θ) 0 true
| cvar_pos_n Θ :
  cvar_pos (_: Θ) 0 false
| cvar_pos_conv Θ x A b :
  cvar_pos Θ x b ->
  cvar_pos (A :: Θ) x.+1 b.

Inductive dyn_occurs :
  dyn_ctx -> sta_ctx -> dyn_ctx -> term -> term -> cvar -> nat -> Prop :=
(* core *)
| dyn_occurs_var Θ Γ Δ x s A i :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  sta_has Γ x A ->
  dyn_has Δ x s A ->
  dyn_occurs Θ Γ Δ (Var x) A i 0
| dyn_occurs_lam0 Θ Γ Δ A B m s i j :
  Θ ▷ s ->
  Δ ▷ s ->
  dyn_occurs Θ (A :: Γ) (_: Δ) m B i j ->
  dyn_occurs Θ Γ Δ (Lam0 A m s) (Pi0 A B s) i j
| dyn_occurs_lam1 Θ Γ Δ A B m s t i j :
  Θ ▷ s ->
  Δ ▷ s ->
  dyn_occurs Θ (A :: Γ) (A :{t} Δ) m B i j ->
  dyn_occurs Θ Γ Δ (Lam1 A m s) (Pi1 A B s) i j
| dyn_occurs_app0 Θ Γ Δ A B m n s i j :
  dyn_occurs Θ Γ Δ m (Pi0 A B s) i j ->
  Γ ⊢ n : A ->
  dyn_occurs Θ Γ Δ (App m n) B.[n/] i j
| dyn_occurs_app1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s i j1 j2 :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  dyn_occurs Θ1 Γ Δ1 m (Pi1 A B s) i j1 ->
  dyn_occurs Θ2 Γ Δ2 n A i j2 ->
  dyn_occurs Θ Γ Δ (App m n) B.[n/] i (j1 + j2)
| dyn_occurs_pair0 Θ Γ Δ A B m n t i j :
  Γ ⊢ Sig0 A B t : Sort t ->
  Γ ⊢ m : A ->
  dyn_occurs Θ Γ Δ n B.[m/] i j ->
  dyn_occurs Θ Γ Δ (Pair0 m n t) (Sig0 A B t) i j
| dyn_occurs_pair1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t i j1 j2 :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  Γ ⊢ Sig1 A B t : Sort t ->
  dyn_occurs Θ1 Γ Δ1 m A i j1 ->
  dyn_occurs Θ2 Γ Δ2 n B.[m/] i j2 ->
  dyn_occurs Θ Γ Δ (Pair1 m n t) (Sig1 A B t) i (j1 + j2)
| dyn_occurs_letin0 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t i j1 j2 :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  (Sig0 A B t :: Γ) ⊢ C : Sort s ->
  dyn_occurs Θ1 Γ Δ1 m (Sig0 A B t) i j1 ->
  dyn_occurs Θ2 (B :: A :: Γ) (B :{r} _: Δ2) n
    C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] i j2 ->
  dyn_occurs Θ Γ Δ (LetIn C m n) C.[m/] i (j1 + j2)
| dyn_occurs_letin1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t i j1 j2 :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  (Sig1 A B t :: Γ) ⊢ C : Sort s ->
  dyn_occurs Θ1 Γ Δ1 m (Sig1 A B t) i j1 ->
  dyn_occurs Θ2 (B :: A :: Γ) (B :{r2} A :{r1} Δ2) n
    C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] i j2 ->
  dyn_occurs Θ Γ Δ (LetIn C m n) C.[m/] i (j1 + j2)
| dyn_occurs_fix Θ Γ Δ A m i j :
  Θ ▷ U ->
  Δ ▷ U ->
  dyn_occurs Θ (A :: Γ) (A :U Δ) m A.[ren (+1)] i j ->
  dyn_occurs Θ Γ Δ (Fix A m) A i j
(* data *)
| dyn_occurs_ii Θ Γ Δ i :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  dyn_occurs Θ Γ Δ II Unit i 0
| dyn_occurs_tt Θ Γ Δ i :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  dyn_occurs Θ Γ Δ TT Bool i 0
| dyn_occurs_ff Θ Γ Δ i :
  dyn_empty Θ ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  dyn_occurs Θ Γ Δ FF Bool i 0
| dyn_occurs_ifte Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s i j0 j1 j2 :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  (Bool :: Γ) ⊢ A : Sort s ->
  dyn_occurs Θ1 Γ Δ1 m Bool i j0 ->
  dyn_occurs Θ2 Γ Δ2 n1 A.[TT/] i j1 ->
  dyn_occurs Θ2 Γ Δ2 n2 A.[FF/] i j2 ->
  dyn_occurs Θ Γ Δ (Ifte A m n1 n2) A.[m/] i (j0 + maxn j1 j2)
(* monadic *)
| dyn_occurs_return Θ Γ Δ m A i j :
  dyn_occurs Θ Γ Δ m A i j ->
  dyn_occurs Θ Γ Δ (Return m) (IO A) i j
| dyn_occurs_bind Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t i j1 j2 :
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  Γ ⊢ B : Sort t ->
  dyn_occurs Θ1 Γ Δ1 m (IO A) i j1 ->
  dyn_occurs Θ2 (A :: Γ) (A :{s} Δ2) n (IO B.[ren (+1)]) i j2 ->
  dyn_occurs Θ Γ Δ (Bind m n) (IO B) i (j1 + j2)
(* session *)
| dyn_occurs_cvar Θ Γ Δ r x A i j :
  j = (if x == i then 1 else 0) ->
  dyn_just Θ x (Ch r A) ->
  dyn_wf Γ Δ ->
  Δ ▷ U ->
  nil ⊢ A : Proto ->
  dyn_occurs Θ Γ Δ (CVar x) (Ch r A.[ren (+size Γ)]) i j
| dyn_occurs_fork Θ Γ Δ m A i j :
  dyn_occurs Θ (Ch true A :: Γ) (Ch true A :L Δ) m (IO Unit) i j ->
  dyn_occurs Θ Γ Δ (Fork A m) (IO (Ch false A)) i j
| dyn_ocurrs_recv0 Θ Γ Δ r1 r2 A B m i j :
  r1 (+) r2 = false ->
  dyn_occurs Θ Γ Δ m (Ch r1 (Act0 r2 A B)) i j ->
  dyn_occurs Θ Γ Δ (Recv0 m) (IO (Sig0 A (Ch r1 B) L)) i j
| dyn_occurs_recv1 Θ Γ Δ r1 r2 A B m i j :
  r1 (+) r2 = false ->
  dyn_occurs Θ Γ Δ m (Ch r1 (Act1 r2 A B)) i j ->
  dyn_occurs Θ Γ Δ (Recv1 m) (IO (Sig1 A (Ch r1 B) L)) i j
| dyn_occurs_send0 Θ Γ Δ r1 r2 A B m i j :
  r1 (+) r2 = true ->
  dyn_occurs Θ Γ Δ m (Ch r1 (Act0 r2 A B)) i j ->
  dyn_occurs Θ Γ Δ (Send0 m) (Pi0 A (IO (Ch r1 B)) L) i j
| dyn_occurs_send1 Θ Γ Δ r1 r2 A B m i j :
  r1 (+) r2 = true ->
  dyn_occurs Θ Γ Δ m (Ch r1 (Act1 r2 A B)) i j ->
  dyn_occurs Θ Γ Δ (Send1 m) (Pi1 A (IO (Ch r1 B)) L) i j
| dyn_occurs_wait Θ Γ Δ r1 r2 m i j :
  r1 (+) r2 = false ->
  dyn_occurs Θ Γ Δ m (Ch r1 (Stop r2)) i j ->
  dyn_occurs Θ Γ Δ (Wait m) (IO Unit) i j
| dyn_occurs_close Θ Γ Δ r1 r2 m i j :
  r1 (+) r2 = true ->
  dyn_occurs Θ Γ Δ m (Ch r1 (Stop r2)) i j ->
  dyn_occurs Θ Γ Δ (Close m) (IO Unit) i j
(* conversion *)
| dyn_occurs_conv Θ Γ Δ A B m s i j :
  A === B ->
  dyn_occurs Θ Γ Δ m A i j ->
  Γ ⊢ B : Sort s ->
  dyn_occurs Θ Γ Δ m B i j.

Lemma dyn_occurs_type Θ Γ Δ m A i j :
  dyn_occurs Θ Γ Δ m A i j -> Θ ; Γ ; Δ ⊢ m : A.
Proof with eauto using dyn_type. elim... Qed.

Lemma cvar_pos_merge_false Θ1 Θ2 Θ i :
  Θ1 ∘ Θ2 => Θ -> 
  cvar_pos Θ1 i false ->
  cvar_pos Θ2 i false ->
  cvar_pos Θ i false.
Proof with eauto using cvar_pos.
  move=>mrg. elim: mrg i=>{Θ1 Θ2 Θ}...
  { move=>Θ1 Θ2 Θ m mrg ih i pos1 pos2. inv pos1. inv pos2... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos1 pos2. inv pos1. inv pos2... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos1 pos2. inv pos1; inv pos2... }
  { move=>Θ1 Θ2 Θ mrg ih i pos1 pos2. inv pos1; inv pos2... }
Qed.

Lemma cvar_pos_split_false Θ1 Θ2 Θ i :
  Θ1 ∘ Θ2 => Θ -> cvar_pos Θ i false ->
  cvar_pos Θ1 i false /\
  cvar_pos Θ2 i false.
Proof with eauto using cvar_pos.
  move=>mrg. elim: mrg i=>{Θ1 Θ2 Θ}...
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[pos1 pos2]:=ih _ H3... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[pos1 pos2]:=ih _ H3... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[pos1 pos2]:=ih _ H3... }
  { move=>Θ1 Θ2 Θ mrg ih i pos. inv pos...
    have[pos1 pos2]:=ih _ H3... }
Qed.

Lemma cvar_pos_merge_true Θ1 Θ2 Θ i :
  Θ1 ∘ Θ2 => Θ -> cvar_pos Θ i true ->
  (cvar_pos Θ1 i false /\ cvar_pos Θ2 i true) \/
  (cvar_pos Θ1 i true /\ cvar_pos Θ2 i false).
Proof with eauto using cvar_pos.
  move=>mrg. elim: mrg i=>{Θ1 Θ2 Θ}.
  { move=>i pos. inv pos. }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    right...
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    left...
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
  { move=>Θ1 Θ2 Θ mrg ih i pos. inv pos.
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
Qed.

Lemma dyn_empty_pos_true Θ i : dyn_empty Θ -> cvar_pos Θ i true -> False.
Proof.
  move=>emp. elim: emp i=>{Θ}.
  { move=>i pos. inv pos. }
  { move=>Δ emp ih i pos. inv pos.
    apply: ih. apply: H3. }
Qed.

Lemma dyn_empty_pos_false Θ i : dyn_empty Θ -> cvar_pos Θ i false.
Proof.
  move=>emp. elim: emp i=>{Θ}.
  { move=>i. constructor. }
  { move=>Δ emp ih[|i].
    constructor.
    by constructor. }
Qed.

Lemma dyn_just_pos_true Θ x i A :
  dyn_just Θ x A -> cvar_pos Θ i true <-> x == i = true.
Proof with eauto.
  move=>js. elim: js i=>{Θ x A}.
  { move=>Δ A emp i. split.
    { move=>pos. inv pos=>//.
      exfalso. apply: dyn_empty_pos_true... }
    { move=>/eqP<-. constructor. } }
  { move=>Δ A x js ih i. split.
    { move=>pos. inv pos. move/ih in H3... }
    { move=>/eqP<-. constructor.
      rewrite ih. by apply/eqP. } }
Qed.

Lemma dyn_just_pos_false Θ x i A :
  dyn_just Θ x A -> cvar_pos Θ i false <-> x == i = false.
Proof with eauto.
  move=>js. elim: js i=>{Θ x A}.
  { move=>Δ A emp i. split.
    { move=>pos. inv pos. by apply/eqP. }
    { move: i=>[|i]/eqP//_.
      constructor. by apply: dyn_empty_pos_false. } }
  { move=>Δ A x js ih i. split. 
    { move=>pos. inv pos.
      by apply/eqP.
      move/ih in H3... }
    { move: i=>[|i] neq...
      constructor.
      constructor.
      rewrite ih... } }
Qed.

Lemma dyn_type_occurs0 Θ Γ Δ m A i :
  Θ ; Γ ; Δ ⊢ m : A -> cvar_pos Θ i false -> dyn_occurs Θ Γ Δ m A i 0.
Proof with eauto using dyn_occurs.
  move=>ty. elim: ty i=>{Θ Γ Δ m A}...
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have{}ihm:=ihm _ pos1.
    have{}ihn:=ihn _ pos2.
    have//:=dyn_occurs_app1 mrg1 mrg2 ihm ihn. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have{}ihm:=ihm _ pos1.
    have{}ihn:=ihn _ pos2.
    have//:=dyn_occurs_pair1 mrg1 mrg2 tyS ihm ihn. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2
           tyC tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have{}ihm:=ihm _ pos1.
    have{}ihn:=ihn _ pos2.
    have//:=dyn_occurs_letin0 mrg1 mrg2 tyC ihm ihn. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2
           tyC tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have{}ihm:=ihm _ pos1.
    have{}ihn:=ihn _ pos2.
    have//:=dyn_occurs_letin1 mrg1 mrg2 tyC ihm ihn. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
            tyA tym ihm tyn1 ihn1 tyn2 ihn2 i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have{}ihm:=ihm _ pos1.
    have{}ihn1:=ihn1 _ pos2.
    have{}ihn2:=ihn2 _ pos2.
    have//:=dyn_occurs_ifte mrg1 mrg2 tyA ihm ihn1 ihn2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
           tyB tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have{}ihm:=ihm _ pos1.
    have{}ihn:=ihn _ pos2.
    have//:=dyn_occurs_bind mrg1 mrg2 tyB ihm ihn. }
  { move=>Θ Γ Δ r x A js wf k tyA i pos.
    apply: dyn_occurs_cvar...
    move/(dyn_just_pos_false _ js) in pos.
    rewrite pos... }
Qed.

Lemma dyn_type_occurs1 Θ Γ Δ m A i :
  Θ ; Γ ; Δ ⊢ m : A -> cvar_pos Θ i true -> dyn_occurs Θ Γ Δ m A i 1.
Proof with eauto using dyn_occurs, dyn_type_occurs0.
  move=>ty. elim: ty i=>{Θ Γ Δ m A}...
  { move=>Θ Γ Δ x s A emp wf shs dhs i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_merge_true mrg1 pos.
    { replace 1 with (0 + 1) by eauto... }
    { replace 1 with (1 + 0) by eauto... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2
            tyS tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_merge_true mrg1 pos.
    { replace 1 with (0 + 1) by eauto... }
    { replace 1 with (1 + 0) by eauto... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2
            tyC tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_merge_true mrg1 pos.
    { replace 1 with (0 + 1) by eauto... }
    { replace 1 with (1 + 0) by eauto... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2
            tyC tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_merge_true mrg1 pos.
    { replace 1 with (0 + 1) by eauto... }
    { replace 1 with (1 + 0) by eauto... } }
  { move=>Θ Γ Δ emp wf k i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ Γ Δ emp wf k i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ Γ Δ emp wf k i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
           tyA tym ihm tyn1 ihn1 tyn2 ihn2 i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_merge_true mrg1 pos.
    { replace 1 with (0 + maxn 1 1) by eauto... }
    { replace 1 with (1 + maxn 0 0) by eauto... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
           tyB tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_merge_true mrg1 pos.
    { replace 1 with (0 + 1) by eauto... }
    { replace 1 with (1 + 0) by eauto... } }
  { move=>Θ Γ Δ r x A js wf k tyA i pos.
    constructor...
    move/(dyn_just_pos_true _ js) in pos.
    rewrite pos... }
Qed.

Lemma dyn_occurs_pos0 Θ Γ Δ m A i :
  dyn_occurs Θ Γ Δ m A i 0 -> cvar_pos Θ i false.
Proof with eauto using cvar_pos.
  move e:(0)=>j ty. elim: ty e=>{Θ Γ Δ m A i j}...
  { move=>Θ Γ Δ x s A i emp wf shs dhs _.
    apply: dyn_empty_pos_false... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s i j1 j2 mrg1 mrg2 tym ihm tyn ihn e.
    destruct j1; destruct j2; inv e.
    apply: cvar_pos_merge_false... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t i j1 j2 mrg1 mrg2 tyS tym ihm tyn ihn e.
    destruct j1; destruct j2; inv e.
    apply: cvar_pos_merge_false... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t i j1 j2 mrg1 mrg2 tyC tym ihm tyn ihn e.
    destruct j1; destruct j2; inv e.
    apply: cvar_pos_merge_false... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t i j1 j2 mrg1 mrg2 tyC tym ihm tyn ihn e.
    destruct j1; destruct j2; inv e.
    apply: cvar_pos_merge_false... }
  { move=>Θ Γ Δ i emp wf k _.
    apply: dyn_empty_pos_false... }
  { move=>Θ Γ Δ i emp wf k _.
    apply: dyn_empty_pos_false... }
  { move=>Θ Γ Δ i emp wf k _.
    apply: dyn_empty_pos_false... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s i j0 j1 j2 mrg1 mrg2 tyA tym ihm tyn1 ihn1 tyn2 ihn2 e.
    destruct j0; destruct j1; destruct j2; inv e.
    { apply: cvar_pos_merge_false... }
    { rewrite maxnSS in H0. inv H0. } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t i j1 j2 mrg1 mrg2 tyB tym ihm tyn ihn e.
    destruct j1; destruct j2; inv e.
    apply: cvar_pos_merge_false... }
  { move=>Θ Γ Δ r x A i j e1 js wf k ty. subst.
    case_eq (x == i)=>e1 e2//.
    rewrite dyn_just_pos_false... }
Qed.

Definition iren i (ξ : cvar -> cvar) := forall x, ξ x == i = false.

Lemma iren0 : iren 0 (+2).
Proof. elim; simpl; eauto. Qed.

Lemma iren1 : iren 1 (+2).
Proof. elim; simpl; eauto. Qed.

Lemma dyn_occurs_iren Θ Γ Δ m A i ξ :
  Θ ; Γ ; Δ ⊢ term_cren m ξ : A ->
  iren i ξ -> dyn_occurs Θ Γ Δ (term_cren m ξ) A i 0.
Proof with eauto using dyn_occurs.
  move e:(term_cren m ξ)=>x ty.
  elim: ty m ξ e i=>{Θ Γ Δ x A}...
  { move=>Θ Γ Δ A B m s k1 k2 tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ A B m s t k1 k2 tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ A B m n s tym ihm tyn m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e.
    replace 0 with (0 + 0) by eauto.
    apply: dyn_occurs_app1... }
  { move=>Θ Γ Δ A B m n t tyS tym tyn ihn m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2
           tyS tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e.
    replace 0 with (0 + 0) by eauto... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2
           tyC tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e.
    replace 0 with (0 + 0) by eauto.
    apply: dyn_occurs_letin0... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2
           tyC tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e.
    replace 0 with (0 + 0) by eauto.
    apply: dyn_occurs_letin1... }
  { move=>Θ Γ Δ A m k1 k2 tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
           tyA tym ihm tyn1 ihn1 tyn2 ihn2 m0 ξ e i h.
    destruct m0; inv e.
    replace 0 with (0 + maxn 0 0) by eauto... }
  { move=>Θ Γ Δ m A tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
           tyB tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e.
    replace 0 with (0 + 0) by eauto... }
  { move=>Θ Γ Δ r x A js wf k tyA m ξ e i h.
    destruct m; inv e.
    constructor...
    by rewrite h. }
  { move=>Θ Γ Δ m A tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
Qed.
