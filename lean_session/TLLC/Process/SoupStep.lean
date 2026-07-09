import TLLC.Process.Soup

/-!
# Machine steps on soup configurations

`Prim` is the abstract-machine form of `Process.Step`: each rule fires on the *front* threads of a
configuration and (for session redexes) on binder `0` — the soup equivalence relocates any thread
to the front and any binder to index `0`, so this loses no generality. `SoupStep` saturates `Prim`
with `SoupEquiv` on both sides. `step_soup` then maps every process reduction to a soup step of the
prenex forms: the base reduction rules are *literally* `Prim` instances (the process rules already
fire under a bare `nu (par _ _)`), the `par`/`res` congruence rules become configuration
compositions, and the `congr` rule is absorbed by `congruence_soup` plus saturation.

`Prim.close` carries the side condition that the remaining threads do not mention binder `0`
explicitly: the process `end` rule fires under a `nu` holding exactly the two closing threads, and
composition only adds threads from outside that restriction's scope, which cannot reference its
binder. The unshift `(· - 1)` may still rename *implicit* channel positions of the remaining
threads arbitrarily — implicit positions are erased ghosts, equated by `CongrTerm.chan_im`, so
this is invisible modulo `SoupEquiv`.
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Abstract-machine reduction on soup configurations. -/
inductive Prim : Config → Config → Prop where
  /-- A term reduction in the front thread (`Step.exp`). -/
  | exp {k m m' ts} :
    TLLC.Dynamic.Step m m' →
    Prim (k, m :: ts) (k, m' :: ts)
  /-- A fork in the front thread (`Step.fork`): mint binder `0`, shifting everything else up. -/
  | fork {k} {N : EvalCtx} {A m ts} :
    Prim (k, (N.eval (.fork A m)) :: ts)
      (k + 1,
        ((N.cren ((· + 1) : Nat → Nat)).eval (.pure (cvar 0))) ::
        ((m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan; (cvar 0)..]) ::
        ts.map (fun n => n⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩))
  /-- Implicit communication on binder `0` between the two front threads (`Step.comIm`). -/
  | comIm {k} {M N : EvalCtx} {o ts} :
    Prim
      (k + 1,
        (M.eval (.app (.send (cvar 0) .im) o .im)) :: (N.eval (.recv (cvar 0) .im)) :: ts)
      (k + 1,
        (M.eval (.pure (cvar 0))) :: (N.eval (.pure (.pair o (cvar 0) .im .L))) :: ts)
  /-- Explicit communication on binder `0` between the two front threads (`Step.comEx`). -/
  | comEx {k} {M N : EvalCtx} {v ts} :
    Val v →
    Prim
      (k + 1,
        (M.eval (.app (.send (cvar 0) .ex) v .ex)) :: (N.eval (.recv (cvar 0) .ex)) :: ts)
      (k + 1,
        (M.eval (.pure (cvar 0))) :: (N.eval (.pure (.pair v (cvar 0) .ex .L))) :: ts)
  /-- Closing binder `0` between the two front threads (`Step.end`): the binder is discarded and
  every other index unshifts. Neither the closing contexts nor the remaining threads may mention
  binder `0` explicitly (always true of well-typed processes, by linearity); without this the
  unshift's capture of dangling references would depend on the enclosing context and the rule
  could not be relocated. -/
  | close {k} {M N : EvalCtx} {ts} :
    occurs 0 (M.eval (.pure .one)) = 0 →
    occurs 0 (N.eval (.pure .one)) = 0 →
    (∀ n ∈ ts, occurs 0 n = 0) →
    Prim
      (k + 1,
        (M.eval (.close true (cvar 0))) :: (N.eval (.close false (cvar 0))) :: ts)
      (k,
        ((M.cren ((· - 1) : Nat → Nat)).eval (.pure .one)) ::
        ((N.cren ((· - 1) : Nat → Nat)).eval (.pure .one)) ::
        ts.map (fun n => n⟨((· - 1) : Nat → Nat); (id : Nat → Nat)⟩))

/-- A soup step: a machine step up to the soup equivalence on both sides. -/
def SoupStep (c c' : Config) : Prop :=
  ∃ c₁ c₂, SoupEquiv c c₁ ∧ Prim c₁ c₂ ∧ SoupEquiv c₂ c'

lemma SoupStep.of_prim {c c'} (h : Prim c c') : SoupStep c c' :=
  ⟨c, c', ARS.Conv.refl, h, ARS.Conv.refl⟩

lemma SoupStep.congr {c c₁ c₂ c'} (h1 : SoupEquiv c c₁) (h : SoupStep c₁ c₂)
    (h2 : SoupEquiv c₂ c') : SoupStep c c' := by
  obtain ⟨d₁, d₂, e1, prim, e2⟩ := h
  exact ⟨d₁, d₂, ARS.conv_trans h1 e1, prim, ARS.conv_trans e2 h2⟩

/-- Machine steps lift under a fresh outer restriction. -/
lemma Prim.nuConfig {c c' : Config} (h : Prim c c') :
    Prim (nuConfig c) (nuConfig c') := by
  cases h with
  | exp h => exact Prim.exp h
  | fork => exact Prim.fork
  | comIm => exact Prim.comIm
  | comEx hv => exact Prim.comEx hv
  | close hM hN hocc => exact Prim.close hM hN hocc

/-- Soup steps compose under a restriction. -/
lemma SoupStep.nuConfig {c c' : Config} (h : SoupStep c c') :
    SoupStep (nuConfig c) (nuConfig c') := by
  obtain ⟨d₁, d₂, e1, prim, e2⟩ := h
  exact ⟨TLLC.Process.nuConfig d₁, TLLC.Process.nuConfig d₂,
    SoupEquiv.nuConfig_congr e1, prim.nuConfig, SoupEquiv.nuConfig_congr e2⟩

/-! ## Positional machine steps -/

/-- Discard binder `e`: identity below, unshift above. -/
def unbind (e : Nat) (x : Nat) : Nat := if x < e then x else x - 1

/-- Machine steps with explicit redex positions and binder indices — no congruence slack. A
`Prim` step of any soup-equivalent configuration pulls back to a `PrimAt` step
(`prim_pullback` in `TLLC/Spawning/Reflection.lean`), which a spawning tree can replay
literally. New fork binders are minted at index `0`, shifting the others up; a closed binder
`e` is discarded, unshifting the others. -/
inductive PrimAt : Config → Config → Prop where
  | exp {k ts i m m'} :
    ts[i]? = some m →
    TLLC.Dynamic.Step m m' →
    PrimAt (k, ts) (k, ts.set i m')
  | fork {k ts i} {N : EvalCtx} {A m} :
    ts[i]? = some (N.eval (.fork A m)) →
    PrimAt (k, ts)
      (k + 1,
        ((ts.map (fun n => n⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)).set i
          ((N.cren ((· + 1) : Nat → Nat)).eval (.pure (cvar 0)))) ++
        [(m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)[Chan.var_Chan; (cvar 0)..]])
  | comIm {k ts i j e} {M N : EvalCtx} {o} :
    i ≠ j →
    e < k →
    ts[i]? = some (M.eval (.app (.send (cvar e) .im) o .im)) →
    ts[j]? = some (N.eval (.recv (cvar e) .im)) →
    PrimAt (k, ts)
      (k, (ts.set i (M.eval (.pure (cvar e)))).set j
        (N.eval (.pure (.pair o (cvar e) .im .L))))
  | comEx {k ts i j e} {M N : EvalCtx} {v} :
    i ≠ j →
    e < k →
    Val v →
    ts[i]? = some (M.eval (.app (.send (cvar e) .ex) v .ex)) →
    ts[j]? = some (N.eval (.recv (cvar e) .ex)) →
    PrimAt (k, ts)
      (k, (ts.set i (M.eval (.pure (cvar e)))).set j
        (N.eval (.pure (.pair v (cvar e) .ex .L))))
  | close {k ts i j e} {M N : EvalCtx} :
    i ≠ j →
    e < k →
    ts[i]? = some (M.eval (.close true (cvar e))) →
    ts[j]? = some (N.eval (.close false (cvar e))) →
    occurs e (M.eval (.pure .one)) = 0 →
    occurs e (N.eval (.pure .one)) = 0 →
    (∀ x m, ts[x]? = some m → x ≠ i → x ≠ j → occurs e m = 0) →
    PrimAt (k, ts)
      (k - 1,
        ((ts.set i (M.eval (.pure .one))).set j (N.eval (.pure .one))).map
          (fun n => n⟨unbind e; (id : Nat → Nat)⟩))

end TLLC.Process
