import TLLC.Dynamic.Progress
import TLLC.Spawning.Canonical

/-!
# Spawning-tree progress (Lemma 5.92)

Deadlock freedom for spawning trees: a valid tree is terminal or reduces; a valid node tree is
poised on its parent channel or reduces.

The mutual typing family cannot be `induction`ed directly, so the proof is a strong induction on
`treeMeasure`. The statement is strengthened with an `avoid` set of channel indices: every
constructed step's newly minted channels (fork rules) avoid it. This is what lets the congruence
cases discharge the `stepAvoids` side conditions of `Step.rootChild`/`nodeChild`/`rootSubtree`/
`nodeSubtree` — the inductive hypothesis is instantiated with the channels of the enclosing tree.

The parent-capturing fork is covered by `Step.nodeForkForward`; without that rule (absent from the
report) this lemma is false.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-! ## Fresh channel minting -/

/-- A channel index strictly above every element of `l`. -/
def freshIndex (l : List Nat) : Nat := l.foldr max 0 + 1

lemma le_foldr_max : ∀ {l : List Nat} {x}, x ∈ l → x ≤ l.foldr max 0
  | a :: l, x, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact (le_foldr_max h).trans (le_max_right _ _)

lemma lt_freshIndex {l : List Nat} {x} (h : x ∈ l) : x < freshIndex l :=
  Nat.lt_succ_of_le (le_foldr_max h)

lemma freshIndex_not_mem {l : List Nat} : freshIndex l ∉ l :=
  fun h => absurd (lt_freshIndex h) (by omega)

/-- Positions beyond the endpoint context are dead. -/
lemma CvarPos.ge_length_false : ∀ (Θ : PCtx) {x}, Θ.length ≤ x → CvarPos Θ x false
  | [], _, _ => .nil
  | s :: Θ, x, h => by
      cases x with
      | zero => simp at h
      | succ x =>
          exact .cons (CvarPos.ge_length_false Θ (by simpa using h))

/-- Closed terms do not mention channels beyond their endpoint context. -/
lemma occurs_ge_length {Θ : PCtx} {m A : Term}
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A) {x : Nat} (hx : Θ.length ≤ x) :
    occurs x m = 0 :=
  ty.occurs0 (CvarPos.ge_length_false Θ hx)

/-! ## Termination measure bookkeeping -/

lemma treeMeasure_le_childMeasure {c : Chan} {child : Tree} :
    ∀ {ms : List (Chan × Tree)}, (c, child) ∈ ms → treeMeasure child ≤ childMeasure ms
  | (c', t') :: ms, h => by
      rcases List.mem_cons.mp h with he | h
      · cases he
        simp only [childMeasure]
        omega
      · have := treeMeasure_le_childMeasure h
        simp only [childMeasure]
        omega

lemma treeMeasure_le_subMeasure {sub : Tree} :
    ∀ {ns : List Tree}, sub ∈ ns → treeMeasure sub ≤ subMeasure ns
  | t' :: ns, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp only [subMeasure]
        omega
      · have := treeMeasure_le_subMeasure h
        simp only [subMeasure]
        omega

/-! ## Avoid-set plumbing -/

/-- The channels created by a step (present in `t'` but not in `t`) avoid the index set `avoid`.
Instantiating `avoid` with the channels of an enclosing tree yields exactly `stepAvoids`. -/
def newChansAvoid (t t' : Tree) (avoid : List Nat) : Prop :=
  ∀ x ∈ treeChans t', x ∉ treeChans t → x ∉ avoid

/-- Steps that create no channels avoid everything. -/
lemma newChansAvoid_of_eq {t t' : Tree} {avoid : List Nat}
    (e : treeChansM t' = treeChansM t) : newChansAvoid t t' avoid := by
  intro x hx hnx
  exact absurd (mem_treeChansM.mp (e ▸ mem_treeChansM.mpr hx)) hnx

/-- Steps that only drop or rearrange channels (source = two extra channels on top of a
permutation of the target, or exactly a permutation) avoid everything. -/
lemma newChansAvoid_of_le {t t' : Tree} {avoid : List Nat}
    (h : treeChansM t' ≤ treeChansM t) : newChansAvoid t t' avoid := by
  intro x hx hnx
  exact absurd (mem_treeChansM.mp (Multiset.mem_of_le h (mem_treeChansM.mpr hx))) hnx

/-- Fresh channels chosen outside `avoid` keep the avoid-set condition for fork-shaped steps. -/
lemma newChansAvoid_of_cons₂ {t t' : Tree} {avoid : List Nat} {c d : Nat}
    (e : treeChansM t' = c ::ₘ d ::ₘ treeChansM t)
    (hc : c ∉ avoid) (hd : d ∉ avoid) : newChansAvoid t t' avoid := by
  intro x hx hnx
  have hx' := mem_treeChansM.mpr hx
  rw [e, Multiset.mem_cons, Multiset.mem_cons] at hx'
  rcases hx' with rfl | rfl | hx'
  · exact hc
  · exact hd
  · exact absurd (mem_treeChansM.mp hx') hnx

/-- Lifting an inner step's avoid-set guarantee through one congruence layer: it discharges the
`stepAvoids` side condition and propagates the outer guarantee. -/
lemma newChansAvoid_congr {t t' sub sub' : Tree} {ctx : Multiset Nat} {avoid : List Nat}
    (esrc : treeChansM t = ctx + treeChansM sub)
    (etgt : treeChansM t' = ctx + treeChansM sub')
    (hav : newChansAvoid sub sub' (treeChans t ++ avoid)) :
    stepAvoids sub sub' t ∧ newChansAvoid t t' avoid := by
  constructor
  · intro x hx hnx hmem
    exact hav x hx hnx (List.mem_append_left _ hmem)
  · intro x hx hnx
    have hx' := mem_treeChansM.mpr hx
    rw [etgt, Multiset.mem_add] at hx'
    rcases hx' with hx' | hx'
    · exact absurd (mem_treeChansM.mp (by rw [esrc, Multiset.mem_add]; exact .inl hx')) hnx
    · by_cases hsub : x ∈ treeChans sub
      · exact absurd (mem_treeChansM.mp
          (by rw [esrc, Multiset.mem_add]; exact .inr (mem_treeChansM.mpr hsub))) hnx
      · intro hmem
        exact hav x (mem_treeChansM.mp hx') hsub (List.mem_append_right _ hmem)

/-! ## List-level progress sweeps -/

/-- Either every detached subtree is terminal, or some detached subtree steps. -/
lemma subtrees_progress {qs : List Tree} (avoid : List Nat)
    (ty : ∀ q ∈ qs, Typed q)
    (ih : ∀ q ∈ qs, Typed q → Terminal q ∨ ∃ q', Step q q' ∧ newChansAvoid q q' avoid) :
    (∀ q ∈ qs, Terminal q) ∨
      ∃ l q r q', qs = l ++ q :: r ∧ Step q q' ∧ newChansAvoid q q' avoid := by
  induction qs with
  | nil => exact .inl (by simp)
  | cons q qs ihqs =>
      rcases ih q (by simp) (ty q (by simp)) with hterm | ⟨q', st, hav⟩
      · rcases ihqs (fun p hp => ty p (by simp [hp]))
            (fun p hp typ => ih p (by simp [hp]) typ) with hall | ⟨l, p, r, p', e, st, hav⟩
        · refine .inl ?_
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hterm
          · exact hall p hp
        · exact .inr ⟨q :: l, p, r, p', by simp [e], st, hav⟩
      · exact .inr ⟨[], q, qs, q', rfl, st, hav⟩

/-- Either every child is poised on its own edge, or some child steps. -/
lemma children_progress {ms : List (Chan × Tree)} (avoid : List Nat)
    (ty : ∀ c child, (c, child) ∈ ms → ∃ r A, TypedAt r A child)
    (ih : ∀ c child, (c, child) ∈ ms → ∀ r A, TypedAt r A child →
      (∃ d, PoisedAt d child) ∨ ∃ child', Step child child' ∧ newChansAvoid child child' avoid) :
    (∀ c child, (c, child) ∈ ms → ∃ d, PoisedAt d child) ∨
      ∃ l c child r child', ms = l ++ (c, child) :: r ∧ Step child child' ∧
        newChansAvoid child child' avoid := by
  induction ms with
  | nil => exact .inl (by simp)
  | cons e ms ihms =>
      obtain ⟨c, child⟩ := e
      obtain ⟨r, A, tyc⟩ := ty c child (by simp)
      rcases ih c child (by simp) r A tyc with hpoised | ⟨child', st, hav⟩
      · rcases ihms (fun c' ch hm => ty c' ch (by simp [hm]))
            (fun c' ch hm r' A' ty' => ih c' ch (by simp [hm]) r' A' ty') with
          hall | ⟨l, c', ch, rr, ch', e, st, hav⟩
        · refine .inl ?_
          intro c' ch hm
          rcases List.mem_cons.mp hm with he | hm
          · cases he
            exact hpoised
          · exact hall c' ch hm
        · exact .inr ⟨(c, child) :: l, c', ch, rr, ch', by simp [e], st, hav⟩
      · exact .inr ⟨[], c, child, ms, child', rfl, st, hav⟩

/-! ## Duality dispatch -/

/-- The session type of a poised term's endpoint slot determines the shape of its redex: an
action type forces the matching receive/send (with the polarity recorded), `stop` forces the
matching close/wait. This is the "by well-typedness, the dual form" step of the report's
Lemma 5.92. -/
lemma poisedRedex_dispatch {dkx : Nat} {redex : Term}
    (hp : PoisedRedex (.var_Chan dkx) redex)
    {Θk Θk1 Θk2 : PCtx} (single : PCtxSingle Θk) (mrg : PMerge Θk1 Θk2 Θk)
    {rC : Bool} {C : Term} (has : PHas Θk dkx rC C)
    {A0 : Term} (tyRedex : Θk1 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ redex : A0) :
    (∃ r2 A B i, (C ≃ .act r2 A B i) ∧ xor rC r2 = false ∧
        redex = .recv (.chan (.var_Chan dkx)) i) ∨
    (∃ r2 A B i v, (C ≃ .act r2 A B i) ∧ xor rC r2 = true ∧
        (i = .ex → Dynamic.Val v) ∧
        (i = .im → ∃ A'', Static.Typed ([] : Static.Ctx) v A'') ∧
        redex = .app (.send (.chan (.var_Chan dkx)) i) v i) ∨
    ((C ≃ .stop) ∧ redex = .close rC (.chan (.var_Chan dkx))) := by
  cases hp with
  | recvEx =>
      obtain ⟨r1, r2, A, B, hxor, _, tyChan⟩ := recvEx_inv tyRedex
      obtain ⟨r1', A1, just, _, eqCh⟩ := chan_inv tyChan
      rw [cren_len_nil] at eqCh
      obtain ⟨er, eAct⟩ := Static.ch_inj eqCh
      subst er
      obtain ⟨hrc, hAC⟩ := PJust_PHas_agree single mrg just has
      subst hrc
      subst hAC
      exact .inl ⟨r2, A, B, .ex, ARS.conv_sym eAct, hxor, rfl⟩
  | recvIm =>
      obtain ⟨r1, r2, A, B, hxor, _, tyChan⟩ := recvIm_inv tyRedex
      obtain ⟨r1', A1, just, _, eqCh⟩ := chan_inv tyChan
      rw [cren_len_nil] at eqCh
      obtain ⟨er, eAct⟩ := Static.ch_inj eqCh
      subst er
      obtain ⟨hrc, hAC⟩ := PJust_PHas_agree single mrg just has
      subst hrc
      subst hAC
      exact .inl ⟨r2, A, B, .im, ARS.conv_sym eAct, hxor, rfl⟩
  | @sendEx v hv =>
      obtain ⟨A_, B_, s_, Θs1, Θs2, Δ1, Δ2, mrgS, _, tySend, _, _⟩ := appEx_inv tyRedex
      obtain ⟨rs1, rs2, AAs, BBs, hxor, _, tyChan⟩ := sendEx_inv tySend
      obtain ⟨r1', A1, just, _, eqCh⟩ := chan_inv tyChan
      rw [cren_len_nil] at eqCh
      obtain ⟨er, eAct⟩ := Static.ch_inj eqCh
      subst er
      obtain ⟨Θc, _, mrgC⟩ := PMerge.splitR mrg mrgS
      obtain ⟨hrc, hAC⟩ := PJust_PHas_agree single mrgC.sym just has
      subst hrc
      subst hAC
      refine .inr (.inl ⟨rs2, AAs, BBs, .ex, v, ARS.conv_sym eAct, hxor, fun _ => hv, ?_, rfl⟩)
      intro h
      simp at h
  | @sendIm o =>
      obtain ⟨A_, B_, s_, tySend, tyStatic, _⟩ := appIm_inv tyRedex
      obtain ⟨rs1, rs2, AAs, BBs, hxor, _, tyChan⟩ := sendIm_inv tySend
      obtain ⟨r1', A1, just, _, eqCh⟩ := chan_inv tyChan
      rw [cren_len_nil] at eqCh
      obtain ⟨er, eAct⟩ := Static.ch_inj eqCh
      subst er
      obtain ⟨hrc, hAC⟩ := PJust_PHas_agree single mrg just has
      subst hrc
      subst hAC
      exact .inr (.inl ⟨rs2, AAs, BBs, .im, o, ARS.conv_sym eAct, hxor,
        (fun h => by simp at h), fun _ => ⟨A_, tyStatic⟩, rfl⟩)
  | close =>
      obtain ⟨_, tyChan⟩ := close_inv tyRedex
      obtain ⟨r1', A1, just, _, eqCh⟩ := chan_inv tyChan
      rw [cren_len_nil] at eqCh
      obtain ⟨er, eStop⟩ := Static.ch_inj eqCh
      obtain ⟨hrc, hAC⟩ := PJust_PHas_agree single mrg just has
      subst hrc
      subst hAC
      subst er
      exact .inr (.inr ⟨ARS.conv_sym eStop, rfl⟩)
  | wait =>
      obtain ⟨_, tyChan⟩ := wait_inv tyRedex
      obtain ⟨r1', A1, just, _, eqCh⟩ := chan_inv tyChan
      rw [cren_len_nil] at eqCh
      obtain ⟨er, eStop⟩ := Static.ch_inj eqCh
      obtain ⟨hrc, hAC⟩ := PJust_PHas_agree single mrg just has
      subst hrc
      subst hAC
      subst er
      exact .inr (.inr ⟨ARS.conv_sym eStop, rfl⟩)

/-! ## The main induction -/

/-- Lemma 5.92 (Spawning Tree Progress), strengthened for the induction: steps can be chosen with
their fresh channels avoiding any given index set. -/
theorem progress_mutual :
    ∀ (n : Nat) (t : Tree), treeMeasure t ≤ n → ∀ avoid : List Nat,
      (Typed t → Terminal t ∨ ∃ t', Step t t' ∧ newChansAvoid t t' avoid) ∧
      (∀ r A, TypedAt r A t →
        (∃ d, PoisedAt d t) ∨ ∃ t', Step t t' ∧ newChansAvoid t t' avoid) := by
  intro n
  induction n with
  | zero =>
      intro t h _
      exfalso
      cases t <;> simp [treeMeasure] at h
  | succ n ihn =>
      intro t hle avoid
      cases t with
      | root m ms qs =>
          refine ⟨fun ty => ?_, fun r A ty => (by cases ty)⟩
          cases ty with
          | @root Θ _ _ _ single tym tyms tyqs =>
          simp only [treeMeasure] at hle
          -- (1) sweep the detached subtrees
          rcases subtrees_progress (treeChans (.root m ms qs) ++ avoid)
              (fun q hq => tyqs.typed_of_mem hq)
              (fun q hq typ =>
                (ihn q (by have := treeMeasure_le_subMeasure hq; omega) _).1 typ) with
            hallTerm | ⟨l, q, rr, q', rfl, st, hav⟩
          · -- (2) analyze the root computation
            rcases TLLC.Dynamic.Typed.progress tym with hval | ⟨m', dst⟩
            · -- (3) values: finished or thunk
              rcases tym.monad_canonical hval ARS.Conv.refl with ⟨u, vu, rfl⟩ | hthunk
              · -- (4) finished: the tree is terminal
                have hone : u = .one := (pure_inv tym).unit_canonical vu ARS.Conv.refl
                subst hone
                cases ms with
                | nil => exact .inl (Terminal.root hallTerm)
                | cons e ms' =>
                    exfalso
                    obtain ⟨c, child⟩ := e
                    have hpos := ChildrenTyped.pos_of_label tyms
                      (List.mem_map.mpr ⟨(c, child), by simp, rfl⟩)
                    have h1 := tym.occurs1 hpos
                    simp [occurs] at h1
              · -- (5) thunks: decompose into an evaluation context and a partial redex
                obtain ⟨M, redex, rfl, hpart⟩ := hthunk.evalctx
                cases hpart with
                | @fork A' body =>
                    -- mint two fresh channels above the context, the tree, and the avoid set
                    have hlen : Θ.length < freshIndex (Θ.length ::
                        (treeChans (.root (M.eval (.fork A' body)) ms qs) ++ avoid)) :=
                      lt_freshIndex (by simp)
                    have htree : ∀ x ∈ treeChans (.root (M.eval (.fork A' body)) ms qs),
                        x < freshIndex (Θ.length ::
                          (treeChans (.root (M.eval (.fork A' body)) ms qs) ++ avoid)) :=
                      fun x hx => lt_freshIndex (by simp [hx])
                    have havd : ∀ x ∈ avoid, x < freshIndex (Θ.length ::
                        (treeChans (.root (M.eval (.fork A' body)) ms qs) ++ avoid)) :=
                      fun x hx => lt_freshIndex (by simp [hx])
                    set cI := freshIndex (Θ.length ::
                      (treeChans (.root (M.eval (.fork A' body)) ms qs) ++ avoid)) with hcI
                    refine .inr ⟨_, Step.rootFork (c := .var_Chan cI)
                      (d := .var_Chan (cI + 1)) ?_ ?_ ?_, ?_⟩
                    · exact occurs_ge_length tym (by omega)
                    · exact occurs_ge_length tym (by omega)
                    · refine ⟨fun h => ?_, fun h => ?_, ?_⟩
                      · have := htree _ h
                        simp [chanIndex] at this
                      · have := htree _ h
                        simp [chanIndex] at this
                      · simp only [chanIndex]
                        omega
                    · refine newChansAvoid_of_cons₂ (c := cI) (d := cI + 1) ?_ ?_ ?_
                      · simp only [treeChansM_root, forkChildren, childChansM_insertChild,
                          treeChansM_node, subChansM_nil, add_zero, chanIndex,
                          ← Multiset.singleton_add]
                        rw [← childChansM_split body ms]
                        abel
                      · intro h
                        have := havd _ h
                        omega
                      · intro h
                        have := havd _ h
                        omega
                | @recv c i =>
                    -- session type of the receiving channel
                    obtain ⟨Θ1, Θ2, A0, mrg, tyRecv, cont⟩ := evalCtx_inv tym
                    have hInv : ∃ rr1 rr2 AAr BBr,
                        xor rr1 rr2 = false ∧
                        (Θ1 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
                          .chan (.var_Chan c) : .ch rr1 (.act rr2 AAr BBr i)) := by
                      cases i
                      · obtain ⟨rr1, rr2, AAr, BBr, hx, _, tyChan⟩ := recvIm_inv tyRecv
                        exact ⟨rr1, rr2, AAr, BBr, hx, tyChan⟩
                      · obtain ⟨rr1, rr2, AAr, BBr, hx, _, tyChan⟩ := recvEx_inv tyRecv
                        exact ⟨rr1, rr2, AAr, BBr, hx, tyChan⟩
                    obtain ⟨rr1, rr2, AAr, BBr, xorR, tyChanR⟩ := hInv
                    obtain ⟨r1, A1, just, _, eqCh⟩ := chan_inv tyChanR
                    rw [cren_len_nil] at eqCh
                    obtain ⟨er, eAct⟩ := Static.ch_inj eqCh
                    subst er
                    -- locate the receiving channel among the children
                    have posC : CvarPos Θ c true :=
                      CvarPos.merge_true_left single mrg (just.pos_true.mpr rfl)
                    obtain ⟨⟨ck, child⟩, hmem, hck⟩ :=
                      List.mem_map.mp (ChildrenTyped.label_of_pos tyms posC)
                    simp only at hck
                    subst hck
                    obtain ⟨l, rr, hms⟩ := List.append_of_mem hmem
                    subst hms
                    obtain ⟨C, tyChild, hC, tyRest⟩ :=
                      ChildrenTyped.remove just mrg tyms rfl rfl
                    -- the child either steps or is poised on its endpoint
                    have hmeas : treeMeasure child ≤ n := by
                      have h := treeMeasure_le_childMeasure
                        (c := Chan.var_Chan c) (child := child)
                        (ms := l ++ (Chan.var_Chan c, child) :: rr) (by simp)
                      omega
                    rcases (ihn child hmeas
                        (treeChans (.root (M.eval (.recv (.chan (.var_Chan c)) i))
                          (l ++ (Chan.var_Chan c, child) :: rr) qs) ++ avoid)).2 _ _
                        tyChild with ⟨dk, hpoised⟩ | ⟨child', st, hav⟩
                    · -- the child is poised: duality forces the matching send
                      cases hpoised with
                      | @node mk msk qsk hpm =>
                      obtain ⟨N, redex', hmk, hredex⟩ := hpm.evalctx
                      subst hmk
                      cases tyChild with
                      | @node Θk dkx _ _ _ _ _ singlek hask tymk tymsk tyqsk =>
                      obtain ⟨Θk1, Θk2, A0k, mrgk, tyRedex, _⟩ := evalCtx_inv tymk
                      rcases poisedRedex_dispatch hredex singlek mrgk hask tyRedex with
                        ⟨r2', A', B', i', hCact, hxor', _⟩ |
                        ⟨r2', A', B', i', v, hCact, _, hvalFn, _, hredexEq⟩ |
                        ⟨hCstop, _⟩
                      · -- the child also receives: polarity clash
                        exfalso
                        have hActs : Term.act r2' A' B' i' ≃ .act rr2 AAr BBr i :=
                          ARS.conv_trans (ARS.conv_sym hCact)
                            (ARS.conv_trans hC (ARS.conv_sym eAct))
                        obtain ⟨_, _, hr2, _⟩ := Static.act_inj hActs
                        rw [hr2] at hxor'
                        cases rr1 <;> cases rr2 <;> simp_all
                      · -- the child sends: fire the com
                        have hActs : Term.act r2' A' B' i' ≃ .act rr2 AAr BBr i :=
                          ARS.conv_trans (ARS.conv_sym hCact)
                            (ARS.conv_trans hC (ARS.conv_sym eAct))
                        obtain ⟨_, _, hr2, hi⟩ := Static.act_inj hActs
                        rw [hi] at hredexEq
                        subst hredexEq
                        cases i with
                        | ex =>
                            refine .inr ⟨_, Step.rootRecvEx (hvalFn hi), newChansAvoid_of_eq ?_⟩
                            have e3 : childChansM (splitChildrenByTerm v msk).1
                                  + childChansM (splitChildrenByTerm v msk).2
                                = childChansM msk := childChansM_split v msk
                            have e1 : treeChansM (.root
                                  (M.eval (.pure (.pair v (Term.chan (.var_Chan c)) .ex .L)))
                                  (recvExChildren v (.var_Chan c) (.var_Chan dkx) N msk qsk
                                    (l ++ rr)) qs)
                                = (childChansM (splitChildrenByTerm v msk).1
                                    + childChansM (splitChildrenByTerm v msk).2)
                                  + ({chanIndex (Chan.var_Chan c)}
                                      + {chanIndex (Chan.var_Chan dkx)} + childChansM l
                                      + childChansM rr + subChansM qsk + subChansM qs) := by
                              simp only [recvExChildren, treeChansM_root, treeChansM_node,
                                childChansM_insertChild, childChansM_mergeChildren,
                                childChansM_append, ← Multiset.singleton_add]
                              abel
                            have e2 : treeChansM (.root
                                  (M.eval (.recv (.chan (.var_Chan c)) .ex))
                                  (l ++ (Chan.var_Chan c, .node (Chan.var_Chan dkx)
                                    (N.eval (.app (.send (Term.chan (.var_Chan dkx)) .ex) v .ex))
                                    msk qsk) :: rr) qs)
                                = childChansM msk
                                  + ({chanIndex (Chan.var_Chan c)}
                                      + {chanIndex (Chan.var_Chan dkx)} + childChansM l
                                      + childChansM rr + subChansM qsk + subChansM qs) := by
                              simp only [treeChansM_root, treeChansM_node, childChansM_append,
                                childChansM_cons, ← Multiset.singleton_add]
                              abel
                            rw [e1, e3, e2]
                        | im =>
                            refine .inr ⟨_, Step.rootRecvIm, newChansAvoid_of_eq ?_⟩
                            simp only [treeChansM_root, treeChansM_node, childChansM_append,
                              childChansM_cons]
                      · -- the child is finished: protocol clash
                        exfalso
                        have hbad : Term.act rr2 AAr BBr i ≃ .stop :=
                          ARS.conv_trans eAct
                            (ARS.conv_trans (ARS.conv_sym hC) hCstop)
                        false_conv
                    · -- the selected child steps: Root-Child
                      have esrc : treeChansM (.root
                            (M.eval (.recv (.chan (.var_Chan c)) i))
                            (l ++ (Chan.var_Chan c, child) :: rr) qs)
                          = (chanIndex (Chan.var_Chan c) ::ₘ 0
                              + (childChansM l + childChansM rr + subChansM qs))
                            + treeChansM child := by
                        simp only [treeChansM_root, childChansM_append, childChansM_cons,
                          ← Multiset.singleton_add]
                        abel
                      have etgt : treeChansM (.root
                            (M.eval (.recv (.chan (.var_Chan c)) i))
                            (l ++ (Chan.var_Chan c, child') :: rr) qs)
                          = (chanIndex (Chan.var_Chan c) ::ₘ 0
                              + (childChansM l + childChansM rr + subChansM qs))
                            + treeChansM child' := by
                        simp only [treeChansM_root, childChansM_append, childChansM_cons,
                          ← Multiset.singleton_add]
                        abel
                      obtain ⟨hsa, houter⟩ := newChansAvoid_congr esrc etgt hav
                      exact .inr ⟨_, Step.rootChild st hsa, houter⟩
                | @appSendIm c o =>
                    -- session type of the sending channel
                    obtain ⟨Θ1, Θ2, A0, mrg, tyApp, cont⟩ := evalCtx_inv tym
                    obtain ⟨A_, B_, s_, tySend, _, _⟩ := appIm_inv tyApp
                    obtain ⟨rs1, rs2, AAs, BBs, xorS, _, tyChanS⟩ := sendIm_inv tySend
                    obtain ⟨r1, A1, just, _, eqCh⟩ := chan_inv tyChanS
                    rw [cren_len_nil] at eqCh
                    obtain ⟨er, eAct⟩ := Static.ch_inj eqCh
                    subst er
                    -- locate the sending channel among the children
                    have posC : CvarPos Θ c true :=
                      CvarPos.merge_true_left single mrg (just.pos_true.mpr rfl)
                    obtain ⟨⟨ck, child⟩, hmem, hck⟩ :=
                      List.mem_map.mp (ChildrenTyped.label_of_pos tyms posC)
                    simp only at hck
                    subst hck
                    obtain ⟨l, rr, hms⟩ := List.append_of_mem hmem
                    subst hms
                    obtain ⟨C, tyChild, hC, tyRest⟩ :=
                      ChildrenTyped.remove just mrg tyms rfl rfl
                    have hmeas : treeMeasure child ≤ n := by
                      have h := treeMeasure_le_childMeasure
                        (c := Chan.var_Chan c) (child := child)
                        (ms := l ++ (Chan.var_Chan c, child) :: rr) (by simp)
                      omega
                    rcases (ihn child hmeas
                        (treeChans (.root
                          (M.eval (.app (.send (.chan (.var_Chan c)) .im) o .im))
                          (l ++ (Chan.var_Chan c, child) :: rr) qs) ++ avoid)).2 _ _
                        tyChild with ⟨dk, hpoised⟩ | ⟨child', st, hav⟩
                    · -- the child is poised: duality forces the matching receive
                      cases hpoised with
                      | @node mk msk qsk hpm =>
                      obtain ⟨N, redex', hmk, hredex⟩ := hpm.evalctx
                      subst hmk
                      cases tyChild with
                      | @node Θk dkx _ _ _ _ _ singlek hask tymk tymsk tyqsk =>
                      obtain ⟨Θk1, Θk2, A0k, mrgk, tyRedex, _⟩ := evalCtx_inv tymk
                      rcases poisedRedex_dispatch hredex singlek mrgk hask tyRedex with
                        ⟨r2', A', B', i', hCact, _, hredexEq⟩ |
                        ⟨r2', A', B', i', v, hCact, hxor', _, _, _⟩ |
                        ⟨hCstop, _⟩
                      · -- the child receives: fire the com
                        have hActs : Term.act r2' A' B' i' ≃ .act rs2 AAs BBs .im :=
                          ARS.conv_trans (ARS.conv_sym hCact)
                            (ARS.conv_trans hC (ARS.conv_sym eAct))
                        obtain ⟨_, _, _, hi⟩ := Static.act_inj hActs
                        rw [hi] at hredexEq
                        subst hredexEq
                        refine .inr ⟨_, Step.rootSendIm, newChansAvoid_of_eq ?_⟩
                        simp only [treeChansM_root, treeChansM_node, childChansM_append,
                          childChansM_cons]
                      · -- the child also sends: polarity clash
                        exfalso
                        have hActs : Term.act r2' A' B' i' ≃ .act rs2 AAs BBs .im :=
                          ARS.conv_trans (ARS.conv_sym hCact)
                            (ARS.conv_trans hC (ARS.conv_sym eAct))
                        obtain ⟨_, _, hr2, _⟩ := Static.act_inj hActs
                        rw [hr2] at hxor'
                        cases rs1 <;> cases rs2 <;> simp_all
                      · -- the child is finished: protocol clash
                        exfalso
                        have hbad : Term.act rs2 AAs BBs .im ≃ .stop :=
                          ARS.conv_trans eAct
                            (ARS.conv_trans (ARS.conv_sym hC) hCstop)
                        false_conv
                    · -- the selected child steps: Root-Child
                      have esrc : treeChansM (.root
                            (M.eval (.app (.send (.chan (.var_Chan c)) .im) o .im))
                            (l ++ (Chan.var_Chan c, child) :: rr) qs)
                          = (chanIndex (Chan.var_Chan c) ::ₘ 0
                              + (childChansM l + childChansM rr + subChansM qs))
                            + treeChansM child := by
                        simp only [treeChansM_root, childChansM_append, childChansM_cons,
                          ← Multiset.singleton_add]
                        abel
                      have etgt : treeChansM (.root
                            (M.eval (.app (.send (.chan (.var_Chan c)) .im) o .im))
                            (l ++ (Chan.var_Chan c, child') :: rr) qs)
                          = (chanIndex (Chan.var_Chan c) ::ₘ 0
                              + (childChansM l + childChansM rr + subChansM qs))
                            + treeChansM child' := by
                        simp only [treeChansM_root, childChansM_append, childChansM_cons,
                          ← Multiset.singleton_add]
                        abel
                      obtain ⟨hsa, houter⟩ := newChansAvoid_congr esrc etgt hav
                      exact .inr ⟨_, Step.rootChild st hsa, houter⟩
                | @appSendEx c v value =>
                    -- session type of the sending channel
                    obtain ⟨Θ1, Θ2, A0, mrg, tyApp, cont⟩ := evalCtx_inv tym
                    obtain ⟨A_, B_, s_, Θs1, Θs2, Δ1, Δ2, mrgS, _, tySend, _, _⟩ :=
                      appEx_inv tyApp
                    obtain ⟨rs1, rs2, AAs, BBs, xorS, _, tyChanS⟩ := sendEx_inv tySend
                    obtain ⟨r1, A1, just, _, eqCh⟩ := chan_inv tyChanS
                    rw [cren_len_nil] at eqCh
                    obtain ⟨er, eAct⟩ := Static.ch_inj eqCh
                    subst er
                    obtain ⟨Θc', _, mrg2⟩ := PMerge.splitR mrg mrgS
                    -- locate the sending channel among the children
                    have posC : CvarPos Θ c true :=
                      CvarPos.merge_true_left single mrg2.sym (just.pos_true.mpr rfl)
                    obtain ⟨⟨ck, child⟩, hmem, hck⟩ :=
                      List.mem_map.mp (ChildrenTyped.label_of_pos tyms posC)
                    simp only at hck
                    subst hck
                    obtain ⟨l, rr, hms⟩ := List.append_of_mem hmem
                    subst hms
                    obtain ⟨C, tyChild, hC, tyRest⟩ :=
                      ChildrenTyped.remove just mrg2.sym tyms rfl rfl
                    have hmeas : treeMeasure child ≤ n := by
                      have h := treeMeasure_le_childMeasure
                        (c := Chan.var_Chan c) (child := child)
                        (ms := l ++ (Chan.var_Chan c, child) :: rr) (by simp)
                      omega
                    rcases (ihn child hmeas
                        (treeChans (.root
                          (M.eval (.app (.send (.chan (.var_Chan c)) .ex) v .ex))
                          (l ++ (Chan.var_Chan c, child) :: rr) qs) ++ avoid)).2 _ _
                        tyChild with ⟨dk, hpoised⟩ | ⟨child', st, hav⟩
                    · -- the child is poised: duality forces the matching receive
                      cases hpoised with
                      | @node mk msk qsk hpm =>
                      obtain ⟨N, redex', hmk, hredex⟩ := hpm.evalctx
                      subst hmk
                      cases tyChild with
                      | @node Θk dkx _ _ _ _ _ singlek hask tymk tymsk tyqsk =>
                      obtain ⟨Θk1, Θk2, A0k, mrgk, tyRedex, _⟩ := evalCtx_inv tymk
                      rcases poisedRedex_dispatch hredex singlek mrgk hask tyRedex with
                        ⟨r2', A', B', i', hCact, _, hredexEq⟩ |
                        ⟨r2', A', B', i', w, hCact, hxor', _, _, _⟩ |
                        ⟨hCstop, _⟩
                      · -- the child receives: fire the com
                        have hActs : Term.act r2' A' B' i' ≃ .act rs2 AAs BBs .ex :=
                          ARS.conv_trans (ARS.conv_sym hCact)
                            (ARS.conv_trans hC (ARS.conv_sym eAct))
                        obtain ⟨_, _, _, hi⟩ := Static.act_inj hActs
                        rw [hi] at hredexEq
                        subst hredexEq
                        refine .inr ⟨_, Step.rootSendEx value, newChansAvoid_of_eq ?_⟩
                        have e3 : childChansM (splitChildrenByTerm v (l ++ rr)).1
                              + childChansM (splitChildrenByTerm v (l ++ rr)).2
                            = childChansM l + childChansM rr := by
                          rw [childChansM_split, childChansM_append]
                        have e1 : treeChansM (.root
                              (M.eval (.pure (Term.chan (.var_Chan c))))
                              (sendExChildren v (.var_Chan c) (.var_Chan dkx) N msk qsk
                                (l ++ rr)) qs)
                            = (childChansM (splitChildrenByTerm v (l ++ rr)).1
                                + childChansM (splitChildrenByTerm v (l ++ rr)).2)
                              + ({chanIndex (Chan.var_Chan c)}
                                  + {chanIndex (Chan.var_Chan dkx)} + childChansM msk
                                  + subChansM qsk + subChansM qs) := by
                          simp only [sendExChildren, treeChansM_root, treeChansM_node,
                            childChansM_insertChild, childChansM_mergeChildren,
                            ← Multiset.singleton_add]
                          abel
                        have e2 : treeChansM (.root
                              (M.eval (.app (.send (.chan (.var_Chan c)) .ex) v .ex))
                              (l ++ (Chan.var_Chan c, .node (Chan.var_Chan dkx)
                                (N.eval (.recv (Term.chan (.var_Chan dkx)) .ex))
                                msk qsk) :: rr) qs)
                            = (childChansM l + childChansM rr)
                              + ({chanIndex (Chan.var_Chan c)}
                                  + {chanIndex (Chan.var_Chan dkx)} + childChansM msk
                                  + subChansM qsk + subChansM qs) := by
                          simp only [treeChansM_root, treeChansM_node, childChansM_append,
                            childChansM_cons, ← Multiset.singleton_add]
                          abel
                        rw [e1, e3, e2]
                      · -- the child also sends: polarity clash
                        exfalso
                        have hActs : Term.act r2' A' B' i' ≃ .act rs2 AAs BBs .ex :=
                          ARS.conv_trans (ARS.conv_sym hCact)
                            (ARS.conv_trans hC (ARS.conv_sym eAct))
                        obtain ⟨_, _, hr2, _⟩ := Static.act_inj hActs
                        rw [hr2] at hxor'
                        cases rs1 <;> cases rs2 <;> simp_all
                      · -- the child is finished: protocol clash
                        exfalso
                        have hbad : Term.act rs2 AAs BBs .ex ≃ .stop :=
                          ARS.conv_trans eAct
                            (ARS.conv_trans (ARS.conv_sym hC) hCstop)
                        false_conv
                    · -- the selected child steps: Root-Child
                      have esrc : treeChansM (.root
                            (M.eval (.app (.send (.chan (.var_Chan c)) .ex) v .ex))
                            (l ++ (Chan.var_Chan c, child) :: rr) qs)
                          = (chanIndex (Chan.var_Chan c) ::ₘ 0
                              + (childChansM l + childChansM rr + subChansM qs))
                            + treeChansM child := by
                        simp only [treeChansM_root, childChansM_append, childChansM_cons,
                          ← Multiset.singleton_add]
                        abel
                      have etgt : treeChansM (.root
                            (M.eval (.app (.send (.chan (.var_Chan c)) .ex) v .ex))
                            (l ++ (Chan.var_Chan c, child') :: rr) qs)
                          = (chanIndex (Chan.var_Chan c) ::ₘ 0
                              + (childChansM l + childChansM rr + subChansM qs))
                            + treeChansM child' := by
                        simp only [treeChansM_root, childChansM_append, childChansM_cons,
                          ← Multiset.singleton_add]
                        abel
                      obtain ⟨hsa, houter⟩ := newChansAvoid_congr esrc etgt hav
                      exact .inr ⟨_, Step.rootChild st hsa, houter⟩
                | @close b c =>
                    -- locate the closing channel among the children
                    obtain ⟨Θ1, Θ2, A0, mrg, tyClose, cont⟩ := evalCtx_inv tym
                    have hinv : (Term.M A0 ≃ Term.M .unit) ∧
                        (Θ1 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
                          .chan (Chan.var_Chan c) : .ch b .stop) := by
                      cases b
                      · exact wait_inv tyClose
                      · exact close_inv tyClose
                    obtain ⟨r1, A1, just, _, eqCh⟩ := chan_inv hinv.2
                    rw [cren_len_nil] at eqCh
                    obtain ⟨er, eStop⟩ := Static.ch_inj eqCh
                    subst er
                    have posC : CvarPos Θ c true :=
                      CvarPos.merge_true_left single mrg (just.pos_true.mpr rfl)
                    obtain ⟨⟨ck, child⟩, hmem, hck⟩ :=
                      List.mem_map.mp (ChildrenTyped.label_of_pos tyms posC)
                    simp only at hck
                    subst hck
                    obtain ⟨l, rr, hms⟩ := List.append_of_mem hmem
                    subst hms
                    obtain ⟨C, tyChild, hC, tyRest⟩ :=
                      ChildrenTyped.remove just mrg tyms rfl rfl
                    -- the child either steps or is poised on its endpoint
                    have hmeas : treeMeasure child ≤ n := by
                      have h := treeMeasure_le_childMeasure
                        (c := Chan.var_Chan c) (child := child)
                        (ms := l ++ (Chan.var_Chan c, child) :: rr) (by simp)
                      omega
                    rcases (ihn child hmeas
                        (treeChans (.root (M.eval (.close b (.chan (.var_Chan c))))
                          (l ++ (Chan.var_Chan c, child) :: rr) qs) ++ avoid)).2 _ _
                        tyChild with ⟨dk, hpoised⟩ | ⟨child', st, hav⟩
                    · -- the child is poised: duality forces the matching close
                      cases hpoised with
                      | @node mk msk qsk hpm =>
                      obtain ⟨N, redex', hmk, hredex⟩ := hpm.evalctx
                      subst hmk
                      cases tyChild with
                      | @node Θk dkx _ _ _ _ _ singlek hask tymk tymsk tyqsk =>
                      obtain ⟨Θk1, Θk2, A0k, mrgk, tyRedex, _⟩ := evalCtx_inv tymk
                      rcases poisedRedex_dispatch hredex singlek mrgk hask tyRedex with
                        ⟨r2, A', B', i, hCact, _, _⟩ | ⟨r2, A', B', i, v, hCact, _, _, _⟩ |
                        ⟨hCstop, hredexEq⟩
                      · exfalso
                        have hbad : Term.act r2 A' B' i ≃ .stop :=
                          ARS.conv_trans (ARS.conv_sym hCact)
                            (ARS.conv_trans hC (ARS.conv_sym eStop))
                        false_conv
                      · exfalso
                        have hbad : Term.act r2 A' B' i ≃ .stop :=
                          ARS.conv_trans (ARS.conv_sym hCact)
                            (ARS.conv_trans hC (ARS.conv_sym eStop))
                        false_conv
                      · -- fire the END step
                        subst hredexEq
                        cases b with
                        | false =>
                            simp only [Bool.not_false]
                            refine .inr ⟨_, Step.rootWait, newChansAvoid_of_le ?_⟩
                            have e : treeChansM (.root
                                  (M.eval (.close false (Term.chan (.var_Chan c))))
                                  (l ++ (Chan.var_Chan c, .node (Chan.var_Chan dkx)
                                    (N.eval (.close true (Term.chan (.var_Chan dkx))))
                                    msk qsk) :: rr) qs)
                                = chanIndex (Chan.var_Chan c) ::ₘ
                                    chanIndex (Chan.var_Chan dkx) ::ₘ
                                    treeChansM (.root (M.eval (.pure .one)) (l ++ rr)
                                      (qs ++ [Tree.root (N.eval (.pure .one)) msk qsk])) := by
                              simp only [treeChansM_root, treeChansM_node, childChansM_append,
                                childChansM_cons, subChansM_append, subChansM_cons, subChansM_nil,
                                add_zero, ← Multiset.singleton_add]
                              abel
                            rw [e]
                            exact (Multiset.le_cons_self _ _).trans (Multiset.le_cons_self _ _)
                        | true =>
                            simp only [Bool.not_true]
                            refine .inr ⟨_, Step.rootClose, newChansAvoid_of_le ?_⟩
                            have e : treeChansM (.root
                                  (M.eval (.close true (Term.chan (.var_Chan c))))
                                  (l ++ (Chan.var_Chan c, .node (Chan.var_Chan dkx)
                                    (N.eval (.close false (Term.chan (.var_Chan dkx))))
                                    msk qsk) :: rr) qs)
                                = chanIndex (Chan.var_Chan c) ::ₘ
                                    chanIndex (Chan.var_Chan dkx) ::ₘ
                                    treeChansM (.root (M.eval (.pure .one)) (l ++ rr)
                                      (qs ++ [Tree.root (N.eval (.pure .one)) msk qsk])) := by
                              simp only [treeChansM_root, treeChansM_node, childChansM_append,
                                childChansM_cons, subChansM_append, subChansM_cons, subChansM_nil,
                                add_zero, ← Multiset.singleton_add]
                              abel
                            rw [e]
                            exact (Multiset.le_cons_self _ _).trans (Multiset.le_cons_self _ _)
                    · -- the selected child steps: Root-Child
                      have esrc : treeChansM (.root
                            (M.eval (.close b (.chan (.var_Chan c))))
                            (l ++ (Chan.var_Chan c, child) :: rr) qs)
                          = (chanIndex (Chan.var_Chan c) ::ₘ 0
                              + (childChansM l + childChansM rr + subChansM qs))
                            + treeChansM child := by
                        simp only [treeChansM_root, childChansM_append, childChansM_cons,
                          ← Multiset.singleton_add]
                        abel
                      have etgt : treeChansM (.root
                            (M.eval (.close b (.chan (.var_Chan c))))
                            (l ++ (Chan.var_Chan c, child') :: rr) qs)
                          = (chanIndex (Chan.var_Chan c) ::ₘ 0
                              + (childChansM l + childChansM rr + subChansM qs))
                            + treeChansM child' := by
                        simp only [treeChansM_root, childChansM_append, childChansM_cons,
                          ← Multiset.singleton_add]
                        abel
                      obtain ⟨hsa, houter⟩ := newChansAvoid_congr esrc etgt hav
                      exact .inr ⟨_, Step.rootChild st hsa, houter⟩
            · -- the root computation steps: Root-Expr
              refine .inr ⟨_, Step.rootExpr dst, newChansAvoid_of_eq ?_⟩
              simp only [treeChansM_root]
          · -- a detached subtree steps: Root-SubTree
            have esrc : treeChansM (.root m ms (l ++ q :: rr))
                = (childChansM ms + subChansM l + subChansM rr) + treeChansM q := by
              simp only [treeChansM_root, subChansM_append, subChansM_cons]
              abel
            have etgt : treeChansM (.root m ms (l ++ q' :: rr))
                = (childChansM ms + subChansM l + subChansM rr) + treeChansM q' := by
              simp only [treeChansM_root, subChansM_append, subChansM_cons]
              abel
            obtain ⟨hsa, houter⟩ := newChansAvoid_congr esrc etgt hav
            exact .inr ⟨_, Step.rootSubtree st hsa, houter⟩
      | node p m ms qs =>
          refine ⟨fun ty => (by cases ty), fun r A ty => ?_⟩
          cases ty with
          | @node Θ y _ _ _ _ _ single has tym tyms tyqs =>
          simp only [treeMeasure] at hle
          -- (1) sweep the detached subtrees
          rcases subtrees_progress (treeChans (.node (.var_Chan y) m ms qs) ++ avoid)
              (fun q hq => tyqs.typed_of_mem hq)
              (fun q hq typ =>
                (ihn q (by have := treeMeasure_le_subMeasure hq; omega) _).1 typ) with
            hallTerm | ⟨l, q, rr, q', rfl, st, hav⟩
          · -- (2) analyze the node computation
            rcases TLLC.Dynamic.Typed.progress tym with hval | ⟨m', dst⟩
            · -- (3) values: a node can never finish
              rcases tym.monad_canonical hval ARS.Conv.refl with ⟨u, vu, rfl⟩ | hthunk
              · exfalso
                have hone : u = .one := (pure_inv tym).unit_canonical vu ARS.Conv.refl
                subst hone
                have h1 := tym.occurs1 (PHas.pos_true has)
                simp [occurs] at h1
              · -- (5) thunks: decompose into an evaluation context and a partial redex
                obtain ⟨M, redex, rfl, hpart⟩ := hthunk.evalctx
                cases hpart with
                | @fork A' body =>
                    -- mint two fresh channels above the context, the tree, and the avoid set
                    have hlen : Θ.length < freshIndex (Θ.length ::
                        (treeChans (.node (.var_Chan y) (M.eval (.fork A' body)) ms qs)
                          ++ avoid)) :=
                      lt_freshIndex (by simp)
                    have htree : ∀ x ∈ treeChans
                          (.node (.var_Chan y) (M.eval (.fork A' body)) ms qs),
                        x < freshIndex (Θ.length ::
                          (treeChans (.node (.var_Chan y) (M.eval (.fork A' body)) ms qs)
                            ++ avoid)) :=
                      fun x hx => lt_freshIndex (by simp [hx])
                    have havd : ∀ x ∈ avoid, x < freshIndex (Θ.length ::
                        (treeChans (.node (.var_Chan y) (M.eval (.fork A' body)) ms qs)
                          ++ avoid)) :=
                      fun x hx => lt_freshIndex (by simp [hx])
                    set cI := freshIndex (Θ.length ::
                      (treeChans (.node (.var_Chan y) (M.eval (.fork A' body)) ms qs)
                        ++ avoid)) with hcI
                    by_cases hocc : occurs y body = 0
                    · -- fork body avoids the parent endpoint: Node-Fork
                      refine .inr ⟨_, Step.nodeFork (c := .var_Chan cI)
                        (d := .var_Chan (cI + 1)) ?_ ?_ hocc ?_, ?_⟩
                      · exact occurs_ge_length tym (by omega)
                      · exact occurs_ge_length tym (by omega)
                      · refine ⟨fun h => ?_, fun h => ?_, ?_⟩
                        · have := htree _ h
                          simp [chanIndex] at this
                        · have := htree _ h
                          simp [chanIndex] at this
                        · simp only [chanIndex]
                          omega
                      · refine newChansAvoid_of_cons₂ (c := cI) (d := cI + 1) ?_ ?_ ?_
                        · simp only [forkChildren, childChansM_insertChild, treeChansM_node,
                            subChansM_nil, add_zero, chanIndex, ← Multiset.singleton_add]
                          rw [← childChansM_split body ms]
                          abel
                        · intro h
                          have := havd _ h
                          omega
                        · intro h
                          have := havd _ h
                          omega
                    · -- fork body captures the parent endpoint: Node-Fork-Forward
                      refine .inr ⟨_, Step.nodeForkForward (c := .var_Chan cI)
                        (d := .var_Chan (cI + 1)) ?_ ?_ hocc ?_, ?_⟩
                      · exact occurs_ge_length tym (by omega)
                      · exact occurs_ge_length tym (by omega)
                      · refine ⟨fun h => ?_, fun h => ?_, ?_⟩
                        · have := htree _ h
                          simp [chanIndex] at this
                        · have := htree _ h
                          simp [chanIndex] at this
                        · simp only [chanIndex]
                          omega
                      · refine newChansAvoid_of_cons₂ (c := cI) (d := cI + 1) ?_ ?_ ?_
                        · simp only [forkForwardChildren, childChansM_insertChild,
                            treeChansM_node, subChansM_nil, add_zero, chanIndex,
                            ← Multiset.singleton_add]
                          rw [← childChansM_split body ms]
                          abel
                        · intro h
                          have := havd _ h
                          omega
                        · intro h
                          have := havd _ h
                          omega
                | @recv c i =>
                    -- session type of the receiving channel
                    obtain ⟨Θ1, Θ2, A0, mrg, tyRecv, cont⟩ := evalCtx_inv tym
                    have hInv : ∃ rr1 rr2 AAr BBr,
                        xor rr1 rr2 = false ∧
                        (Θ1 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
                          .chan (.var_Chan c) : .ch rr1 (.act rr2 AAr BBr i)) := by
                      cases i
                      · obtain ⟨rr1, rr2, AAr, BBr, hx, _, tyChan⟩ := recvIm_inv tyRecv
                        exact ⟨rr1, rr2, AAr, BBr, hx, tyChan⟩
                      · obtain ⟨rr1, rr2, AAr, BBr, hx, _, tyChan⟩ := recvEx_inv tyRecv
                        exact ⟨rr1, rr2, AAr, BBr, hx, tyChan⟩
                    obtain ⟨rr1, rr2, AAr, BBr, xorR, tyChanR⟩ := hInv
                    obtain ⟨r1, A1, just, _, eqCh⟩ := chan_inv tyChanR
                    rw [cren_len_nil] at eqCh
                    obtain ⟨er, eAct⟩ := Static.ch_inj eqCh
                    subst er
                    have posC : CvarPos Θ c true :=
                      CvarPos.merge_true_left single mrg (just.pos_true.mpr rfl)
                    rcases ChildrenTypedAt.label_of_pos tyms posC with hlabel | hcy
                    · -- a child edge: communicate with the child
                      obtain ⟨⟨ck, child⟩, hmem, hck⟩ := List.mem_map.mp hlabel
                      simp only at hck
                      subst hck
                      obtain ⟨l, rr, hms⟩ := List.append_of_mem hmem
                      subst hms
                      obtain ⟨C, tyChild, hC, tyRest⟩ :=
                        ChildrenTypedAt.remove just mrg tyms rfl rfl
                      have hmeas : treeMeasure child ≤ n := by
                        have h := treeMeasure_le_childMeasure
                          (c := Chan.var_Chan c) (child := child)
                          (ms := l ++ (Chan.var_Chan c, child) :: rr) (by simp)
                        omega
                      rcases (ihn child hmeas
                          (treeChans (.node (.var_Chan y)
                            (M.eval (.recv (.chan (.var_Chan c)) i))
                            (l ++ (Chan.var_Chan c, child) :: rr) qs) ++ avoid)).2 _ _
                          tyChild with ⟨dk, hpoised⟩ | ⟨child', st, hav⟩
                      · -- the child is poised: duality forces the matching send
                        cases hpoised with
                        | @node mk msk qsk hpm =>
                        obtain ⟨N, redex', hmk, hredex⟩ := hpm.evalctx
                        subst hmk
                        cases tyChild with
                        | @node Θk dkx _ _ _ _ _ singlek hask tymk tymsk tyqsk =>
                        obtain ⟨Θk1, Θk2, A0k, mrgk, tyRedex, _⟩ := evalCtx_inv tymk
                        rcases poisedRedex_dispatch hredex singlek mrgk hask tyRedex with
                          ⟨r2', A', B', i', hCact, hxor', _⟩ |
                          ⟨r2', A', B', i', v, hCact, _, hvalFn, _, hredexEq⟩ |
                          ⟨hCstop, _⟩
                        · -- the child also receives: polarity clash
                          exfalso
                          have hActs : Term.act r2' A' B' i' ≃ .act rr2 AAr BBr i :=
                            ARS.conv_trans (ARS.conv_sym hCact)
                              (ARS.conv_trans hC (ARS.conv_sym eAct))
                          obtain ⟨_, _, hr2, _⟩ := Static.act_inj hActs
                          rw [hr2] at hxor'
                          cases rr1 <;> cases rr2 <;> simp_all
                        · -- the child sends: fire the com
                          have hActs : Term.act r2' A' B' i' ≃ .act rr2 AAr BBr i :=
                            ARS.conv_trans (ARS.conv_sym hCact)
                              (ARS.conv_trans hC (ARS.conv_sym eAct))
                          obtain ⟨_, _, hr2, hi⟩ := Static.act_inj hActs
                          rw [hi] at hredexEq
                          subst hredexEq
                          cases i with
                          | ex =>
                              refine .inr ⟨_, Step.nodeRecvEx (hvalFn hi),
                                newChansAvoid_of_eq ?_⟩
                              have e3 : childChansM (splitChildrenByTerm v msk).1
                                    + childChansM (splitChildrenByTerm v msk).2
                                  = childChansM msk := childChansM_split v msk
                              have e1 : treeChansM (.node (.var_Chan y)
                                    (M.eval (.pure (.pair v (Term.chan (.var_Chan c)) .ex .L)))
                                    (recvExChildren v (.var_Chan c) (.var_Chan dkx) N msk qsk
                                      (l ++ rr)) qs)
                                  = (childChansM (splitChildrenByTerm v msk).1
                                      + childChansM (splitChildrenByTerm v msk).2)
                                    + ({chanIndex (Chan.var_Chan y)}
                                        + {chanIndex (Chan.var_Chan c)}
                                        + {chanIndex (Chan.var_Chan dkx)} + childChansM l
                                        + childChansM rr + subChansM qsk + subChansM qs) := by
                                simp only [recvExChildren, treeChansM_root, treeChansM_node,
                                  childChansM_insertChild, childChansM_mergeChildren,
                                  childChansM_append, ← Multiset.singleton_add]
                                abel
                              have e2 : treeChansM (.node (.var_Chan y)
                                    (M.eval (.recv (.chan (.var_Chan c)) .ex))
                                    (l ++ (Chan.var_Chan c, .node (Chan.var_Chan dkx)
                                      (N.eval (.app (.send (Term.chan (.var_Chan dkx)) .ex)
                                        v .ex)) msk qsk) :: rr) qs)
                                  = childChansM msk
                                    + ({chanIndex (Chan.var_Chan y)}
                                        + {chanIndex (Chan.var_Chan c)}
                                        + {chanIndex (Chan.var_Chan dkx)} + childChansM l
                                        + childChansM rr + subChansM qsk + subChansM qs) := by
                                simp only [treeChansM_root, treeChansM_node, childChansM_append,
                                  childChansM_cons, ← Multiset.singleton_add]
                                abel
                              rw [e1, e3, e2]
                          | im =>
                              refine .inr ⟨_, Step.nodeRecvIm, newChansAvoid_of_eq ?_⟩
                              simp only [treeChansM_root, treeChansM_node, childChansM_append,
                                childChansM_cons]
                        · -- the child is finished: protocol clash
                          exfalso
                          have hbad : Term.act rr2 AAr BBr i ≃ .stop :=
                            ARS.conv_trans eAct
                              (ARS.conv_trans (ARS.conv_sym hC) hCstop)
                          false_conv
                      · -- the selected child steps: Node-Child
                        have esrc : treeChansM (.node (.var_Chan y)
                              (M.eval (.recv (.chan (.var_Chan c)) i))
                              (l ++ (Chan.var_Chan c, child) :: rr) qs)
                            = (chanIndex (Chan.var_Chan y) ::ₘ
                                chanIndex (Chan.var_Chan c) ::ₘ 0
                                + (childChansM l + childChansM rr + subChansM qs))
                              + treeChansM child := by
                          simp only [treeChansM_node, childChansM_append, childChansM_cons,
                            ← Multiset.singleton_add]
                          abel
                        have etgt : treeChansM (.node (.var_Chan y)
                              (M.eval (.recv (.chan (.var_Chan c)) i))
                              (l ++ (Chan.var_Chan c, child') :: rr) qs)
                            = (chanIndex (Chan.var_Chan y) ::ₘ
                                chanIndex (Chan.var_Chan c) ::ₘ 0
                                + (childChansM l + childChansM rr + subChansM qs))
                              + treeChansM child' := by
                          simp only [treeChansM_node, childChansM_append, childChansM_cons,
                            ← Multiset.singleton_add]
                          abel
                        obtain ⟨hsa, houter⟩ := newChansAvoid_congr esrc etgt hav
                        exact .inr ⟨_, Step.nodeChild st hsa, houter⟩
                    · -- the parent endpoint: the node is poised
                      subst hcy
                      cases i with
                      | im =>
                          exact .inl ⟨_, PoisedAt.node
                            (Poised.plug M (Poised.redex PoisedRedex.recvIm))⟩
                      | ex =>
                          exact .inl ⟨_, PoisedAt.node
                            (Poised.plug M (Poised.redex PoisedRedex.recvEx))⟩
                | @appSendIm c o =>
                    -- session type of the sending channel
                    obtain ⟨Θ1, Θ2, A0, mrg, tyApp, cont⟩ := evalCtx_inv tym
                    obtain ⟨A_, B_, s_, tySend, _, _⟩ := appIm_inv tyApp
                    obtain ⟨rs1, rs2, AAs, BBs, xorS, _, tyChanS⟩ := sendIm_inv tySend
                    obtain ⟨r1, A1, just, _, eqCh⟩ := chan_inv tyChanS
                    rw [cren_len_nil] at eqCh
                    obtain ⟨er, eAct⟩ := Static.ch_inj eqCh
                    subst er
                    have posC : CvarPos Θ c true :=
                      CvarPos.merge_true_left single mrg (just.pos_true.mpr rfl)
                    rcases ChildrenTypedAt.label_of_pos tyms posC with hlabel | hcy
                    · -- a child edge: communicate with the child
                      obtain ⟨⟨ck, child⟩, hmem, hck⟩ := List.mem_map.mp hlabel
                      simp only at hck
                      subst hck
                      obtain ⟨l, rr, hms⟩ := List.append_of_mem hmem
                      subst hms
                      obtain ⟨C, tyChild, hC, tyRest⟩ :=
                        ChildrenTypedAt.remove just mrg tyms rfl rfl
                      have hmeas : treeMeasure child ≤ n := by
                        have h := treeMeasure_le_childMeasure
                          (c := Chan.var_Chan c) (child := child)
                          (ms := l ++ (Chan.var_Chan c, child) :: rr) (by simp)
                        omega
                      rcases (ihn child hmeas
                          (treeChans (.node (.var_Chan y)
                            (M.eval (.app (.send (.chan (.var_Chan c)) .im) o .im))
                            (l ++ (Chan.var_Chan c, child) :: rr) qs) ++ avoid)).2 _ _
                          tyChild with ⟨dk, hpoised⟩ | ⟨child', st, hav⟩
                      · -- the child is poised: duality forces the matching receive
                        cases hpoised with
                        | @node mk msk qsk hpm =>
                        obtain ⟨N, redex', hmk, hredex⟩ := hpm.evalctx
                        subst hmk
                        cases tyChild with
                        | @node Θk dkx _ _ _ _ _ singlek hask tymk tymsk tyqsk =>
                        obtain ⟨Θk1, Θk2, A0k, mrgk, tyRedex, _⟩ := evalCtx_inv tymk
                        rcases poisedRedex_dispatch hredex singlek mrgk hask tyRedex with
                          ⟨r2', A', B', i', hCact, _, hredexEq⟩ |
                          ⟨r2', A', B', i', v, hCact, hxor', _, _, _⟩ |
                          ⟨hCstop, _⟩
                        · -- the child receives: fire the com
                          have hActs : Term.act r2' A' B' i' ≃ .act rs2 AAs BBs .im :=
                            ARS.conv_trans (ARS.conv_sym hCact)
                              (ARS.conv_trans hC (ARS.conv_sym eAct))
                          obtain ⟨_, _, _, hi⟩ := Static.act_inj hActs
                          rw [hi] at hredexEq
                          subst hredexEq
                          refine .inr ⟨_, Step.nodeSendIm, newChansAvoid_of_eq ?_⟩
                          simp only [treeChansM_root, treeChansM_node, childChansM_append,
                            childChansM_cons]
                        · -- the child also sends: polarity clash
                          exfalso
                          have hActs : Term.act r2' A' B' i' ≃ .act rs2 AAs BBs .im :=
                            ARS.conv_trans (ARS.conv_sym hCact)
                              (ARS.conv_trans hC (ARS.conv_sym eAct))
                          obtain ⟨_, _, hr2, _⟩ := Static.act_inj hActs
                          rw [hr2] at hxor'
                          cases rs1 <;> cases rs2 <;> simp_all
                        · -- the child is finished: protocol clash
                          exfalso
                          have hbad : Term.act rs2 AAs BBs .im ≃ .stop :=
                            ARS.conv_trans eAct
                              (ARS.conv_trans (ARS.conv_sym hC) hCstop)
                          false_conv
                      · -- the selected child steps: Node-Child
                        have esrc : treeChansM (.node (.var_Chan y)
                              (M.eval (.app (.send (.chan (.var_Chan c)) .im) o .im))
                              (l ++ (Chan.var_Chan c, child) :: rr) qs)
                            = (chanIndex (Chan.var_Chan y) ::ₘ
                                chanIndex (Chan.var_Chan c) ::ₘ 0
                                + (childChansM l + childChansM rr + subChansM qs))
                              + treeChansM child := by
                          simp only [treeChansM_node, childChansM_append, childChansM_cons,
                            ← Multiset.singleton_add]
                          abel
                        have etgt : treeChansM (.node (.var_Chan y)
                              (M.eval (.app (.send (.chan (.var_Chan c)) .im) o .im))
                              (l ++ (Chan.var_Chan c, child') :: rr) qs)
                            = (chanIndex (Chan.var_Chan y) ::ₘ
                                chanIndex (Chan.var_Chan c) ::ₘ 0
                                + (childChansM l + childChansM rr + subChansM qs))
                              + treeChansM child' := by
                          simp only [treeChansM_node, childChansM_append, childChansM_cons,
                            ← Multiset.singleton_add]
                          abel
                        obtain ⟨hsa, houter⟩ := newChansAvoid_congr esrc etgt hav
                        exact .inr ⟨_, Step.nodeChild st hsa, houter⟩
                    · -- the parent endpoint: the node is poised
                      subst hcy
                      exact .inl ⟨_, PoisedAt.node
                        (Poised.plug M (Poised.redex PoisedRedex.sendIm))⟩
                | @appSendEx c v value =>
                    -- session type of the sending channel
                    obtain ⟨Θ1, Θ2, A0, mrg, tyApp, cont⟩ := evalCtx_inv tym
                    obtain ⟨A_, B_, s_, Θs1, Θs2, Δ1, Δ2, mrgS, _, tySend, _, _⟩ :=
                      appEx_inv tyApp
                    obtain ⟨rs1, rs2, AAs, BBs, xorS, _, tyChanS⟩ := sendEx_inv tySend
                    obtain ⟨r1, A1, just, _, eqCh⟩ := chan_inv tyChanS
                    rw [cren_len_nil] at eqCh
                    obtain ⟨er, eAct⟩ := Static.ch_inj eqCh
                    subst er
                    obtain ⟨Θc', _, mrg2⟩ := PMerge.splitR mrg mrgS
                    have posC : CvarPos Θ c true :=
                      CvarPos.merge_true_left single mrg2.sym (just.pos_true.mpr rfl)
                    rcases ChildrenTypedAt.label_of_pos tyms posC with hlabel | hcy
                    · -- a child edge: communicate with the child
                      obtain ⟨⟨ck, child⟩, hmem, hck⟩ := List.mem_map.mp hlabel
                      simp only at hck
                      subst hck
                      obtain ⟨l, rr, hms⟩ := List.append_of_mem hmem
                      subst hms
                      obtain ⟨C, tyChild, hC, tyRest⟩ :=
                        ChildrenTypedAt.remove just mrg2.sym tyms rfl rfl
                      have hmeas : treeMeasure child ≤ n := by
                        have h := treeMeasure_le_childMeasure
                          (c := Chan.var_Chan c) (child := child)
                          (ms := l ++ (Chan.var_Chan c, child) :: rr) (by simp)
                        omega
                      rcases (ihn child hmeas
                          (treeChans (.node (.var_Chan y)
                            (M.eval (.app (.send (.chan (.var_Chan c)) .ex) v .ex))
                            (l ++ (Chan.var_Chan c, child) :: rr) qs) ++ avoid)).2 _ _
                          tyChild with ⟨dk, hpoised⟩ | ⟨child', st, hav⟩
                      · -- the child is poised: duality forces the matching receive
                        cases hpoised with
                        | @node mk msk qsk hpm =>
                        obtain ⟨N, redex', hmk, hredex⟩ := hpm.evalctx
                        subst hmk
                        cases tyChild with
                        | @node Θk dkx _ _ _ _ _ singlek hask tymk tymsk tyqsk =>
                        obtain ⟨Θk1, Θk2, A0k, mrgk, tyRedex, _⟩ := evalCtx_inv tymk
                        rcases poisedRedex_dispatch hredex singlek mrgk hask tyRedex with
                          ⟨r2', A', B', i', hCact, _, hredexEq⟩ |
                          ⟨r2', A', B', i', w, hCact, hxor', _, _, _⟩ |
                          ⟨hCstop, _⟩
                        · -- the child receives: send or forward on the parent occurrence
                          have hActs : Term.act r2' A' B' i' ≃ .act rs2 AAs BBs .ex :=
                            ARS.conv_trans (ARS.conv_sym hCact)
                              (ARS.conv_trans hC (ARS.conv_sym eAct))
                          obtain ⟨_, _, _, hi⟩ := Static.act_inj hActs
                          rw [hi] at hredexEq
                          subst hredexEq
                          by_cases hocc : occurs y v = 0
                          · -- the payload avoids the parent endpoint: Node-Send
                            refine .inr ⟨_, Step.nodeSendEx value hocc,
                              newChansAvoid_of_eq ?_⟩
                            have e3 : childChansM (splitChildrenByTerm v (l ++ rr)).1
                                  + childChansM (splitChildrenByTerm v (l ++ rr)).2
                                = childChansM l + childChansM rr := by
                              rw [childChansM_split, childChansM_append]
                            have e1 : treeChansM (.node (.var_Chan y)
                                  (M.eval (.pure (Term.chan (.var_Chan c))))
                                  (sendExChildren v (.var_Chan c) (.var_Chan dkx) N msk qsk
                                    (l ++ rr)) qs)
                                = (childChansM (splitChildrenByTerm v (l ++ rr)).1
                                    + childChansM (splitChildrenByTerm v (l ++ rr)).2)
                                  + ({chanIndex (Chan.var_Chan y)}
                                      + {chanIndex (Chan.var_Chan c)}
                                      + {chanIndex (Chan.var_Chan dkx)} + childChansM msk
                                      + subChansM qsk + subChansM qs) := by
                              simp only [sendExChildren, treeChansM_root, treeChansM_node,
                                childChansM_insertChild, childChansM_mergeChildren,
                                ← Multiset.singleton_add]
                              abel
                            have e2 : treeChansM (.node (.var_Chan y)
                                  (M.eval (.app (.send (.chan (.var_Chan c)) .ex) v .ex))
                                  (l ++ (Chan.var_Chan c, .node (Chan.var_Chan dkx)
                                    (N.eval (.recv (Term.chan (.var_Chan dkx)) .ex))
                                    msk qsk) :: rr) qs)
                                = (childChansM l + childChansM rr)
                                  + ({chanIndex (Chan.var_Chan y)}
                                      + {chanIndex (Chan.var_Chan c)}
                                      + {chanIndex (Chan.var_Chan dkx)} + childChansM msk
                                      + subChansM qsk + subChansM qs) := by
                              simp only [treeChansM_root, treeChansM_node, childChansM_append,
                                childChansM_cons, ← Multiset.singleton_add]
                              abel
                            rw [e1, e3, e2]
                          · -- the payload captures the parent endpoint: Node-Forward
                            refine .inr ⟨_, Step.nodeForward value hocc,
                              newChansAvoid_of_eq ?_⟩
                            have e3 : childChansM (splitChildrenByTerm v (l ++ rr)).1
                                  + childChansM (splitChildrenByTerm v (l ++ rr)).2
                                = childChansM l + childChansM rr := by
                              rw [childChansM_split, childChansM_append]
                            have e1 : treeChansM (.node (.var_Chan y)
                                  (N.eval (.pure (.pair v (Term.chan (.var_Chan dkx)) .ex .L)))
                                  (forwardChildren v (.var_Chan c) (.var_Chan dkx) M msk
                                    (l ++ rr) qs) qsk)
                                = (childChansM (splitChildrenByTerm v (l ++ rr)).1
                                    + childChansM (splitChildrenByTerm v (l ++ rr)).2)
                                  + ({chanIndex (Chan.var_Chan y)}
                                      + {chanIndex (Chan.var_Chan c)}
                                      + {chanIndex (Chan.var_Chan dkx)} + childChansM msk
                                      + subChansM qsk + subChansM qs) := by
                              simp only [forwardChildren, treeChansM_root, treeChansM_node,
                                childChansM_insertChild, childChansM_mergeChildren,
                                ← Multiset.singleton_add]
                              abel
                            have e2 : treeChansM (.node (.var_Chan y)
                                  (M.eval (.app (.send (.chan (.var_Chan c)) .ex) v .ex))
                                  (l ++ (Chan.var_Chan c, .node (Chan.var_Chan dkx)
                                    (N.eval (.recv (Term.chan (.var_Chan dkx)) .ex))
                                    msk qsk) :: rr) qs)
                                = (childChansM l + childChansM rr)
                                  + ({chanIndex (Chan.var_Chan y)}
                                      + {chanIndex (Chan.var_Chan c)}
                                      + {chanIndex (Chan.var_Chan dkx)} + childChansM msk
                                      + subChansM qsk + subChansM qs) := by
                              simp only [treeChansM_root, treeChansM_node, childChansM_append,
                                childChansM_cons, ← Multiset.singleton_add]
                              abel
                            rw [e1, e3, e2]
                        · -- the child also sends: polarity clash
                          exfalso
                          have hActs : Term.act r2' A' B' i' ≃ .act rs2 AAs BBs .ex :=
                            ARS.conv_trans (ARS.conv_sym hCact)
                              (ARS.conv_trans hC (ARS.conv_sym eAct))
                          obtain ⟨_, _, hr2, _⟩ := Static.act_inj hActs
                          rw [hr2] at hxor'
                          cases rs1 <;> cases rs2 <;> simp_all
                        · -- the child is finished: protocol clash
                          exfalso
                          have hbad : Term.act rs2 AAs BBs .ex ≃ .stop :=
                            ARS.conv_trans eAct
                              (ARS.conv_trans (ARS.conv_sym hC) hCstop)
                          false_conv
                      · -- the selected child steps: Node-Child
                        have esrc : treeChansM (.node (.var_Chan y)
                              (M.eval (.app (.send (.chan (.var_Chan c)) .ex) v .ex))
                              (l ++ (Chan.var_Chan c, child) :: rr) qs)
                            = (chanIndex (Chan.var_Chan y) ::ₘ
                                chanIndex (Chan.var_Chan c) ::ₘ 0
                                + (childChansM l + childChansM rr + subChansM qs))
                              + treeChansM child := by
                          simp only [treeChansM_node, childChansM_append, childChansM_cons,
                            ← Multiset.singleton_add]
                          abel
                        have etgt : treeChansM (.node (.var_Chan y)
                              (M.eval (.app (.send (.chan (.var_Chan c)) .ex) v .ex))
                              (l ++ (Chan.var_Chan c, child') :: rr) qs)
                            = (chanIndex (Chan.var_Chan y) ::ₘ
                                chanIndex (Chan.var_Chan c) ::ₘ 0
                                + (childChansM l + childChansM rr + subChansM qs))
                              + treeChansM child' := by
                          simp only [treeChansM_node, childChansM_append, childChansM_cons,
                            ← Multiset.singleton_add]
                          abel
                        obtain ⟨hsa, houter⟩ := newChansAvoid_congr esrc etgt hav
                        exact .inr ⟨_, Step.nodeChild st hsa, houter⟩
                    · -- the parent endpoint: the node is poised
                      subst hcy
                      exact .inl ⟨_, PoisedAt.node
                        (Poised.plug M (Poised.redex (PoisedRedex.sendEx value)))⟩
                | @close b c =>
                    -- locate the closing channel: a child edge or the parent endpoint
                    obtain ⟨Θ1, Θ2, A0, mrg, tyClose, cont⟩ := evalCtx_inv tym
                    have hinv : (Term.M A0 ≃ Term.M .unit) ∧
                        (Θ1 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
                          .chan (Chan.var_Chan c) : .ch b .stop) := by
                      cases b
                      · exact wait_inv tyClose
                      · exact close_inv tyClose
                    obtain ⟨r1, A1, just, _, eqCh⟩ := chan_inv hinv.2
                    rw [cren_len_nil] at eqCh
                    obtain ⟨er, eStop⟩ := Static.ch_inj eqCh
                    subst er
                    have posC : CvarPos Θ c true :=
                      CvarPos.merge_true_left single mrg (just.pos_true.mpr rfl)
                    rcases ChildrenTypedAt.label_of_pos tyms posC with hlabel | hcy
                    · -- a child edge: communicate with the child
                      obtain ⟨⟨ck, child⟩, hmem, hck⟩ := List.mem_map.mp hlabel
                      simp only at hck
                      subst hck
                      obtain ⟨l, rr, hms⟩ := List.append_of_mem hmem
                      subst hms
                      obtain ⟨C, tyChild, hC, tyRest⟩ :=
                        ChildrenTypedAt.remove just mrg tyms rfl rfl
                      have hmeas : treeMeasure child ≤ n := by
                        have h := treeMeasure_le_childMeasure
                          (c := Chan.var_Chan c) (child := child)
                          (ms := l ++ (Chan.var_Chan c, child) :: rr) (by simp)
                        omega
                      rcases (ihn child hmeas
                          (treeChans (.node (.var_Chan y)
                            (M.eval (.close b (.chan (.var_Chan c))))
                            (l ++ (Chan.var_Chan c, child) :: rr) qs) ++ avoid)).2 _ _
                          tyChild with ⟨dk, hpoised⟩ | ⟨child', st, hav⟩
                      · -- the child is poised: duality forces the matching close
                        cases hpoised with
                        | @node mk msk qsk hpm =>
                        obtain ⟨N, redex', hmk, hredex⟩ := hpm.evalctx
                        subst hmk
                        cases tyChild with
                        | @node Θk dkx _ _ _ _ _ singlek hask tymk tymsk tyqsk =>
                        obtain ⟨Θk1, Θk2, A0k, mrgk, tyRedex, _⟩ := evalCtx_inv tymk
                        rcases poisedRedex_dispatch hredex singlek mrgk hask tyRedex with
                          ⟨r2, A', B', i, hCact, _, _⟩ | ⟨r2, A', B', i, v, hCact, _, _, _, _⟩ |
                          ⟨hCstop, hredexEq⟩
                        · exfalso
                          have hbad : Term.act r2 A' B' i ≃ .stop :=
                            ARS.conv_trans (ARS.conv_sym hCact)
                              (ARS.conv_trans hC (ARS.conv_sym eStop))
                          false_conv
                        · exfalso
                          have hbad : Term.act r2 A' B' i ≃ .stop :=
                            ARS.conv_trans (ARS.conv_sym hCact)
                              (ARS.conv_trans hC (ARS.conv_sym eStop))
                          false_conv
                        · -- fire the END step
                          subst hredexEq
                          cases b with
                          | false =>
                              simp only [Bool.not_false]
                              refine .inr ⟨_, Step.nodeWait, newChansAvoid_of_le ?_⟩
                              have e : treeChansM (.node (.var_Chan y)
                                    (M.eval (.close false (Term.chan (.var_Chan c))))
                                    (l ++ (Chan.var_Chan c, .node (Chan.var_Chan dkx)
                                      (N.eval (.close true (Term.chan (.var_Chan dkx))))
                                      msk qsk) :: rr) qs)
                                  = chanIndex (Chan.var_Chan c) ::ₘ
                                      chanIndex (Chan.var_Chan dkx) ::ₘ
                                      treeChansM (.node (.var_Chan y)
                                        (M.eval (.pure .one)) (l ++ rr)
                                        (qs ++ [Tree.root (N.eval (.pure .one)) msk qsk])) := by
                                simp only [treeChansM_root, treeChansM_node, childChansM_append,
                                  childChansM_cons, subChansM_append, subChansM_cons,
                                  subChansM_nil, add_zero, ← Multiset.singleton_add]
                                abel
                              rw [e]
                              exact (Multiset.le_cons_self _ _).trans (Multiset.le_cons_self _ _)
                          | true =>
                              simp only [Bool.not_true]
                              refine .inr ⟨_, Step.nodeClose, newChansAvoid_of_le ?_⟩
                              have e : treeChansM (.node (.var_Chan y)
                                    (M.eval (.close true (Term.chan (.var_Chan c))))
                                    (l ++ (Chan.var_Chan c, .node (Chan.var_Chan dkx)
                                      (N.eval (.close false (Term.chan (.var_Chan dkx))))
                                      msk qsk) :: rr) qs)
                                  = chanIndex (Chan.var_Chan c) ::ₘ
                                      chanIndex (Chan.var_Chan dkx) ::ₘ
                                      treeChansM (.node (.var_Chan y)
                                        (M.eval (.pure .one)) (l ++ rr)
                                        (qs ++ [Tree.root (N.eval (.pure .one)) msk qsk])) := by
                                simp only [treeChansM_root, treeChansM_node, childChansM_append,
                                  childChansM_cons, subChansM_append, subChansM_cons,
                                  subChansM_nil, add_zero, ← Multiset.singleton_add]
                                abel
                              rw [e]
                              exact (Multiset.le_cons_self _ _).trans (Multiset.le_cons_self _ _)
                      · -- the selected child steps: Node-Child
                        have esrc : treeChansM (.node (.var_Chan y)
                              (M.eval (.close b (.chan (.var_Chan c))))
                              (l ++ (Chan.var_Chan c, child) :: rr) qs)
                            = (chanIndex (Chan.var_Chan y) ::ₘ
                                chanIndex (Chan.var_Chan c) ::ₘ 0
                                + (childChansM l + childChansM rr + subChansM qs))
                              + treeChansM child := by
                          simp only [treeChansM_node, childChansM_append, childChansM_cons,
                            ← Multiset.singleton_add]
                          abel
                        have etgt : treeChansM (.node (.var_Chan y)
                              (M.eval (.close b (.chan (.var_Chan c))))
                              (l ++ (Chan.var_Chan c, child') :: rr) qs)
                            = (chanIndex (Chan.var_Chan y) ::ₘ
                                chanIndex (Chan.var_Chan c) ::ₘ 0
                                + (childChansM l + childChansM rr + subChansM qs))
                              + treeChansM child' := by
                          simp only [treeChansM_node, childChansM_append, childChansM_cons,
                            ← Multiset.singleton_add]
                          abel
                        obtain ⟨hsa, houter⟩ := newChansAvoid_congr esrc etgt hav
                        exact .inr ⟨_, Step.nodeChild st hsa, houter⟩
                    · -- the parent endpoint: the node is poised
                      subst hcy
                      cases b with
                      | false =>
                          exact .inl ⟨_, PoisedAt.node
                            (Poised.plug M (Poised.redex PoisedRedex.wait))⟩
                      | true =>
                          exact .inl ⟨_, PoisedAt.node
                            (Poised.plug M (Poised.redex PoisedRedex.close))⟩
            · -- the node computation steps: Node-Expr
              refine .inr ⟨_, Step.nodeExpr dst, newChansAvoid_of_eq ?_⟩
              simp only [treeChansM_node]
          · -- a detached subtree steps: Node-SubTree
            have esrc : treeChansM (.node (.var_Chan y) m ms (l ++ q :: rr))
                = (chanIndex (Chan.var_Chan y) ::ₘ 0
                    + (childChansM ms + subChansM l + subChansM rr)) + treeChansM q := by
              simp only [treeChansM_node, subChansM_append, subChansM_cons,
                ← Multiset.singleton_add]
              abel
            have etgt : treeChansM (.node (.var_Chan y) m ms (l ++ q' :: rr))
                = (chanIndex (Chan.var_Chan y) ::ₘ 0
                    + (childChansM ms + subChansM l + subChansM rr)) + treeChansM q' := by
              simp only [treeChansM_node, subChansM_append, subChansM_cons,
                ← Multiset.singleton_add]
              abel
            obtain ⟨hsa, houter⟩ := newChansAvoid_congr esrc etgt hav
            exact .inr ⟨_, Step.nodeSubtree st hsa, houter⟩

/-- Lemma 5.92 (Spawning Tree Progress), root half: a valid spawning tree is terminal or
reduces. -/
theorem Typed.progress {t : Tree} (ty : Typed t) :
    Terminal t ∨ ∃ t', Step t t' := by
  rcases (progress_mutual (treeMeasure t) t le_rfl []).1 ty with h | ⟨t', st, _⟩
  · exact .inl h
  · exact .inr ⟨t', st⟩

/-- Lemma 5.92, node half: a valid node tree is poised on its parent channel or reduces. -/
theorem TypedAt.progress {r : Bool} {A : Term} {t : Tree} (ty : TypedAt r A t) :
    (∃ d, PoisedAt d t) ∨ ∃ t', Step t t' := by
  rcases (progress_mutual (treeMeasure t) t le_rfl []).2 r A ty with h | ⟨t', st, _⟩
  · exact .inl h
  · exact .inr ⟨t', st⟩

end TLLC.Spawning
