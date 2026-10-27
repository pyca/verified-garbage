module

public import VerifiedGarbage.Proof.Framework.Fence
public import VerifiedGarbage.Proof.Framework.SpectreTaint

/-!
# Fences where they are needed

`Fence.lean` fences every branch target, which makes any constant-time code
speculatively constant time, at a cost (up to several times slower). Code
whose constant time the taint analysis proves needs no barrier at its
branches (`Taint.specConstantTime`, `SpectreTaint.lean`), only one before it
returns, so that a mispredicted branch does not return to its caller still
misspeculating, with transient stores of secrets in memory the caller reads
(`SpecSafe`). So each function chooses where its barriers go:

* `FenceIns f c' c`: `c'` is `c` with blocks of the barrier `f` inserted
  anywhere. It has the same runs (`Exec.fenceIns_iff`), so it stays verified
  (`Verified.fenceIns`), whatever the placement.
* `specSafe_fenceFn`: with a barrier at every branch target, any
  constant-time code is `SpecSafe`, for every transient semantics.
* `specSafe_taint`: code that the taint analysis checks, followed by a
  barrier, is `SpecSafe`, for a transient semantics for which the analysis
  is sound (`Taint.SpecSound`).
-/

@[expose] public section

namespace VG

/-- `c'` is `c` with blocks of the barrier `f` inserted, before or after any
part of it. -/
inductive FenceIns {I C : Type} (f : I) : Code I C → Code I C → Prop
  | refl (c : Code I C) : FenceIns f c c
  | seq {a a' b b'} : FenceIns f a' a → FenceIns f b' b → FenceIns f (.seq a' b') (.seq a b)
  | ite {c t t' e e'} : FenceIns f t' t → FenceIns f e' e → FenceIns f (.ite c t' e') (.ite c t e)
  | loop {b b' c} : FenceIns f b' b → FenceIns f (.loop b' c) (.loop b c)
  | call {n b b'} : FenceIns f b' b → FenceIns f (.call n b') (.call n b)
  | frame {i j b b'} : FenceIns f b' b → FenceIns f (.frame i b' j) (.frame i b j)
  | pre {c c'} : FenceIns f c' c → FenceIns f (.seq (.block [f]) c') c
  | post {c c'} : FenceIns f c' c → FenceIns f (.seq c' (.block [f])) c
  | trans {a b c} : FenceIns f a b → FenceIns f b c → FenceIns f a c

variable {M : ISA}

theorem FenceIns.fenceArm {f : M.Instr} {c c' : Prog M} (h : FenceIns f c' c) :
    FenceIns f (c'.fenceArm f) c := by
  refine .trans ?_ h
  unfold Code.fenceArm
  split
  · exact .seq (.refl _) (.pre (.refl _))
  · exact .pre (.refl _)

theorem FenceIns.fence (f : M.Instr) (c : Prog M) : FenceIns f (c.fence f) c := by
  induction c with
  | block => exact .refl _
  | seq _ _ ha hb => exact .seq ha hb
  | ite _ _ _ ht he => exact .ite ht.fenceArm he.fenceArm
  | loop _ _ hb => exact .post (.loop hb.fenceArm)
  | call _ _ hb => exact .call hb
  | frame _ _ _ hb => exact .frame hb

theorem FenceIns.fenceFn (f : M.Instr) (c : Prog M) : FenceIns f (c.fenceFn f) c :=
  .pre (.fence f c)

section Seq

variable {f : M.Instr} (hn : Nop M f)
include hn

/-- Code with barriers inserted has the same runs as the original. -/
theorem Exec.fenceIns_iff {c c' : Prog M} (h : FenceIns f c' c) {s s' : M.State}
    {t : List Leak} : Exec M c' s t s' ↔ Exec M c s t s' := by
  induction h generalizing s s' t with
  | refl => exact Iff.rfl
  | seq _ _ iha ihb =>
    constructor
    · intro e; cases e with | seq x y => exact .seq (iha.mp x) (ihb.mp y)
    · intro e; cases e with | seq x y => exact .seq (iha.mpr x) (ihb.mpr y)
  | ite _ _ iht ihe =>
    constructor
    · intro e
      cases e with
      | iteT hc x => exact .iteT hc (iht.mp x)
      | iteF hc x => exact .iteF hc (ihe.mp x)
    · intro e
      cases e with
      | iteT hc x => exact .iteT hc (iht.mpr x)
      | iteF hc x => exact .iteF hc (ihe.mpr x)
  | loop _ ih =>
    exact ⟨Exec.loop_congr fun _ _ _ x => ih.mp x, Exec.loop_congr fun _ _ _ x => ih.mpr x⟩
  | call _ ih =>
    constructor
    · intro e; cases e with | call h₁ x h₂ => exact .call h₁ (ih.mp x) h₂
    · intro e; cases e with | call h₁ x h₂ => exact .call h₁ (ih.mpr x) h₂
  | frame _ ih =>
    constructor
    · intro e; cases e with | frame h₁ x h₂ => exact .frame h₁ (ih.mp x) h₂
    · intro e; cases e with | frame h₁ x h₂ => exact .frame h₁ (ih.mpr x) h₂
  | pre _ ih => exact (Exec.fenceSeq_iff hn).trans ih
  | post _ ih => exact (Exec.seqFence_iff hn).trans ih
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit hn in
/-- Inserting barriers keeps an artifact verified. -/
theorem Verified.fenceIns {T : Target} {f : T.isa.Instr} (hn : Nop T.isa f) {c c' : Prog T.isa}
    {k : Contract T.isa} (hi : FenceIns f c' c) (h : Verified T c k) : Verified T c' k :=
  ⟨fun s hs => let ⟨t, s', e, h₁, h₂⟩ := h.1 s hs
    ⟨t, s', (Exec.fenceIns_iff hn hi).mpr e, h₁, h₂⟩,
   fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    h.2.1 _ _ _ _ _ _ h₁ h₂ hp ((Exec.fenceIns_iff hn hi).mp e₁) ((Exec.fenceIns_iff hn hi).mp e₂),
   h.2.2⟩

end Seq

/-! ## Speculative safety -/

/-- Speculatively constant time, and contained: a run that starts without
misspeculating never ends (returns to its caller) misspeculating. -/
def SpecSafe (S : Spectre M) (Pre : M.State → Prop) (Pub : M.State → M.State → Prop)
    (c : Prog M) : Prop :=
  SpecConstantTime S Pre Pub c ∧
    ∀ s D n t s' ms D' n', Pre s → SExec S c s false D n t (.done s' ms D' n') → ms = false

variable {S : Spectre M} {f : M.Instr}

/-- **Fencing every branch target**: constant-time code becomes speculatively
safe, for every transient semantics in which `f` is a barrier. -/
theorem specSafe_fenceFn (hs : LeakShape M) (hn : Nop M f) (hf : S.fence f = true)
    {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    (hv : ∀ s, Pre s → ∃ t s', Exec M c s t s') (hct : ConstantTime M Pre Pub c) :
    SpecSafe S Pre Pub (c.fenceFn f) := by
  refine ⟨specConstantTime_fence hs hn hf hv hct, fun s D n t s' ms D' n' hp e => ?_⟩
  obtain ⟨T, s₁, x⟩ := hv s hp
  rcases sexec_fenceSeq_false hn e with ⟨-, -, h⟩ | ⟨k, rfl, y⟩
  · cases h
  · obtain ⟨-, -, -, h, -⟩ := (fence_rel hs hn hf c x x rfl y y).2
    exact h

/-- **Code the taint analysis checks, with a barrier before it returns**, is
speculatively safe, without barriers at its branches. -/
theorem specSafe_taint {A : Taint M} (hs : Taint.SpecSound A S) (hf : S.fence f = true)
    {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M} (τ : A.T)
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → A.Agree τ s₁ s₂) {hc : Taint.Hint A.T}
    (h : (A.check τ (.seq c (.block [f])) hc).isSome = true) :
    SpecSafe S Pre Pub (.seq c (.block [f])) := by
  refine ⟨Taint.specConstantTime hs τ hpub h, fun s D n t s' ms D' n' _ e => ?_⟩
  cases e with
  | seq _ b =>
    cases b with
    | blockDone y =>
      cases y with
      | cons hf' _ y => cases y; simpa [hf] using hf'

end VG
