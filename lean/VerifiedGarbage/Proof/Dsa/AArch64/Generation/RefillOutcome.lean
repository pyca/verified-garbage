module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedOutcome
import VerifiedGarbage.Proof.Framework.Offset

/-! # The refillable-tape search's seeds on AArch64: their `h` window and result

The refillable-tape search (`Impl/Dsa/AArch64/Generation/Refill.lean`) runs
a seed attempt with its `h` tape (frame words 11 and 13) pointed, for each
seed, at a window of the witness tape (`GenerationTape.slice`):
`GenerationContext.withHs` is the context with it as the `h` tape, and
`RefillFinished` an attempt's end, whose context may have any `h` tape (the
slots it keeps leave out 11 and 13). -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum

/-- The context with `hs` as its `h` tape. -/
def GenerationContext.withHs (p : GenerationContext) (hs : GenerationTape p.geo) : GenerationContext where
  geo := p.geo
  seeds := p.seeds
  hs := hs
  rand := p.rand
  saved := fun k => if k = 11 then hs.ptr else if k = 13 then BitVec.ofNat 64 hs.bytes.length else p.saved k
  wrappedSlot := p.wrappedSlot
  hashesSlot := p.hashesSlot
  baseSlot := p.baseSlot
  seedsSlot := p.seedsSlot
  seedsLengthSlot := p.seedsLengthSlot
  hSlot := rfl
  hLengthSlot := rfl
  randSlot := p.randSlot
  randLengthSlot := p.randLengthSlot
  pLenSlot := p.pLenSlot
  qLenSlot := p.qLenSlot
  hashLenSlot := p.hashLenSlot

@[simp] theorem GenerationContext.withHs_geo (p : GenerationContext) (hs : GenerationTape p.geo) :
    (p.withHs hs).geo = p.geo := rfl

@[simp] theorem GenerationContext.withHs_rand (p : GenerationContext) (hs : GenerationTape p.geo) :
    (p.withHs hs).rand = p.rand := rfl

@[simp] theorem GenerationContext.withHs_changed (p : GenerationContext) (hs : GenerationTape p.geo) :
    (p.withHs hs).changed = p.changed := rfl

theorem GenerationContext.withHs_withHs (p : GenerationContext) (hs hs' : GenerationTape p.geo) :
    (p.withHs hs).withHs hs' = p.withHs hs' := by
  simp only [GenerationContext.withHs]
  congr 1
  funext k
  by_cases h11 : k = 11 <;> by_cases h13 : k = 13 <;> simp [h11, h13]

theorem GenerationContext.withHs_self (p : GenerationContext) : p.withHs p.hs = p := by
  cases p
  simp only [GenerationContext.withHs, GenerationContext.mk.injEq, heq_eq_eq, true_and]
  funext k
  by_cases h11 : k = 11
  · subst h11; simp [*]
  · by_cases h13 : k = 13
    · subst h13; simp [*]
    · simp [h11, h13]

/-- The slots a refill attempt keeps: the finite search's, but the `h`
tape's. -/
def refillSlots : List Nat := [1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 17, 18, 26]

/-- A refill attempt's end, from the context `p` and the words `initial`:
for some `h` tape inside the random tape, the result `res` (as
`SeedOutcome` states it), with `used` the witness tape's octets consumed. -/
def RefillFinished (p : GenerationContext) (initial : Nat → BitVec 64)
    (res : Option (Option Spec.Dsa.Params × List Byte)) (s t : State) : Prop :=
  ∃ (hs : GenerationTape p.geo) (W : Nat → BitVec 64) (used : Nat),
    Region.Sub ⟨hs.ptr, hs.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩ ∧ GenerationMemory (p.withHs hs) W t ∧
    used ≤ p.rand.bytes.length ∧ W 16 = BitVec.ofNat 64 used ∧
    (∀ k ∈ refillSlots, W k = initial k) ∧ SeedOutcome p res W used t ∧
    Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem refillSlots_search {k : Nat} (h : k ∈ refillSlots) : k ∈ searchSlots := by
  simp only [refillSlots, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [searchSlots]

theorem RefillFinished.prepend {p : GenerationContext} {Wi Wm : Nat → BitVec 64}
    {res : Option (Option Spec.Dsa.Params × List Byte)} {s u t : State}
    (h : RefillFinished p Wm res u t) (slots : ∀ k ∈ searchSlots, Wm k = Wi k)
    (hf : Frame p.changed s.mem u.mem) (hr : u.rd = s.rd) (hw : u.wr = s.wr) :
    RefillFinished p Wi res s t := by
  obtain ⟨hs, W, used, sub, mt, hu, h16, hsl, outcome, ft, rt, wt⟩ := h
  exact ⟨hs, W, used, sub, mt, hu, h16, fun k hk => (hsl k hk).trans (slots k (refillSlots_search hk)), outcome,
    hf.trans ft, rt.trans hr, wt.trans hw⟩

/-- An attempt that ends with the context's own `h` tape. -/
theorem refillFinished_of {p : GenerationContext} {W Wt : Nat → BitVec 64} {used : Nat}
    {res : Option (Option Spec.Dsa.Params × List Byte)} {s t : State}
    (h : GenerationMemory p Wt t)
    (hhs : Region.Sub ⟨p.hs.ptr, p.hs.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩)
    (hu : used ≤ p.rand.bytes.length) (h16 : Wt 16 = BitVec.ofNat 64 used)
    (slots : ∀ k ∈ searchSlots, Wt k = W k) (outcome : SeedOutcome p res Wt used t)
    (hf : Frame p.changed s.mem t.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    RefillFinished p W res s t := by
  refine ⟨p.hs, Wt, used, hhs, ?_, hu, h16, fun k hk => slots k (refillSlots_search hk), outcome, hf, hr, hw⟩
  rw [GenerationContext.withHs_self]
  exact h

end VG.Proof.Dsa.AArch64.Generation
