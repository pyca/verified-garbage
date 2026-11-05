module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedOutcome
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # The refillable-tape search's seeds on x86-64: their `h` window and result

The refillable-tape search (`Impl/Dsa/X86_64/Generation/Refill.lean`) runs
the finite search's seed attempt with its `h` tape (frame words 11 and 12)
pointed, for each seed, at a window of the witness tape: `window` is that
part of a tape, `GenerationContext.withHs` the context with it as the `h`
tape, and `RefillFinished` an attempt's end, whose context may have any
`h` tape (the slots it keeps leave out 11 and 12). -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum

theorem bytesAt_window (m : Mem) (a : Addr) {d n len : Nat} (h : d + n ≤ len) :
    Spec.Rsa.bytesAt m (a + BitVec.ofNat 64 d) n = ((Spec.Rsa.bytesAt m a len).drop d).take n := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, List.length_take, List.length_drop]
    omega
  · intro i h₁ h₂
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- The `n` octets of a tape from its `d`-th. -/
def GenerationTape.window {g : GenerationGeometry} (t : GenerationTape g) (d n : Nat)
    (h : d + n ≤ t.bytes.length) : GenerationTape g where
  ptr := off t.ptr d
  bytes := (t.bytes.drop d).take n
  bound := by
    have := t.bound
    simp only [List.length_take, List.length_drop, off]
    have := t.size
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  size := by
    have := t.size
    simp only [List.length_take, List.length_drop]; omega
  arena := t.arena.sub_left (by
    simp only [List.length_take, List.length_drop, off]
    exact Offset.sub_base t.ptr (by omega))
  frame := t.frame.sub_left (by
    simp only [List.length_take, List.length_drop, off]
    exact Offset.sub_base t.ptr (by omega))
  stack := t.stack.sub_left (by
    simp only [List.length_take, List.length_drop, off]
    exact Offset.sub_base t.ptr (by omega))

theorem GenerationTape.window_length {g : GenerationGeometry} (t : GenerationTape g) {d n : Nat}
    (h : d + n ≤ t.bytes.length) : (t.window d n h).bytes.length = n := by
  simp only [GenerationTape.window, List.length_take, List.length_drop]; omega

theorem GenerationTapeMemory.window {g : GenerationGeometry} {t : GenerationTape g} {s : State}
    (ht : GenerationTapeMemory t s) {d n : Nat} (h : d + n ≤ t.bytes.length) :
    GenerationTapeMemory (t.window d n h) s := by
  refine ⟨?_, ?_⟩
  · intro a k ⟨r, hr, hc⟩
    simp only [List.mem_singleton] at hr
    subst hr
    refine ht.cover a k ⟨_, List.mem_singleton_self _, ?_⟩
    have hl := t.size
    simp only [Region.Contains, t.window_length h] at hc ⊢
    have e : a - t.ptr = (a - (t.ptr + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
      rw [← BitVec.sub_sub, BitVec.sub_add_cancel]
    change (a - (t.ptr + BitVec.ofNat 64 d)).toNat + k ≤ n at hc
    rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [t.window_length h]
    show Spec.Rsa.bytesAt s.mem (t.ptr + BitVec.ofNat 64 d) n = (t.bytes.drop d).take n
    rw [bytesAt_window s.mem t.ptr h, ht.bytes]

/-- The context with `hs` as its `h` tape. -/
def GenerationContext.withHs (p : GenerationContext) (hs : GenerationTape p.geo) : GenerationContext where
  geo := p.geo
  seeds := p.seeds
  hs := hs
  rand := p.rand
  saved := fun k => if k = 11 then hs.ptr else if k = 12 then BitVec.ofNat 64 hs.bytes.length else p.saved k
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

/-- The slots a refill attempt keeps: the finite search's, but the `h`
tape's. -/
def refillSlots : List Nat := [1, 3, 4, 5, 6, 7, 8, 9, 10, 13, 15, 17, 18, 28]

/-- A refill attempt's end, from the context `p` and the words `initial`:
for some `h` tape, the result `res` (as `SeedOutcome` states it), with
`used` the witness tape's octets consumed. -/
def RefillFinished (p : GenerationContext) (initial : Nat → BitVec 64)
    (res : Option (Option Spec.Dsa.Params × List Byte)) (s t : State) : Prop :=
  ∃ (hs : GenerationTape p.geo) (W : Nat → BitVec 64) (used : Nat),
    Region.Sub ⟨hs.ptr, hs.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩ ∧ GenerationMemory (p.withHs hs) W t ∧
    used ≤ p.rand.bytes.length ∧ W 16 = BitVec.ofNat 64 used ∧
    (∀ k ∈ refillSlots, W k = initial k) ∧ SeedOutcome p res W used t ∧
    Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

end VG.Proof.Dsa.X86_64.Generation
