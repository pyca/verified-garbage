module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.Words32

/-! # Values known at a stage of the prepared Miller–Rabin round -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- Updating one known array or scratch word does not make another known. -/
def setAt {α : Type} (values : Nat → α) (index : Nat) (value : α) : Nat → α :=
  fun i => if i = index then value else values i

@[simp] theorem setAt_self {α : Type} (values : Nat → α) (index : Nat) (value : α) :
    setAt values index value index = value := by simp only [setAt, ↓reduceIte]

theorem setAt_other {α : Type} (values : Nat → α) {index i : Nat} (value : α) (other : i ≠ index) :
    setAt values index value i = values i := by simp only [setAt, other, ↓reduceIte]

theorem setAt_same {α : Type} (values : Nat → α) (index : Nat) :
    setAt values index (values index) = values := by
  funext j
  by_cases same : j = index
  · subst j; exact setAt_self values index (values index)
  · exact setAt_other values (values index) same

theorem setAt_twice {α : Type} (values : Nat → α) (index : Nat) (first last : α) :
    setAt (setAt values index first) index last = setAt values index last := by
  funext j
  by_cases same : j = index
  · subst j; rw [setAt_self, setAt_self]
  · rw [setAt_other _ _ same, setAt_other _ _ same, setAt_other _ _ same]

/-- Only the explicitly listed arrays and scratch words have known values.
Modulus metadata and caller stack invariants are tracked separately. -/
structure Data (g : Geometry) (arrays : Nat → Nat) (knownArrays : List Nat)
    (slots : Nat → BitVec 32) (knownSlots : List Nat) (s : State) : Prop where
  context : Context g s
  arrayValues : ∀ j ∈ knownArrays, j < 28 ∧ val32 s.mem g.W (g.array j) g.words = arrays j
  slotValues : ∀ d ∈ knownSlots, scratchWord d ∧ s.mem.readW (off g.W d) 32 = slots d

theorem Data.mono {g : Geometry} {A A' : Nat → Nat} {Js Js' : List Nat}
    {V V' : Nat → BitVec 32} {Ds Ds' : List Nat} {s : State} (D : Data g A Js V Ds s)
    (arrays : ∀ j ∈ Js', j ∈ Js ∧ A j = A' j)
    (slots : ∀ d ∈ Ds', d ∈ Ds ∧ V d = V' d) : Data g A' Js' V' Ds' s := by
  refine ⟨D.context, ?_, ?_⟩
  · intro j mem
    obtain ⟨known, value⟩ := arrays j mem
    obtain ⟨bound, read⟩ := D.arrayValues j known
    exact ⟨bound, read.trans value⟩
  · intro d mem
    obtain ⟨known, value⟩ := slots d mem
    obtain ⟨scratch, read⟩ := D.slotValues d known
    exact ⟨scratch, read.trans value⟩

theorem Geometry.array_ne (g : Geometry) {i j : Nat} (different : i ≠ j) : g.array i ≠ g.array j := by
  have increasing {a b : Nat} (order : a < b) : g.array a < g.array b := by
    have step := Nat.mul_lt_mul_of_pos_right order (by omega : 0 < 8 * (g.w + 2))
    unfold Geometry.array VG.Proof.Rsa.Mont.arrAt VG.Proof.Rsa.Mont.hdrBytes
    omega
  rcases Nat.lt_or_gt_of_ne different with before | after
  · exact Nat.ne_of_lt (increasing before)
  · exact (Nat.ne_of_lt (increasing after)).symm

theorem Geometry.strideBefore (g : Geometry) {i j : Nat} (index : i < j) :
    g.array i + 8 * (g.w + 2) ≤ g.array j := by
  have step := Nat.mul_le_mul_right (8 * (g.w + 2)) index
  unfold Geometry.array VG.Proof.Rsa.Mont.arrAt VG.Proof.Rsa.Mont.hdrBytes
  rw [Nat.succ_mul] at step
  omega

theorem Geometry.readApart (g : Geometry) {i j : Nat} (different : j ≠ i) :
    g.array j + 4 * g.words ≤ g.array i ∨ g.array i + 8 * (g.w + 2) ≤ g.array j := by
  rcases Nat.lt_or_gt_of_ne different with before | after
  · exact Or.inl (g.arrayBefore before)
  · exact Or.inr (g.strideBefore after)

theorem scratch_fit {d : Nat} (scratch : scratchWord d) : d + 4 ≤ 256 := by
  unfold scratchWord at scratch
  omega

theorem scratch_apart {a b : Nat} (sa : scratchWord a) (sb : scratchWord b) (different : a ≠ b) :
    a + 4 ≤ b ∨ b + 4 ≤ a := by
  unfold scratchWord at sa sb
  omega

end VG.Proof.MillerRabin.X86
