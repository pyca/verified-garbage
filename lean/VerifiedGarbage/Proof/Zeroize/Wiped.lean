module

public import VerifiedGarbage.Spec.Zeroize
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the proofs of every function that leaves its scratch scrubbed share it

/-!
# Scratch wiped in fixed places

What each function that leaves its `scratch` scrubbed (`Spec.Zeroize.scrubbed`)
does to it: the bytes at the offsets `S` are zero on return, and the others are
as they were (`WipedBy`). `S` depends only on the code and on public data, so
two runs leave the same bytes (`WipedBy.left`, for `Api.publicOut`).
-/

@[expose] public section

namespace VG.Proof.Zeroize

open VG.Spec.Zeroize

/-- The bytes of the `len` at `p` at the offsets `S` are zero, and the others are
as they were. -/
def WipedBy (S : Nat → Bool) (m m' : Mem) (p : Addr) (len : Nat) : Prop :=
  ∀ i < len, m' (p + BitVec.ofNat 64 i) = if S i then 0 else m (p + BitVec.ofNat 64 i)

variable {S : Nat → Bool} {m m' : Mem} {p : Addr} {len : Nat}

theorem WipedBy.scrubbed (h : WipedBy S m m' p len) : scrubbed m m' p len := by
  intro a ha
  have hi : (a - p).toNat < len := by simp only [Region.Contains] at ha; omega_using [ha]
  have ea : p + BitVec.ofNat 64 (a - p).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have he := h _ hi
  rw [ea] at he
  rw [he]
  split
  · exact .inr rfl
  · exact .inl rfl

/-- Two runs that find the same bytes leave the same bytes. -/
theorem WipedBy.left {m₁ m₂ m₁' m₂' : Mem} {p₁ p₂ : Addr} (h₁ : WipedBy S m₁ m₁' p₁ len)
    (h₂ : WipedBy S m₂ m₂' p₂ len) (hm : left m₁ p₁ len = left m₂ p₂ len) :
    left m₁' p₁ len = left m₂' p₂ len := by
  simp only [VG.Spec.Zeroize.left, bytesAt, List.map_map] at hm ⊢
  refine List.map_congr_left fun i hi => ?_
  have hb := (List.map_inj_left.mp hm) i hi
  have hi := List.mem_range.mp hi
  simp only [Function.comp_def] at hb ⊢
  rw [h₁ i hi, h₂ i hi]
  split
  · rfl
  · exact hb

/-- The first `w` bytes zero, and the others as they were. -/
theorem WipedBy.of_prefix {w : Nat} (hz : bytesAt m' p w = zeros w)
    (ht : ∀ i, w ≤ i → i < len → m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    WipedBy (fun i => decide (i < w)) m m' p len := by
  intro i hi
  by_cases hw : i < w
  · have he := congrArg (·[i]?) hz
    simp only [bytesAt, zeros, List.getElem?_map, List.getElem?_range hw,
      List.getElem?_replicate, hw, ite_true, Option.map_some, Option.some.injEq] at he
    simp only [hw, decide_true, ite_true, he]
  · simp only [hw, decide_false, Bool.false_eq_true, ite_false]
    exact ht i (Nat.le_of_not_lt hw) hi

/-- All of the bytes zero. -/
theorem WipedBy.of_zeros (hz : bytesAt m' p len = zeros len) :
    WipedBy (fun i => decide (i < len)) m m' p len :=
  .of_prefix hz fun _ h₁ h₂ => absurd h₂ (Nat.not_lt.mpr h₁)

/-- None of the bytes written. -/
theorem WipedBy.of_unchanged
    (ht : ∀ i, i < len → m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    WipedBy (fun _ => false) m m' p len := fun i hi => by
  simp only [Bool.false_eq_true, ite_false]; exact ht i hi

/-- It reads the memory on entry and on return only within the buffer. -/
theorem WipedBy.congr {m₁ m₁' : Mem} (h : WipedBy S m m' p len)
    (hm : ∀ i < len, m₁ (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hm' : ∀ i < len, m₁' (p + BitVec.ofNat 64 i) = m' (p + BitVec.ofNat 64 i)) :
    WipedBy S m₁ m₁' p len := fun i hi => by rw [hm i hi, hm' i hi]; exact h i hi

end VG.Proof.Zeroize
