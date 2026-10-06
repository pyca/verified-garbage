import VerifiedGarbage.Proof.Bignum.CrtGPow

/-!
# RSA with the CRT: the header's arguments

The modulus' header slots that `entry` fills and nothing else writes: the
saved registers, `out`, `n`, `k`, the input and the private key's pointers
and lengths (`hFixed`). Each part's changes keep them (`HFix`).
-/

namespace VG.Proof.Bignum

open VG VG.Impl.Bignum

/-- The header slots of the arguments. -/
def hFixed (i : Nat) : Bool :=
  i < 6 || (16 ≤ i && i ≤ 21) || i == 23 || i == 24 || i == 25 || i == 27 || i == 28

/-- A range that keeps the arguments' slots. -/
def KeepsHdr (r : Nat × Nat) : Prop := ∀ i < 32, hFixed i = true → 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i

theorem keepsHdr_ge {r : Nat × Nat} (h : 8 * 32 ≤ r.1) : KeepsHdr r := fun _ hi _ => Or.inl (by omega)

theorem keepsHdr_slot {j : Nat} (hj : j < 32) (hf : hFixed j = false) : KeepsHdr (8 * j, 8) := by
  intro i _ hfi
  have : i ≠ j := by rintro rfl; rw [hf] at hfi; exact absurd hfi (by decide)
  simp only; omega

/-- The arguments' slots, unchanged. -/
def HFix (B : Addr) (m m' : Mem) : Prop := ∀ i < 32, hFixed i = true → word m' B (8 * i) = word m B (8 * i)

theorem HFix.refl (B : Addr) (m : Mem) : HFix B m m := fun _ _ _ => rfl

theorem HFix.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : HFix B m₁ m₂) (h₂ : HFix B m₂ m₃) : HFix B m₁ m₃ :=
  fun i hi hf => (h₂ i hi hf).trans (h₁ i hi hf)

theorem HFix.of_frm {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hr : ∀ r ∈ rs, KeepsHdr r) : HFix B m m' := fun i hi hf =>
  h.word_eq (fun r hr' => hr r hr' i hi hf) (by omega)

theorem keepsHdr_gRanges (w : Nat) : ∀ r ∈ gRanges w, KeepsHdr r := by
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aY (show 31 < 32 by decide)
  simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl)
  · exact keepsHdr_ge (by simp only; omega)
  · exact keepsHdr_ge (by simp only; omega)
  · exact keepsHdr_ge (by simp only; omega)
  · exact keepsHdr_slot (by decide) (by decide)
  · exact keepsHdr_slot (by decide) (by decide)

theorem keepsHdr_setupRanges (w : Nat) : ∀ r ∈ setupRanges w, KeepsHdr r := by
  have := hdr_lt_slot w Public.aN (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aOne (show 31 < 32 by decide)
  simp only [setupRanges, loadRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact keepsHdr_slot (by decide) (by decide)
  · intro i _ hf; simp only [hFixed, sArr] at hf ⊢; revert hf; revert i; decide
  · exact keepsHdr_ge (by simp only; omega)
  · exact keepsHdr_ge (by simp only; omega)
  · exact keepsHdr_slot (by decide) (by decide)
  · exact keepsHdr_slot (by decide) (by decide)
  · exact keepsHdr_ge (by simp only; omega)

theorem keepsHdr_r2Ranges (w : Nat) : ∀ r ∈ r2Ranges w, KeepsHdr r := by
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aR2 (show 31 < 32 by decide)
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl)
  · exact keepsHdr_ge (by simp only; omega)
  · exact keepsHdr_ge (by simp only; omega)
  · exact keepsHdr_ge (by simp only; omega)
  · exact keepsHdr_slot (by decide) (by decide)

end VG.Proof.Bignum
