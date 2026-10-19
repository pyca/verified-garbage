module

public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.X86.Ops

/-! # Bounds and separation for the compact public RSA workspace -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.Impl.Bignum.X86.PublicContext VG.Impl.Mont
open VG.Proof.Mont.X86

theorem slot_le {n i j : Nat} (h : i < j) : slot n i + stride n ≤ slot n j := by
  have := Nat.mul_le_mul_right (stride n) h
  simp only [slot, Nat.succ_mul] at *
  omega

theorem slot_bound {n i : Nat} (h : i < 8) : slot n i + stride n ≤ size n := slot_le h

theorem slot_sep {n i j : Nat} (h : i ≠ j) :
    slot n i + stride n ≤ slot n j ∨ slot n j + stride n ≤ slot n i := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact .inl (slot_le h)
  · exact .inr (slot_le h)

theorem slot_header (n i : Nat) : 256 ≤ slot n i := by
  unfold slot VG.Impl.Bignum.hdrBytes
  omega

theorem size_eq (n : Nat) : size n = 64 * n + 384 := by
  simp only [size, slot, stride, VG.Impl.Bignum.hdrBytes]
  omega

/-- Exactly the byte count promised by the public RSA contract. -/
theorem size_contract (len : Nat) :
    size (Spec.Rsa.modulusWords len) = 8 * Spec.Rsa.publicScratchWords len := by
  rw [size_eq]
  unfold Spec.Rsa.publicScratchWords
  omega

theorem acc_length (n : Nat) : accLen (modulus n) = 16 * n + 4 := by
  simp only [accLen, VG.Impl.Mont.X86.words, modulus]
  omega

/-- The full accumulator fits before array four, including its carry word. -/
theorem acc_end (n : Nat) : slot n 2 + accLen (modulus n) ≤ slot n 4 := by
  rw [acc_length]
  simp only [slot, stride]
  omega

theorem acc_sep {n i : Nat} (hi : operand i) :
    slot n i + 8 * n ≤ slot n 2 ∨ slot n 2 + accLen (modulus n) ≤ slot n i := by
  obtain ⟨hi, hi2, hi3⟩ := hi
  by_cases h : i < 2
  · have := slot_le (n := n) h
    simp only [stride] at this
    omega
  · have h4 : 4 ≤ i := by omega
    have hm := Nat.mul_le_mul_right (stride n) h4
    have he := acc_end n
    simp only [slot] at he ⊢
    omega

theorem operation_layout {n bytes o a b : Nat} (hs : size n ≤ bytes)
    (ho : operand o) (ha : operand a) (hb : operand b) (ho1 : o ≠ 1) :
    OpLay (modulus n) bytes (slot n 2) (slot n o) (slot n a) (slot n b) := by
  have bo := slot_bound (n := n) ho.1
  have ba := slot_bound (n := n) ha.1
  have bb := slot_bound (n := n) hb.1
  have b4 := slot_bound (n := n) (i := 4) (by decide)
  have he := acc_end n
  have so := acc_sep (n := n) ho
  have sa := acc_sep (n := n) ha
  have sb := acc_sep (n := n) hb
  have sm := acc_sep (n := n) (i := 0) (by unfold operand; decide)
  have st := acc_sep (n := n) (i := 1) (by unfold operand; decide)
  have ot := slot_sep (n := n) ho1
  simp only [stride, accLen, VG.Impl.Mont.X86.words, modulus] at *
  constructor <;> simp only [accLen, VG.Impl.Mont.X86.words] <;> omega

end VG.Proof.Bignum.X86.PublicContext
