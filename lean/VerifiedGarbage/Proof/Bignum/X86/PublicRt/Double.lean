module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Output
public import VerifiedGarbage.Proof.Mont.X86.Rt.Body
import VerifiedGarbage.Proof.Framework.Omega

/-! # The numbers' places in public RSA at a run-time width

Number `j + 1` follows number `j` (`numAt_succ`), and two different numbers
lie apart (`numAt_apart`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

theorem numAt_succ (len j : Nat) : numAt len (j + 1) = numAt len j + wb len := by
  simp only [numAt, Nat.succ_mul]; omega

/-- Number `x` and number `d` lie apart. -/
theorem numAt_apart (len : Nat) {x d : Nat} (h : x ≠ d) :
    numAt len d + wb len ≤ numAt len x ∨ numAt len x + wb len ≤ numAt len d := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · right; have := Nat.mul_le_mul_right (wb len) (Nat.succ_le_of_lt h)
    simp only [numAt, Nat.succ_mul] at *; omega
  · left; have := Nat.mul_le_mul_right (wb len) (Nat.succ_le_of_lt h)
    simp only [numAt, Nat.succ_mul] at *; omega

end VG.Proof.Bignum.X86.PublicRt
