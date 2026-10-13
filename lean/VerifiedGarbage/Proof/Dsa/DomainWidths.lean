module

public import VerifiedGarbage.Proof.Dsa.DomainShape
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # Relating public width scans to the DSA parameter-size predicate -/

@[expose] public section

namespace VG.Proof.Dsa
open VG

theorem supported_scans (p q : List Byte) :
    Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q)) ↔
    128 ≤ (significant p).2.toNat ∧ 128 ≤ (significant q).2.toNat ∧
      Spec.Dsa.supportedSizes (8 * (significant p).1) (8 * (significant q).1) := by
  have hp1 := significant_width p (n := 128) (by decide)
  have hp2 := significant_width p (n := 256) (by decide)
  have hp3 := significant_width p (n := 384) (by decide)
  have hq1 := significant_width q (n := 20) (by decide)
  have hq2 := significant_width q (n := 28) (by decide)
  have hq3 := significant_width q (n := 32) (by decide)
  unfold Spec.Dsa.supportedSizes
  omega

/-- Supported subgroup widths are byte-aligned, including padded inputs. -/
theorem subgroup_scan_width {p q : List Byte}
    (h : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q))) :
    Spec.Dsa.bitLength (Spec.Dsa.decodeBE q) = 8 * (significant q).1 := by
  have hs := (supported_scans p q).mp h
  have hq1 := significant_width q (n := 20) (by decide)
  have hq2 := significant_width q (n := 28) (by decide)
  have hq3 := significant_width q (n := 32) (by decide)
  unfold Spec.Dsa.supportedSizes at h hs
  omega

/-- Only the last encoded byte determines whether a modulus is odd. -/
theorem decodeBE_last_mod_two (front : List Byte) (last : Byte) :
    Spec.Dsa.decodeBE (front ++ [last]) % 2 = last.toNat % 2 := by
  rw [decodeBE_append]
  have hlast : Spec.Dsa.decodeBE [last] = last.toNat := by simp [Spec.Dsa.decodeBE]
  rw [hlast]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.pow_one]
  rw [Nat.add_mod, Nat.mul_mod]
  simp

end VG.Proof.Dsa
