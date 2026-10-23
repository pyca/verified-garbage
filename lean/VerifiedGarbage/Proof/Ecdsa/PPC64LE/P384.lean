module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli

/-!
# P-384's configuration of the ECDSA code on PPC64LE

`p384_ok`: the configuration meets what the proofs of the code need
(`CfgOk`): six 64-bit words per number, and no bit of a 48-byte hash dropped.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.Impl.Ecdsa.PPC64LE

theorem p384_nBits : Spec.Ecdsa.nBits p384.C = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `48` bytes is dropped. -/
theorem p384_sh : p384.sh = 0 := by
  show 8 * 48 - Spec.Ecdsa.nBits p384.C = 0
  rw [p384_nBits]

theorem p384_ok : CfgOk p384 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P384.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  n_enc := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [p384_sh]; decide
  fp := Weierstrass.PPC64LE.Mont.p384p_ok
  fpk := rfl
  fpm := rfl
  fn := Weierstrass.PPC64LE.Mont.p384n_ok
  fnk := rfl
  fnm := rfl

end VG.Proof.Ecdsa.PPC64LE
