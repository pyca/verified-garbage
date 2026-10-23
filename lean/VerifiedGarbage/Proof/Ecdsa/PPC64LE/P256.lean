module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LE
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli

/-!
# P-256's configuration of the ECDSA code on PPC64LE

`p256_ok`: the configuration meets what the proofs of the code need
(`CfgOk`): four 64-bit words per number, and no bit of a 32-byte hash dropped.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.Impl.Ecdsa.PPC64LE

theorem p256_nBits : 64 * p256.n ≤ Spec.Ecdsa.nBits p256.C := by
  show 256 ≤ Spec.P256.curve.n.log2 + 1
  have : 255 ≤ Spec.P256.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `32` bytes is dropped. -/
theorem p256_sh : p256.sh = 0 := by
  have h : 64 * 4 ≤ Spec.Ecdsa.nBits p256.C := p256_nBits
  show 8 * 32 - Spec.Ecdsa.nBits p256.C = 0; omega

theorem p256_ok : CfgOk p256 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P256.onCurve_G
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
  sh := by rw [p256_sh]; decide
  fp := Weierstrass.PPC64LE.Mont.p256p_ok
  fpk := rfl
  fpm := rfl
  fn := Weierstrass.PPC64LE.Mont.p256n_ok
  fnk := rfl
  fnm := rfl

end VG.Proof.Ecdsa.PPC64LE
