module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli

/-!
# secp256k1's configuration of the ECDSA code on PPC64LE

`secp256k1_ok`: the configuration meets what the proofs of the code need
(`CfgOk`): four 64-bit words per number, and no bit of a 32-byte hash dropped.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.Impl.Ecdsa.PPC64LE

theorem secp256k1_nBits : Spec.Ecdsa.nBits secp256k1.C = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.Secp256k1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Secp256k1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `32` bytes is dropped. -/
theorem secp256k1_sh : secp256k1.sh = 0 := by
  show 8 * 32 - Spec.Ecdsa.nBits secp256k1.C = 0
  rw [secp256k1_nBits]

theorem secp256k1_ok : CfgOk secp256k1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.Secp256k1.onCurve_G
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
  sh := by rw [secp256k1_sh]; decide
  fp := Weierstrass.PPC64LE.Mont.secp256k1p_ok
  fpk := rfl
  fpm := rfl
  fn := Weierstrass.PPC64LE.Mont.secp256k1n_ok
  fnk := rfl
  fnm := rfl

end VG.Proof.Ecdsa.PPC64LE
