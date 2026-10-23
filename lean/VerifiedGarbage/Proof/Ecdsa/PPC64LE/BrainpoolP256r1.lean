module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.PPC64LE
import VerifiedGarbage.Proof.BrainpoolP256r1.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli

/-!
# brainpoolP256r1's configuration of the ECDSA code on PPC64LE

`brainpoolp256r1_ok`: the configuration meets what the proofs of the code need
(`CfgOk`): four 64-bit words per number, and no bit of a 32-byte hash dropped.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.Impl.Ecdsa.PPC64LE

theorem brainpoolp256r1_nBits : Spec.Ecdsa.nBits brainpoolp256r1.C = 256 := by
  show Spec.BrainpoolP256r1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.BrainpoolP256r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP256r1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `32` bytes is dropped. -/
theorem brainpoolp256r1_sh : brainpoolp256r1.sh = 0 := by
  show 8 * 32 - Spec.Ecdsa.nBits brainpoolp256r1.C = 0
  rw [brainpoolp256r1_nBits]

theorem brainpoolp256r1_ok : CfgOk brainpoolp256r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP256r1.onCurve_G
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
  sh := by rw [brainpoolp256r1_sh]; decide
  fp := Weierstrass.PPC64LE.Mont.brainpoolp256r1p_ok
  fpk := rfl
  fpm := rfl
  fn := Weierstrass.PPC64LE.Mont.brainpoolp256r1n_ok
  fnk := rfl
  fnm := rfl

end VG.Proof.Ecdsa.PPC64LE
