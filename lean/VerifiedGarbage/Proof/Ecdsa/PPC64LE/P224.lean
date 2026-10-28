module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.MulLit
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli

/-!
# P-224's configuration of the ECDSA code on PPC64LE

`p224_ok`: the configuration meets what the proofs of the code need
(`CfgOk`): four 64-bit words per number, and no bit of a 28-byte hash dropped.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.Impl.Ecdsa.PPC64LE

theorem p224_nBits : Spec.Ecdsa.nBits p224.C = 224 := by
  show Spec.P224.curve.n.log2 + 1 = 224
  have h₁ : 223 ≤ Spec.P224.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P224.curve.n.log2 < 224 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `28` bytes is dropped. -/
theorem p224_sh : p224.sh = 0 := by
  show 8 * 28 - Spec.Ecdsa.nBits p224.C = 0
  rw [p224_nBits]

theorem p224_ok : CfgOk p224 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P224.onCurve_G
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
  sh := by rw [p224_sh]; decide
  fp := Weierstrass.PPC64LE.Mont.p224p_ok
  fpk := rfl
  fpm := rfl
  fn := Weierstrass.PPC64LE.Mont.p224n_ok
  fnk := rfl
  fnm := rfl
  mulNf := fun _ _ => Impl.Ecdsa.PPC64LE.mulP224_noFrames

end VG.Proof.Ecdsa.PPC64LE
