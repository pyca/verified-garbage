module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
import VerifiedGarbage.Proof.P192.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli

/-!
# P-192's configuration of the ECDSA code on PPC64LE

`p192_ok`: the configuration meets what the proofs of the code need
(`CfgOk`): three 64-bit words per number, and no bit of a 24-byte hash dropped.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.Impl.Ecdsa.PPC64LE

theorem p192_nBits : Spec.Ecdsa.nBits p192.C = 192 := by
  show Spec.P192.curve.n.log2 + 1 = 192
  have h₁ : 191 ≤ Spec.P192.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P192.curve.n.log2 < 192 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `24` bytes is dropped. -/
theorem p192_sh : p192.sh = 0 := by
  show 8 * 24 - Spec.Ecdsa.nBits p192.C = 0
  rw [p192_nBits]

theorem p192_ok : CfgOk p192 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P192.onCurve_G
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
  sh := by rw [p192_sh]; decide
  fp := Weierstrass.PPC64LE.Mont.p192p_ok
  fpk := rfl
  fpm := rfl
  fn := Weierstrass.PPC64LE.Mont.p192n_ok
  fnk := rfl
  fnm := rfl

end VG.Proof.Ecdsa.PPC64LE
