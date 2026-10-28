module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.MulLit
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontModuli

/-!
# P-521's configuration of the ECDSA code on PPC64LE

`p521_ok`: the configuration meets what the proofs of the code need
(`CfgOk`): nine 64-bit words per number, and the hash's 528 bits shifted right by 7.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.Impl.Ecdsa.PPC64LE

theorem p521_nBits : Spec.Ecdsa.nBits p521.C = 521 := by
  show Spec.P521.curve.n.log2 + 1 = 521
  have h₁ : 520 ≤ Spec.P521.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P521.curve.n.log2 < 521 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- The 7 bits of a hash of `66` bytes past `n`'s 521 are dropped. -/
theorem p521_sh : p521.sh = 7 := by
  unfold Cfg.sh
  rw [p521_nBits]
  rfl

theorem p521_ok : CfgOk p521 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P521.onCurve_G
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
  sh := by rw [p521_sh]; decide
  fp := Weierstrass.PPC64LE.Mont.p521p_ok
  fpk := rfl
  fpm := rfl
  fn := Weierstrass.PPC64LE.Mont.p521n_ok
  fnk := rfl
  fnm := rfl
  mulNf := fun _ _ => Impl.Ecdsa.PPC64LE.mulP521_noFrames

end VG.Proof.Ecdsa.PPC64LE
