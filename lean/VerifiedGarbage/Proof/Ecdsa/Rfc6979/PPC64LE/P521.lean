module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.Verified

/-! # Deterministic ECDSA on PPC64LE: P-521's signature with a given `k` -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p521_sign`, with P-521's group law `hL`. -/
def p521Core (hL : Weierstrass.Law Spec.P521.curve) : Core where
  E := Spec.Ecdsa.P521.inst
  C := Impl.Ecdsa.PPC64LE.signP521
  N := "vg_ecdsa_p521_sign"
  V := (Proof.Ecdsa.PPC64LE.P521.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P521.sign_verified hL).2.1
  d := by decide +kernel

theorem p521_nBits : Spec.Ecdsa.nBits Spec.P521.curve = 521 := by
  show Spec.P521.curve.n.log2 + 1 = 521
  have h₁ : 520 ≤ Spec.P521.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P521.curve.n.log2 < 521 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
