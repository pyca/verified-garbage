module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Verified

/-! # Deterministic ECDSA on PPC64LE: P-384's signature with a given `k` -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p384_sign`, with P-384's group law `hL`. -/
def p384Core (hL : Weierstrass.Law Spec.P384.curve) : Core where
  E := Spec.Ecdsa.P384.inst
  C := Impl.Ecdsa.PPC64LE.signP384
  N := "vg_ecdsa_p384_sign"
  V := (Proof.Ecdsa.PPC64LE.P384.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P384.sign_verified hL).2.1
  d := by decide +kernel

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
