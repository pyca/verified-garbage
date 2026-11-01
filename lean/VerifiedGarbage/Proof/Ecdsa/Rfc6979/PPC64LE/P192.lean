module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Verified

/-! # Deterministic ECDSA on PPC64LE: P-192's signature with a given `k` -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p192_sign`, with P-192's group law `hL`. -/
def p192Core (hL : Weierstrass.Law Spec.P192.curve) : Core where
  E := Spec.Ecdsa.P192.inst
  C := Impl.Ecdsa.PPC64LE.signP192
  N := "vg_ecdsa_p192_sign"
  V := (Proof.Ecdsa.PPC64LE.P192.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P192.sign_verified hL).2.1
  d := by decide +kernel

theorem p192_nBits : Spec.Ecdsa.nBits Spec.P192.curve = 192 := by
  show Spec.P192.curve.n.log2 + 1 = 192
  have h₁ : 191 ≤ Spec.P192.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P192.curve.n.log2 < 192 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
