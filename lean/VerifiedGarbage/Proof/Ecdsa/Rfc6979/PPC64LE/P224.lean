module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.Verified

/-! # Deterministic ECDSA on PPC64LE: P-224's signature with a given `k` -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p224_sign`, with P-224's group law `hL`. -/
def p224Core (hL : Weierstrass.Law Spec.P224.curve) : Core where
  E := Spec.Ecdsa.P224.inst
  C := Impl.Ecdsa.PPC64LE.signP224
  N := "vg_ecdsa_p224_sign"
  V := (Proof.Ecdsa.PPC64LE.P224.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P224.sign_verified hL).2.1
  d := by decide +kernel

theorem p224_nBits : Spec.Ecdsa.nBits Spec.P224.curve = 224 := by
  show Spec.P224.curve.n.log2 + 1 = 224
  have h₁ : 223 ≤ Spec.P224.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P224.curve.n.log2 < 224 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
