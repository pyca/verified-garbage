module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.Verified

/-! # Deterministic ECDSA on PPC64LE: secp256k1's signature with a given `k` -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_secp256k1_sign`, with secp256k1's group law `hL`. -/
def secp256k1Core (hL : Weierstrass.Law Spec.Secp256k1.curve) : Core where
  E := Spec.Ecdsa.Secp256k1.inst
  C := Impl.Ecdsa.PPC64LE.signSecp256k1
  N := "vg_ecdsa_secp256k1_sign"
  V := (Proof.Ecdsa.PPC64LE.Secp256k1.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.Secp256k1.sign_verified hL).2.1
  d := by decide +kernel

theorem secp256k1_nBits : Spec.Ecdsa.nBits Spec.Secp256k1.curve = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.Secp256k1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Secp256k1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
