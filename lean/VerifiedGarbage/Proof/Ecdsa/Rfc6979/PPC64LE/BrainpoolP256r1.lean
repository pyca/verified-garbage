module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP256r1.Verified

/-! # Deterministic ECDSA on PPC64LE: brainpoolP256r1's signature with a given `k` -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_brainpoolp256r1_sign`, with brainpoolP256r1's group law `hL`. -/
def brainpoolp256r1Core (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) : Core where
  E := Spec.Ecdsa.BrainpoolP256r1.inst
  C := Impl.Ecdsa.PPC64LE.signBrainpoolP256r1
  N := "vg_ecdsa_brainpoolp256r1_sign"
  V := (Proof.Ecdsa.PPC64LE.BrainpoolP256r1.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.BrainpoolP256r1.sign_verified hL).2.1
  d := by decide +kernel

theorem brainpoolp256r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP256r1.curve = 256 := by
  show Spec.BrainpoolP256r1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.BrainpoolP256r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP256r1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
