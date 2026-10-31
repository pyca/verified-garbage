module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.MulVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # secp256k1's point multiplication on AArch64 -/

@[expose] public section

namespace VG.Generic.Secp256k1.AArch64.MulSecp256k1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.Secp256k1.Mul

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.Secp256k1.curve) : List Artifact :=
  [C.mulApi.artifact AArch64.target {
      code := secp256k1.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.Secp256k1.AArch64.MulSecp256k1
