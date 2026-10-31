module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.MulVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.MulLit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # secp256k1's point multiplication on x86-64 -/

@[expose] public section

namespace VG.Generic.Secp256k1.X86_64.MulSecp256k1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.Secp256k1.Mul

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.Secp256k1.curve) : List Artifact :=
  [C.mulApi.artifact X86_64.target {
      code := secp256k1.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.Secp256k1.X86_64.MulSecp256k1
