module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.MulVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # brainpoolP256r1's point multiplication on AArch64 -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.AArch64.MulBrainpoolP256r1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Mul

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact :=
  [C.mulApi.artifact AArch64.target {
      code := brainpoolp256r1.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.BrainpoolP256r1.AArch64.MulBrainpoolP256r1
