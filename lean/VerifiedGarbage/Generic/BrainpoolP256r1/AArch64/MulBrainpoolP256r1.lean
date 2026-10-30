module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.MulVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP256r1's point multiplication on AArch64

`vg_brainpoolp256r1_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over brainpoolP256r1's group law and inversions `h`, the variant
`Variants/BrainpoolP256r1/AArch64/Law.lean`: the ladder's proof takes the group law,
and the curve's facts (`brainpoolp256r1_ok`) its inversions.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.AArch64.MulBrainpoolP256r1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Mul

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact :=
  [C.mulApi.artifact AArch64.target {
      code := brainpoolp256r1.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.BrainpoolP256r1.AArch64.MulBrainpoolP256r1
