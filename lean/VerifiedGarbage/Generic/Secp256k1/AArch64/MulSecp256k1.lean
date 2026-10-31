module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.MulVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# secp256k1's point multiplication on AArch64

`vg_secp256k1_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over secp256k1's group law and inversions `h`, the variant
`Variants/Secp256k1/AArch64/Law.lean`: the ladder's proof takes the group law,
and the curve's facts (`secp256k1_ok`) its inversions.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.AArch64.MulSecp256k1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.Secp256k1.Mul

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.Secp256k1.curve) : List Artifact :=
  [C.mulApi.artifact AArch64.target {
      code := secp256k1.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.Secp256k1.AArch64.MulSecp256k1
