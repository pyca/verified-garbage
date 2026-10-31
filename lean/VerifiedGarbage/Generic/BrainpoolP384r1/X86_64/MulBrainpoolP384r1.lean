module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.MulVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.MulLit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP384r1's point multiplication on x86-64

`vg_brainpoolp384r1_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over brainpoolP384r1's group law and inversions `h`, the variant
`Variants/BrainpoolP384r1/X86_64/Law.lean`: the ladder's proof takes the group law,
and the curve's facts (`brainpoolp384r1_ok`) its inversions.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.X86_64.MulBrainpoolP384r1

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.BrainpoolP384r1.Mul

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP384r1.curve) : List Artifact :=
  [C.mulApi.artifact X86_64.target {
      code := brainpoolp384r1.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.BrainpoolP384r1.X86_64.MulBrainpoolP384r1
