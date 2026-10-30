module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.MulLit

/-!
# P-224's point multiplication on PPC64LE

`vg_p224_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.PPC64LE.MulP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p224.mulApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.mulP224
    verified := Proof.Ecdsa.PPC64LE.P224.Mul.mul_verified h.law }]

end VG.Generic.P224.PPC64LE.MulP224
