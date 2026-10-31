module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.MulLit

/-! # P-224's point multiplication on PPC64LE -/

@[expose] public section

namespace VG.Generic.P224.PPC64LE.MulP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p224.mulApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.mulP224
    verified := Proof.Ecdsa.PPC64LE.P224.Mul.mul_verified h.law }]

end VG.Generic.P224.PPC64LE.MulP224
