module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.X86.P384.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.X86.P384.MulLit

/-! # P-384's point multiplication on x86 (32-bit) -/

@[expose] public section

namespace VG.Generic.P384.X86.MulP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p384.mulApi.artifact X86.target {
    code := Impl.Ecdsa.X86.mulP384
    stack := 20
    verified := Proof.Ecdsa.X86.P384.Mul.mul_verified h.law }]

end VG.Generic.P384.X86.MulP384
