module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulLit

/-! # P-521's point multiplication on x86 (32-bit) -/

@[expose] public section

namespace VG.Generic.P521.X86.MulP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p521.mulApi.artifact X86.target {
    code := Impl.Ecdsa.X86.mulP521
    stack := 20
    verified := Proof.Ecdsa.X86.P521.Mul.mul_verified h.law }]

end VG.Generic.P521.X86.MulP521
