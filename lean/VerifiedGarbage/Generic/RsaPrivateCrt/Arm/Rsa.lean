module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # The RSA modulus' precomputed values on ARMv7, for each private CRT implementation -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.Rsa

open VG.Proof.Rsa.Arm

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact Arm.target {
    suffix := v.suffix
    code := v.pc
    stack := 56
    verified := v.pcVerified
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.Rsa
