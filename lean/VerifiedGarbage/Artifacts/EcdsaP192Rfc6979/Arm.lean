module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P192
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P192.Arm.Law

/-! # Deterministic ECDSA (RFC 6979) over P-192 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaP192Rfc6979.Arm

open VG.Proof.P192.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT p192 p192T_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p192 hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p192.tries vars
    stack := stackT
    verified := p192T_verified hasLaw.law }]

end VG.Artifacts.EcdsaP192Rfc6979.Arm
