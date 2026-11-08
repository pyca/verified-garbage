module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P521.Arm.Law

/-! # Deterministic ECDSA (RFC 6979) over P-521 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaP521Rfc6979.Arm

open VG.Proof.P521.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT p521 p521T_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p521 hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p521.tries vars
    stack := stackT
    verified := p521T_verified hasLaw.law }]

end VG.Artifacts.EcdsaP521Rfc6979.Arm
