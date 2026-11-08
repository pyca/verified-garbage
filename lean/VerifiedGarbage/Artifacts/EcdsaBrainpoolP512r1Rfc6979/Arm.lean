module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP512r1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP512r1.Arm.Law

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP512r1 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP512r1Rfc6979.Arm

open VG.Proof.BrainpoolP512r1.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT brainpoolp512r1 brainpoolp512r1T_verified brainpoolp512r1U brainpoolp512r1UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp512r1 hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vars
    stack := stackT
    verified := brainpoolp512r1T_verified hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp512r1U hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vars
    stack := stackT
    verified := brainpoolp512r1UT_verified hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcdsaBrainpoolP512r1Rfc6979.Arm
