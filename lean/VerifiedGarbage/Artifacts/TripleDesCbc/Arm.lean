module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CBC on ARMv7 -/

namespace VG.Artifacts.TripleDesCbc.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cbcEncrypt
    verified := Proof.TripleDes.Arm.Fn.cbcEncrypt },
  Spec.TripleDes.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cbcDecrypt
    verified := Proof.TripleDes.Arm.Fn.cbcDecrypt }]

spec_apis artifacts

end VG.Artifacts.TripleDesCbc.Arm
