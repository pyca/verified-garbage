module

public import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Triple DES-CBC on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cbcEncrypt
    verified := .scrubbed Proof.TripleDes.Arm.Fn.cbcEncrypt },
  Spec.TripleDes.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cbcDecrypt
    verified := .scrubbed Proof.TripleDes.Arm.Fn.cbcDecrypt }]

end VG.Artifacts.TripleDesCbc.Arm
