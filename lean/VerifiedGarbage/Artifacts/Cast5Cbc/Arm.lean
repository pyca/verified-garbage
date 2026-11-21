module

public import VerifiedGarbage.Proof.Cast5.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # CAST5-CBC on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.Arm

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cbcEncryptChained
    verified := Proof.Cast5.Arm.Fn.cbcEncryptChained },
  Spec.Cast5.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cbcDecryptChained
    verified := Proof.Cast5.Arm.Fn.cbcDecryptChained }]

end VG.Artifacts.Cast5Cbc.Arm
