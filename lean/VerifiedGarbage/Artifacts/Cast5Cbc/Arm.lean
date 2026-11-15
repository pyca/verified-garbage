module

public import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # CAST5-CBC on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.Arm

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.cbcEncryptChained
    verified := Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.Arm.cbcEncryptChained_framed },
  Spec.Cast5.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.cbcDecryptChained
    verified := Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.Cast5Cbc.Arm
