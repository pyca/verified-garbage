module

public import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.Arm

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact Arm.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.cbcEncryptChained
    stack := 336
    verified := Proof.Cast5.Arm.cbcEncryptChained_framed },
  Spec.Cast5.cbcDecryptChainedApi.artifact Arm.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.cbcDecryptChained
    stack := 336
    verified := Proof.Cast5.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.Cast5Cbc.Arm
