module

public import VerifiedGarbage.Proof.Blowfish.Arm.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cbcEncryptChained
    stack := 320
    verified := Proof.Blowfish.Arm.cbcEncryptChained_framed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cbcDecryptChained
    stack := 320
    verified := Proof.Blowfish.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.BlowfishCbc.Arm
