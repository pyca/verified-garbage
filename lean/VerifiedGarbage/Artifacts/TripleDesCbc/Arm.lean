module

public import VerifiedGarbage.Proof.TripleDes.Arm.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcEncryptChained
    stack := 1088
    verified := Proof.TripleDes.Arm.cbcEncryptChained_framed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcDecryptChained
    stack := 1088
    verified := Proof.TripleDes.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.TripleDesCbc.Arm
