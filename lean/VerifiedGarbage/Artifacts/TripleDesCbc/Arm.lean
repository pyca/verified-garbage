module

public import VerifiedGarbage.Proof.TripleDes.Arm.CbcVerified
public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.WideVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Triple DES-CBC on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcEncryptChained
    verified := Proof.TripleDes.Arm.cbcEncryptChained_framed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 1040 0 256 Impl.TripleDes.Arm.Wide.cbcDecrypt
    verified := Proof.TripleDes.Arm.Bitsliced.cbcDecrypt_framed }]

end VG.Artifacts.TripleDesCbc.Arm
