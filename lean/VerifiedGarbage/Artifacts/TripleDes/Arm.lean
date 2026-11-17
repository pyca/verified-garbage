module

public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Verified
public import VerifiedGarbage.Proof.TripleDes.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.TripleDes.Arm.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.Bytes
public import VerifiedGarbage.Proof.TripleDes.Permutation
public import VerifiedGarbage.TCB.Arm.Print

/-! # Triple DES on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDes.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.TripleDes.Arm.Key.expandKey
    verified := Proof.TripleDes.Arm.expandKey_framed },
  Spec.TripleDes.ecbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 1024 .r3 256 Impl.TripleDes.Arm.Bitslice.encrypt
    verified := Proof.TripleDes.Arm.ecb_framed Proof.TripleDes.Arm.Bitsliced.encrypt_verified },
  Spec.TripleDes.ecbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 1024 .r3 256 Impl.TripleDes.Arm.Bitslice.decrypt
    verified := Proof.TripleDes.Arm.ecb_framed Proof.TripleDes.Arm.Bitsliced.decrypt_verified }]

end VG.Artifacts.TripleDes.Arm
