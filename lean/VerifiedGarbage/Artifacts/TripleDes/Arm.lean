module

public import VerifiedGarbage.Proof.TripleDes.Arm.Ecb.Verified
public import VerifiedGarbage.Proof.TripleDes.Arm.Frame
public import VerifiedGarbage.Proof.TripleDes.Arm.VerifiedBlock
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
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.Arm.Key.Verified
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Permutation

@[expose] public section

namespace VG.Artifacts.TripleDes.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.TripleDes.Arm.Key.expandKey
    stack := 512
    verified := Proof.TripleDes.Arm.expandKey_framed },
  Spec.TripleDes.ecbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 1024 .r3 256 Impl.TripleDes.Arm.Ecb.encrypt
    stack := 1024
    verified := Proof.TripleDes.Arm.ecb_framed Proof.TripleDes.Arm.Ecb.encrypt_verified },
  Spec.TripleDes.ecbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 1024 .r3 256 Impl.TripleDes.Arm.Ecb.decrypt
    stack := 1024
    verified := Proof.TripleDes.Arm.ecb_framed Proof.TripleDes.Arm.Ecb.decrypt_verified }]

end VG.Artifacts.TripleDes.Arm
