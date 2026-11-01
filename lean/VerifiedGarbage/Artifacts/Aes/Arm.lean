module

public import VerifiedGarbage.Proof.Aes.Arm.Blocks
public import VerifiedGarbage.Proof.Aes.Arm.Frame
public import VerifiedGarbage.Proof.Aes.Arm.ExpandKey
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.Ct32.Layers
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Aes.Ct32.Layers
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream

/-! # AES on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Aes.Arm

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.Aes.Arm.expandKey
    stack := 512
    verified := Proof.Aes.Arm.expandKey_framed },
  Spec.Aes.encryptBlocksApi.artifact Arm.target {
    code := Impl.Aes.Arm.encryptBlocks
    verified := Proof.Aes.Arm.Ecb.encryptBlocks_verified },
  Spec.Aes.decryptBlocksApi.artifact Arm.target {
    code := Impl.Aes.Arm.decryptBlocks
    verified := Proof.Aes.Arm.Ecb.decryptBlocks_verified }]

end VG.Artifacts.Aes.Arm
