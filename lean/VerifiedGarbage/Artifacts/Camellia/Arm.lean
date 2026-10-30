module

public import VerifiedGarbage.Proof.Camellia.Arm.KeyVerified
public import VerifiedGarbage.Proof.Camellia.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Camellia.Arm

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 2720 .r3 680 Impl.Camellia.Arm.expandKey
    stack := 2720
    verified := Proof.Camellia.Arm.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 2816 0 680 (Impl.Camellia.Arm.ecb .encrypt)
    stack := 2816
    verified := Proof.Camellia.Arm.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 2816 0 680 (Impl.Camellia.Arm.ecb .decrypt)
    stack := 2816
    verified := Proof.Camellia.Arm.ecb_framed .decrypt }]

end VG.Artifacts.Camellia.Arm
