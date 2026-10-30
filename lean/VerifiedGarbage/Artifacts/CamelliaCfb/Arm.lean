module

public import VerifiedGarbage.Proof.Camellia.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CFB128 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.Arm

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbEncrypt
    stack := 2904
    verified := Proof.Camellia.Arm.cfbEncrypt_framed },
  Spec.Camellia.cfbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecrypt
    stack := 2904
    verified := Proof.Camellia.Arm.cfbDecrypt_framed }]

end VG.Artifacts.CamelliaCfb.Arm
