module

public import VerifiedGarbage.Proof.TripleDes.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-CFB64 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncrypt
    stack := 1088
    verified := Proof.TripleDes.Arm.cfbEncrypt_framed },
  Spec.TripleDes.cfbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbDecrypt
    stack := 1088
    verified := Proof.TripleDes.Arm.cfbDecrypt_framed }]

end VG.Artifacts.TripleDesCfb.Arm
