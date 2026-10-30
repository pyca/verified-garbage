module

public import VerifiedGarbage.Proof.TripleDes.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-CFB8 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Encrypt
    stack := 1088
    verified := Proof.TripleDes.Arm.cfb8Encrypt_framed },
  Spec.TripleDes.cfb8DecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Decrypt
    stack := 1088
    verified := Proof.TripleDes.Arm.cfb8Decrypt_framed }]

end VG.Artifacts.TripleDesCfb8.Arm
