module

public import VerifiedGarbage.Proof.Blowfish.Arm.FbVerified
public import VerifiedGarbage.Proof.Blowfish.Arm.FbFinalVerified
public import VerifiedGarbage.Impl.Blowfish.Arm.FbFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Blowfish-CFB128 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbEncrypt
    stack := 320
    verified := Proof.Blowfish.Arm.cfbEncrypt_framed },
  Spec.Blowfish.cfbDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbDecrypt
    stack := 320
    verified := Proof.Blowfish.Arm.cfbDecrypt_framed },
  Spec.Blowfish.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbEncryptFinal
    stack := 320
    verified := Proof.Blowfish.Arm.cfbEncryptFinal_framed },
  Spec.Blowfish.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbDecryptFinal
    stack := 320
    verified := Proof.Blowfish.Arm.cfbDecryptFinal_framed }]

end VG.Artifacts.BlowfishCfb.Arm
