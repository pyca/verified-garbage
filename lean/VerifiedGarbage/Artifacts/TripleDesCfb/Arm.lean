module

public import VerifiedGarbage.Proof.TripleDes.Arm.FbVerified
public import VerifiedGarbage.Proof.TripleDes.Arm.FbFinalVerified
public import VerifiedGarbage.Impl.TripleDes.Arm.FbFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

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
    verified := Proof.TripleDes.Arm.cfbDecrypt_framed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncryptFinal
    stack := 1088
    verified := Proof.TripleDes.Arm.cfbEncryptFinal_framed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbDecryptFinal
    stack := 1088
    verified := Proof.TripleDes.Arm.cfbDecryptFinal_framed }]

end VG.Artifacts.TripleDesCfb.Arm
