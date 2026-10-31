module

public import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-CFB64 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.Arm

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact Arm.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.cfbEncrypt
    stack := 336
    verified := Proof.Cast5.Arm.cfbEncrypt_framed },
  Spec.Cast5.cfbDecryptApi.artifact Arm.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.cfbDecrypt
    stack := 336
    verified := Proof.Cast5.Arm.cfbDecrypt_framed }]

end VG.Artifacts.Cast5Cfb.Arm
