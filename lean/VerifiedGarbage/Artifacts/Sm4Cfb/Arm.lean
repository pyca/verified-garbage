module

public import VerifiedGarbage.Proof.Sm4.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-CFB128 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB of `Impl/Modes/Arm/`, one block at a time (each block's input is the ciphertext \
  block before), calling the verified `vg_sm4_ecb_encrypt` on the chaining value in a 72-byte working space on the \
  stack, zeroed on return."

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbEncrypt
    stack := 1560
    verified := Proof.Sm4.Arm.cfbEncrypt_framed },
  Spec.Sm4.cfbDecryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbDecrypt
    stack := 1560
    verified := Proof.Sm4.Arm.cfbDecrypt_framed }]

end VG.Artifacts.Sm4Cfb.Arm
