module

public import VerifiedGarbage.Proof.Sm4.Arm.FbVerified
public import VerifiedGarbage.Proof.Sm4.Arm.CfbBatchVerified
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
    notes := ["Baseline ARMv7: prepare the bitsliced round keys once and decrypt up to eight ciphertext blocks per batch. The IV and preceding ciphertext blocks are encrypted independently. The 1512-byte working space is kept on the stack and zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 Impl.Sm4.Arm.BatchCfb.decrypt
    stack := 1520
    verified := Proof.Sm4.Arm.CfbBatchVerified.framed }]

end VG.Artifacts.Sm4Cfb.Arm
