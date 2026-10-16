module

public import VerifiedGarbage.Proof.TripleDes.Arm.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_triple_des_ecb_encrypt` on each block in a 56-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcEncrypt
    stack := 1088
    verified := Proof.TripleDes.Arm.cbcEncrypt_framed },
  Spec.TripleDes.cbcDecryptApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_triple_des_ecb_decrypt` on each block in place, with the chaining value in a 56-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcDecrypt
    stack := 1088
    verified := Proof.TripleDes.Arm.cbcDecrypt_framed }]

end VG.Artifacts.TripleDesCbc.Arm
