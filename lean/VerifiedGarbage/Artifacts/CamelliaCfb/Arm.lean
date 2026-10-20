module

public import VerifiedGarbage.Proof.Camellia.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CFB128 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB of `Impl/Modes/Arm/`, one block at a time (each block's input is the ciphertext \
  block before), calling the verified `vg_camellia_ecb_encrypt` (bitsliced, in a batch of eight) on the chaining \
  value with the number of rounds, in a 72-byte working space on the stack, zeroed on return."

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbEncrypt
    stack := 2904
    verified := Proof.Camellia.Arm.cfbEncrypt_framed },
  Spec.Camellia.cfbDecryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecrypt
    stack := 2904
    verified := Proof.Camellia.Arm.cfbDecrypt_framed }]

end VG.Artifacts.CamelliaCfb.Arm
