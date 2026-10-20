module

public import VerifiedGarbage.Proof.Blowfish.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CFB128 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB of `Impl/Modes/Arm/`, one block at a time (each block's input is the ciphertext \
  block before), calling the verified `vg_blowfish_ecb_encrypt` on the chaining value in a 56-byte working space on the \
  stack, zeroed on return."

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbEncrypt
    stack := 320
    verified := Proof.Blowfish.Arm.cfbEncrypt_framed },
  Spec.Blowfish.cfbDecryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbDecrypt
    stack := 320
    verified := Proof.Blowfish.Arm.cfbDecrypt_framed }]

end VG.Artifacts.BlowfishCfb.Arm
