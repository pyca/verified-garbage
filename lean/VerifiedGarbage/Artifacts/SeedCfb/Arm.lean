module

public import VerifiedGarbage.Proof.Seed.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED-CFB128 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB of `Impl/Modes/Arm/`, one block at a time (each block's input is the ciphertext \
  block before), calling the verified `vg_seed_ecb_encrypt` on the chaining value in a 72-byte working space on the \
  stack, zeroed on return."

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbEncrypt
    stack := 832
    verified := Proof.Seed.Arm.cfbEncrypt_framed },
  Spec.Seed.cfbDecryptApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbDecrypt
    stack := 832
    verified := Proof.Seed.Arm.cfbDecrypt_framed }]

end VG.Artifacts.SeedCfb.Arm
