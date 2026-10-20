module

public import VerifiedGarbage.Proof.Seed.X86.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.CbcLit

/-! # SEED-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.X86

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact X86.target {
    notes := ["Baseline IA-32: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups, in a batch of eight of which the other seven are unused; the table of round keys in the direction's order is built from the schedule once per call. The mode is the generic CBC encryption of `Impl/Modes/X86/`, over SEED's ECB core. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.X86.withStackScratchWiped 888 4 216 Impl.Seed.X86.cbcEncryptChained
    stack := 888
    verified := Proof.Seed.X86.Cbc.cbcEncryptChained_framed },
  Spec.Seed.cbcDecryptChainedApi.artifact X86.target {
    notes := ["Baseline IA-32: one block at a time, decrypted bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups, in a batch of eight of which the other seven are unused; the table of round keys in the direction's order is built from the schedule once per call. The mode is the generic CBC decryption of `Impl/Modes/X86/`, over SEED's ECB core. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.X86.withStackScratchWiped 888 4 216 Impl.Seed.X86.cbcDecryptChained
    stack := 888
    verified := Proof.Seed.X86.Cbc.cbcDecryptChained_framed }]

end VG.Artifacts.SeedCbc.X86
