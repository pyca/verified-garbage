import VerifiedGarbage.Proof.Seed.X86.CbcVerified

/-! # SEED-CBC artifacts on baseline x86 (32-bit) -/

namespace VG.Artifacts.SeedCbc.X86

def artifacts : List Artifact := [
  { Spec.Seed.cbcEncryptApi with
    target := X86.target
    doc := Spec.Seed.cbcEncryptApi.doc
      (notes := ["Baseline IA-32: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups, in a batch of eight of which the other seven are unused; the table of round keys in the direction's order is built from the schedule once per call. The mode is the generic CBC encryption of `Impl/Modes/X86/`, over SEED's ECB core."])
    code := Impl.StackScratch.X86.withStackScratchWiped 888 4 216 Impl.Seed.X86.cbcEncrypt
    contract := Spec.Seed.cbcEncryptContract X86.abi 888
    stack := 888
    verified := Proof.Seed.X86.cbcEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Seed.cbcDecryptApi with
    target := X86.target
    doc := Spec.Seed.cbcDecryptApi.doc
      (notes := ["Baseline IA-32: one block at a time, decrypted bitsliced in general-purpose registers through the AES S-box circuit (SEED's S-boxes are affine maps of AES's), with no table lookups, in a batch of eight of which the other seven are unused; the table of round keys in the direction's order is built from the schedule once per call. The mode is the generic CBC decryption of `Impl/Modes/X86/`, over SEED's ECB core."])
    code := Impl.StackScratch.X86.withStackScratchWiped 888 4 216 Impl.Seed.X86.cbcDecrypt
    contract := Spec.Seed.cbcDecryptContract X86.abi 888
    stack := 888
    verified := Proof.Seed.X86.cbcDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.SeedCbc.X86
