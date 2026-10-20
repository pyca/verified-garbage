module

public import VerifiedGarbage.Proof.Camellia.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact AArch64.target {
    notes := ["Baseline AArch64: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table of bitsliced subkeys is built once per call, by a call of `vg_camellia_prepare_keys`, and each batch is a call of `vg_camellia_crypt_prepared`. The mode is the generic CBC encryption of `Impl/Modes/AArch64/`, over Camellia's ECB core. The IV's address is kept in a register the core keeps, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cbcEncryptChained
    stack := 3344
    verified := Proof.Camellia.AArch64.cbcEncryptChained_framed },
  Spec.Camellia.cbcDecryptChainedApi.artifact AArch64.target {
    notes := ["Baseline AArch64: eight blocks at a time, decrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups; the table of bitsliced subkeys is built once per call, by a call of `vg_camellia_prepare_keys`, and each batch is a call of `vg_camellia_crypt_prepared`. The mode is the generic CBC decryption of `Impl/Modes/AArch64/`, over Camellia's ECB core. The last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cbcDecryptChained
    stack := 3344
    verified := Proof.Camellia.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.CamelliaCbc.AArch64
