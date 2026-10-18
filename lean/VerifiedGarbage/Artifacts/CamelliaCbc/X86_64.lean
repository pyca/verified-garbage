module

public import VerifiedGarbage.Proof.Camellia.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact X86_64.target {
    notes := ["Baseline x86-64: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table of bitsliced subkeys is built once per call, inline, and each batch is a call of `vg_camellia_crypt_prepared`. The mode is the generic CBC encryption of `Impl/Modes/X86_64/`, over Camellia's ECB core. The IV's address is kept in `xmm15`, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcEncryptChained
    stack := 3288
    verified := Proof.Camellia.X86_64.cbcEncryptChained_framed },
  Spec.Camellia.cbcDecryptChainedApi.artifact X86_64.target {
    notes := ["Baseline x86-64: eight blocks at a time, decrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups; the table of bitsliced subkeys is built once per call, inline, and each batch is a call of `vg_camellia_crypt_prepared`. The mode is the generic CBC decryption of `Impl/Modes/X86_64/`, over Camellia's ECB core. The last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcDecryptChained
    stack := 3288
    verified := Proof.Camellia.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.CamelliaCbc.X86_64
