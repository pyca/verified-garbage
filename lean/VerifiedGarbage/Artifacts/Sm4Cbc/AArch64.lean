module

public import VerifiedGarbage.Proof.Sm4.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact AArch64.target {
    notes := ["Baseline AArch64: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups, in a batch of sixteen of which the other fifteen are unused; the key schedule's table of round keys is built once per call, by a call of `vg_sm4_prepare_keys`, and each batch is a call of `vg_sm4_crypt_prepared`. The mode is the generic CBC encryption of `Impl/Modes/AArch64/`, over SM4's ECB core; the IV's address is kept in `x19`, which the core saves in `v31`, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cbcEncryptChained
    stack := 3264
    verified := Proof.Sm4.AArch64.cbcEncryptChained_framed },
  Spec.Sm4.cbcDecryptChainedApi.artifact AArch64.target {
    notes := ["Baseline AArch64: sixteen blocks at a time, decrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups; the key schedule's table of round keys is built once per call, by a call of `vg_sm4_prepare_keys`, and each batch is a call of `vg_sm4_crypt_prepared`. The mode is the generic CBC decryption of `Impl/Modes/AArch64/`, over SM4's ECB core; the last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cbcDecryptChained
    stack := 3264
    verified := Proof.Sm4.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.Sm4Cbc.AArch64
