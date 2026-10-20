module

public import VerifiedGarbage.Proof.Sm4.X86.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.CbcLit

/-! # SM4-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.X86

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact X86.target {
    notes := ["Baseline IA-32: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups, in a batch of eight of which the other seven are unused; the key schedule's table of round keys is built once per call, by `vg_sm4_prepare_keys`, and the batch encrypted by `vg_sm4_crypt_prepared`. The mode is the generic CBC encryption of `Impl/Modes/X86/`, over SM4's ECB core, with the chaining value, the last ciphertext block, back to the IV at the end."]
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cbcEncryptChained
    stack := 1516
    verified := Proof.Sm4.X86.Cbc.cbcEncryptChained_framed },
  Spec.Sm4.cbcDecryptChainedApi.artifact X86.target {
    notes := ["Baseline IA-32: one block at a time, decrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups, in a batch of eight of which the other seven are unused; the key schedule's table of round keys is built once per call, by `vg_sm4_prepare_keys`, and the batch encrypted by `vg_sm4_crypt_prepared`. The mode is the generic CBC decryption of `Impl/Modes/X86/`, over SM4's ECB core, with the chaining value, the last ciphertext block, back to the IV at the end."]
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cbcDecryptChained
    stack := 1516
    verified := Proof.Sm4.X86.Cbc.cbcDecryptChained_framed }]

end VG.Artifacts.Sm4Cbc.X86
