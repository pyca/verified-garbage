module

public import VerifiedGarbage.Proof.Sm4.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit

/-! # SM4-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact X86_64.target {
    notes := ["Baseline x86-64: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups, in a batch of sixteen of which the other fifteen are unused; the key schedule's table of round keys is built once per call, inline, and each batch is a call of `vg_sm4_crypt_prepared`. The mode is the generic CBC encryption of `Impl/Modes/X86_64/`, over SM4's ECB core; the IV's address is kept in `xmm15`, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcEncryptChained
    stack := 3216
    verified := Proof.Sm4.X86_64.cbcEncryptChained_framed },
  Spec.Sm4.cbcDecryptChainedApi.artifact X86_64.target {
    notes := ["Baseline x86-64: sixteen blocks at a time, decrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups; the key schedule's table of round keys is built once per call, inline, and each batch is a call of `vg_sm4_crypt_prepared`. The mode is the generic CBC decryption of `Impl/Modes/X86_64/`, over SM4's ECB core; the last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcDecryptChained
    stack := 3216
    verified := Proof.Sm4.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.Sm4Cbc.X86_64
