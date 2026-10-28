module

public import VerifiedGarbage.Proof.Camellia.X86.CbcVerified
import VerifiedGarbage.Proof.Camellia.X86.CbcLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.X86

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact X86.target {
    notes := ["Baseline IA-32: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table of bitsliced subkeys is built once per call, inline, and each batch is a call of `vg_camellia_crypt_prepared`, its arguments in a frame on the stack. The mode is the generic CBC encryption of `Impl/Modes/X86/`, over Camellia's ECB core. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcEncryptChained
    stack := 2772
    verified := Proof.Camellia.X86.Cbc.cbcEncryptChained_framed },
  Spec.Camellia.cbcDecryptChainedApi.artifact X86.target {
    notes := ["Baseline IA-32: one block at a time, decrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table of bitsliced subkeys is built once per call, inline, and each batch is a call of `vg_camellia_crypt_prepared`, its arguments in a frame on the stack. The mode is the generic CBC decryption of `Impl/Modes/X86/`, over Camellia's ECB core. The chaining value, the last ciphertext block, goes back to the IV at the end."]
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcDecryptChained
    stack := 2772
    verified := Proof.Camellia.X86.Cbc.cbcDecryptChained_framed }]

end VG.Artifacts.CamelliaCbc.X86
