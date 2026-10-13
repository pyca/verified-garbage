module

public import VerifiedGarbage.Proof.Camellia.X86.CbcVerified
import Mathlib.Tactic.SplitIfs

/-! # Camellia-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.X86

def artifacts : List Artifact := [
  { Spec.Camellia.cbcEncryptApi with
    target := X86.target
    doc := Spec.Camellia.cbcEncryptApi.doc
      (notes := ["Baseline IA-32: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table of bitsliced subkeys is built once per call. The mode is the generic CBC encryption of `Impl/Modes/X86/`, over Camellia's ECB core."])
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcEncrypt
    contract := Spec.Camellia.cbcEncryptContract X86.abi 2756
    stack := 2756
    verified := Proof.Camellia.X86.cbcEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Camellia.cbcDecryptApi with
    target := X86.target
    doc := Spec.Camellia.cbcDecryptApi.doc
      (notes := ["Baseline IA-32: one block at a time, decrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table of bitsliced subkeys is built once per call. The mode is the generic CBC decryption of `Impl/Modes/X86/`, over Camellia's ECB core."])
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcDecrypt
    contract := Spec.Camellia.cbcDecryptContract X86.abi 2756
    stack := 2756
    verified := Proof.Camellia.X86.cbcDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.CamelliaCbc.X86
