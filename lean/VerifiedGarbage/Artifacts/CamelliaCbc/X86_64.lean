import VerifiedGarbage.Proof.Camellia.X86_64.CbcVerified

/-! # Camellia-CBC artifacts on baseline x86-64 -/

namespace VG.Artifacts.CamelliaCbc.X86_64

def artifacts : List Artifact := [
  { Spec.Camellia.cbcEncryptApi with
    target := X86_64.target
    doc := Spec.Camellia.cbcEncryptApi.doc
      (notes := ["Baseline x86-64: one block at a time (CBC encryption is sequential), encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table of bitsliced subkeys is built once per call. The mode is the generic CBC encryption of `Impl/Modes/X86_64/`, over Camellia's ECB core."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r9 401 Impl.Camellia.X86_64.cbcEncrypt
    contract := Spec.Camellia.cbcEncryptContract X86_64.abi 3216
    stack := 3216
    verified := Proof.Camellia.X86_64.cbcEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Camellia.cbcDecryptApi with
    target := X86_64.target
    doc := Spec.Camellia.cbcDecryptApi.doc
      (notes := ["Baseline x86-64: eight blocks at a time, decrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups; the table of bitsliced subkeys is built once per call. The mode is the generic CBC decryption of `Impl/Modes/X86_64/`, over Camellia's ECB core."])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r9 401 Impl.Camellia.X86_64.cbcDecrypt
    contract := Spec.Camellia.cbcDecryptContract X86_64.abi 3216
    stack := 3216
    verified := Proof.Camellia.X86_64.cbcDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.CamelliaCbc.X86_64
