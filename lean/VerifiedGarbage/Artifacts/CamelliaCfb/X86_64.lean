import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified

/-! # Camellia-CFB128 artifacts on baseline x86-64 -/

namespace VG.Artifacts.CamelliaCfb.X86_64

/-- How the functions compute Camellia, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time (each block's input depends on the block before), encrypted bitsliced in \
  general-purpose registers (the S-boxes as Boolean circuits), with no table lookups, in a batch of eight of which \
  the other seven are unused; the subkeys are prepared once per call. The mode is the generic CFB of `Impl/Modes/X86_64/`, \
  over Camellia's ECB core."

def artifacts : List Artifact := [
  { Spec.Camellia.cfbEncryptApi with
    target := X86_64.target
    doc := Spec.Camellia.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r9 401 Impl.Camellia.X86_64.cfbEncrypt
    contract := Spec.Camellia.cfbEncryptContract X86_64.abi 3216
    stack := 3216
    verified := Proof.Camellia.X86_64.cfbEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Camellia.cfbDecryptApi with
    target := X86_64.target
    doc := Spec.Camellia.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r9 401 Impl.Camellia.X86_64.cfbDecrypt
    contract := Spec.Camellia.cfbDecryptContract X86_64.abi 3216
    stack := 3216
    verified := Proof.Camellia.X86_64.cfbDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.CamelliaCfb.X86_64
