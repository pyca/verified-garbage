module

public import VerifiedGarbage.Proof.Camellia.X86.FbVerified

/-! # Camellia-CFB128 artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.X86

/-- How the functions compute Camellia, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, encrypted bitsliced in general-purpose registers, the S-boxes as \
  Boolean circuits, with no table lookups, in a batch of eight of which the other seven are unused; the table \
  of bitsliced subkeys is built once per call. The mode is the generic CFB of `Impl/Modes/X86/`, over \
  Camellia's ECB core."

def artifacts : List Artifact := [
  { Spec.Camellia.cfbEncryptApi with
    target := X86.target
    doc := Spec.Camellia.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncrypt
    contract := Spec.Camellia.cfbEncryptContract X86.abi 2756
    stack := 2756
    verified := Proof.Camellia.X86.Fb.cfbEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Camellia.cfbDecryptApi with
    target := X86.target
    doc := Spec.Camellia.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecrypt
    contract := Spec.Camellia.cfbDecryptContract X86.abi 2756
    stack := 2756
    verified := Proof.Camellia.X86.Fb.cfbDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.CamelliaCfb.X86
