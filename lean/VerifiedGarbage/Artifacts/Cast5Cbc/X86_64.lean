module

public import VerifiedGarbage.Proof.Cast5.X86_64.CbcVerified

/-! # CAST5-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.X86_64

/-- How the functions compute CAST5, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through the generic CBC of `Impl/Modes/X86_64/` over CAST5's ECB \
  block code (inlined): each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, \
  so no secret is an address. The subkeys are copied into the working space once per call; the number \
  of rounds stays in `rsi`; the 240-byte working space on the stack is zeroed on return."

def artifacts : List Artifact := [
  { Spec.Cast5.cbcEncryptApi with
    target := X86_64.target
    doc := Spec.Cast5.cbcEncryptApi.doc (notes := [note])
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 Impl.Cast5.X86_64.cbcEncrypt
    contract := Spec.Cast5.cbcEncryptContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 240
    stack := 240
    verified := Proof.Cast5.X86_64.cbcEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cast5.cbcDecryptApi with
    target := X86_64.target
    doc := Spec.Cast5.cbcDecryptApi.doc (notes := [note])
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 Impl.Cast5.X86_64.cbcDecrypt
    contract := Spec.Cast5.cbcDecryptContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 240
    stack := 240
    verified := Proof.Cast5.X86_64.cbcDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Cast5Cbc.X86_64
