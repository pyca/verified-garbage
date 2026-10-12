import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified

/-! # CAST5-CFB64 artifacts on baseline AArch64 -/

namespace VG.Artifacts.Cast5Cfb.AArch64

/-- How the functions compute CAST5, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through the generic CFB of `Impl/Modes/AArch64/` over CAST5's ECB \
  block code (inlined): each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, \
  so no secret is an address. The subkeys are read where the caller passed them and the number of rounds \
  stays in `x1`; the 112-byte working space on the stack is zeroed on return."

def artifacts : List Artifact := [
  { Spec.Cast5.cfbEncryptApi with
    target := AArch64.target
    doc := Spec.Cast5.cfbEncryptApi.doc (notes := [note])
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbEncrypt
    contract := Spec.Cast5.cfbEncryptContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112
    stack := 112
    verified := Proof.Cast5.AArch64.cfbEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cast5.cfbDecryptApi with
    target := AArch64.target
    doc := Spec.Cast5.cfbDecryptApi.doc (notes := [note])
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbDecrypt
    contract := Spec.Cast5.cfbDecryptContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts) 112
    stack := 112
    verified := Proof.Cast5.AArch64.cfbDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Cast5Cfb.AArch64
