module

public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-CFB64 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.AArch64

/-- How the functions compute CAST5, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through the generic CFB of `Impl/Modes/AArch64/` over CAST5's ECB \
  block code (inlined): each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, \
  so no secret is an address. The subkeys are read where the caller passed them and the number of rounds \
  stays in `x1`; the 112-byte working space on the stack is zeroed on return."

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact AArch64.target {
    notes := [note]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbEncrypt
    stack := 112
    verified := Proof.Cast5.AArch64.cfbEncrypt_framed },
  Spec.Cast5.cfbDecryptApi.artifact AArch64.target {
    notes := [note]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 Impl.Cast5.AArch64.cfbDecrypt
    stack := 112
    verified := Proof.Cast5.AArch64.cfbDecrypt_framed }]

end VG.Artifacts.Cast5Cfb.AArch64
