module

public import VerifiedGarbage.Proof.Cast5.X86_64.CbcVerified
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration

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
  Spec.Cast5.cbcEncryptChainedApi.artifact X86_64.target {
    notes := [note, "The IV's address is kept in `xmm15`, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 Impl.Cast5.X86_64.cbcEncryptChained
    stack := 240
    verified := Proof.Cast5.X86_64.cbcEncryptChained_framed },
  Spec.Cast5.cbcDecryptChainedApi.artifact X86_64.target {
    notes := [note, "The last ciphertext block is copied to the IV before any block is decrypted."]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 Impl.Cast5.X86_64.cbcDecryptChained
    stack := 240
    verified := Proof.Cast5.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.Cast5Cbc.X86_64
