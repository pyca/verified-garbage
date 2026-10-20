module

public import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.X86

/-- How the functions compute CAST5, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, through the generic CBC of `Impl/Modes/X86/` over CAST5's ECB \
  block code: each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, \
  so no secret is an address. The subkeys and the number of rounds are reloaded from the arguments for each block."

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact X86.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cbcEncryptChained
    stack := 336
    verified := Proof.Cast5.X86.ModeFns.cbcEncryptChained_framed },
  Spec.Cast5.cbcDecryptChainedApi.artifact X86.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cbcDecryptChained
    stack := 336
    verified := Proof.Cast5.X86.ModeFns.cbcDecryptChained_framed }]

end VG.Artifacts.Cast5Cbc.X86
