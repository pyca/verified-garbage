module

public import VerifiedGarbage.Proof.Blowfish.X86_64.CbcVerified
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.X86_64

/-- How the functions compute Blowfish, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through `vg_blowfish_ecb_encrypt`'s block code (inlined): \
  each S-box lookup scans every entry of the box in SSE2 registers, so no address depends on the key or \
  the data; the schedule is read where it is. The mode is the generic CBC of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact X86_64.target {
    notes := [note, "The IV's address is kept in `xmm15`, and after the last block the core's buffer, the last ciphertext block, goes back to the IV."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcEncryptChained
    stack := 96
    verified := Proof.Blowfish.X86_64.cbcEncryptChained_framed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact X86_64.target {
    notes := [note, "The last ciphertext block is copied to the IV before any block is decrypted."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcDecryptChained
    stack := 96
    verified := Proof.Blowfish.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.BlowfishCbc.X86_64
