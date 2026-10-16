module

public import VerifiedGarbage.Proof.Blowfish.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Spec.Rc2
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
  Spec.Blowfish.cbcEncryptApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcEncrypt
    stack := 96
    verified := Proof.Blowfish.X86_64.cbcEncrypt_framed },
  Spec.Blowfish.cbcDecryptApi.artifact X86_64.target {
    notes := [note]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcDecrypt
    stack := 96
    verified := Proof.Blowfish.X86_64.cbcDecrypt_framed }]

end VG.Artifacts.BlowfishCbc.X86_64
