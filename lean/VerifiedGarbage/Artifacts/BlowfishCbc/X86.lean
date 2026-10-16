module

public import VerifiedGarbage.Proof.Blowfish.X86.CbcVerified
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.X86

/-- How the functions compute Blowfish, and the mode. -/
def note : String :=
  "One block at a time: each S-box lookup reads the 256 entries of its four byte planes under masks, \
  as in ECB, and the schedule is read in place through its argument. The mode is the generic CBC of \
  `Impl/Modes/X86/`, over Blowfish's ECB block."

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cbcEncrypt
    stack := 112
    verified := Proof.Blowfish.X86.cbcEncrypt_framed },
  Spec.Blowfish.cbcDecryptApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cbcDecrypt
    stack := 112
    verified := Proof.Blowfish.X86.cbcDecrypt_framed }]

end VG.Artifacts.BlowfishCbc.X86
