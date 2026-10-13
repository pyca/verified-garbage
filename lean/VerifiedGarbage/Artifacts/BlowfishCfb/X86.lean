module

public import VerifiedGarbage.Proof.Blowfish.X86.FbVerified
import Mathlib.Tactic.SplitIfs

/-! # Blowfish-CFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.X86

/-- How the functions compute Blowfish, and the mode. -/
def note : String :=
  "One block at a time: each S-box lookup reads the 256 entries of its four byte planes under masks, \
  as in ECB, and the schedule is read in place through its argument. The mode is the generic CFB of \
  `Impl/Modes/X86/`, over Blowfish's ECB block."

def artifacts : List Artifact := [
  { Spec.Blowfish.cfbEncryptApi with
    target := X86.target
    doc := Spec.Blowfish.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbEncrypt
    contract := Spec.Blowfish.cfbEncryptContract X86.abi 112
    stack := 112
    verified := Proof.Blowfish.X86.Fb.cfbEncrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Blowfish.cfbDecryptApi with
    target := X86.target
    doc := Spec.Blowfish.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbDecrypt
    contract := Spec.Blowfish.cfbDecryptContract X86.abi 112
    stack := 112
    verified := Proof.Blowfish.X86.Fb.cfbDecrypt_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.BlowfishCfb.X86
