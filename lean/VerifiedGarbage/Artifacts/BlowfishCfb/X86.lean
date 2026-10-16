module

public import VerifiedGarbage.Proof.Blowfish.X86.FbVerified
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.X86

/-- How the functions compute Blowfish, and the mode. -/
def note : String :=
  "One block at a time: each S-box lookup reads the 256 entries of its four byte planes under masks, \
  as in ECB, and the schedule is read in place through its argument. The mode is the generic CFB of \
  `Impl/Modes/X86/`, over Blowfish's ECB block."

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbEncrypt
    stack := 112
    verified := Proof.Blowfish.X86.Fb.cfbEncrypt_framed },
  Spec.Blowfish.cfbDecryptApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbDecrypt
    stack := 112
    verified := Proof.Blowfish.X86.Fb.cfbDecrypt_framed }]

end VG.Artifacts.BlowfishCfb.X86
