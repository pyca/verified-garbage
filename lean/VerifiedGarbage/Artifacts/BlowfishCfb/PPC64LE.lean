module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit

/-! # Blowfish-CFB64 artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.PPC64LE

/-- How the functions compute Blowfish, and the mode. -/
def note : String :=
  "Baseline PPC64LE: one block at a time, with ECB's verified block function inlined (each S-box lookup reads all 256 entries of its byte planes under masks, so no address depends on the data or the schedule), reading the schedule in place. The mode is the generic one of `Impl/Modes/PPC64LE/`, which keeps its state in `r29`–`r31`; our caller's `r14`–`r17`, which the block function uses, are saved in the working space, which is zeroed before returning."

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbEncrypt
    stack := 128
    verified := Proof.Blowfish.PPC64LE.cfbEnc_framed Proof.Blowfish.PPC64LE.Modes.cfbEncrypt_verified },
  Spec.Blowfish.cfbDecryptApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cfbDecrypt
    stack := 128
    verified := Proof.Blowfish.PPC64LE.cfbDec_framed Proof.Blowfish.PPC64LE.Modes.cfbDecrypt_verified }]

end VG.Artifacts.BlowfishCfb.PPC64LE
