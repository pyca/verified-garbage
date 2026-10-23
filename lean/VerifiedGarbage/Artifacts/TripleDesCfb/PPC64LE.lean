module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-! # Triple DES-CFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.PPC64LE

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline PPC64LE: one block at a time, calling the verified block function (`vg_triple_des_encrypt_block`), \
  with Boolean S-box circuits and no table lookups, reading the schedule in place. The mode is the \
  generic CFB of `Impl/Modes/PPC64LE/`, which keeps its state in `r29`–`r31`."

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfbEncrypt
    stack := 608
    verified := Proof.TripleDes.PPC64LE.cfbEnc_framed Proof.TripleDes.PPC64LE.Modes.cfbEncrypt_verified },
  Spec.TripleDes.cfbDecryptApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfbDecrypt
    stack := 608
    verified := Proof.TripleDes.PPC64LE.cfbDec_framed Proof.TripleDes.PPC64LE.Modes.cfbDecrypt_verified }]

end VG.Artifacts.TripleDesCfb.PPC64LE
