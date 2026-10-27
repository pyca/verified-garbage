module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit

/-! # Camellia-CFB128 artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.PPC64LE

/-- How the functions compute Camellia, and the mode. -/
def note : String :=
  "Baseline PPC64LE: one block at a time, bitsliced in general-purpose registers, each half as eight \
  64-bit planes, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which \
  the other seven are unused: the table of bitsliced subkeys is built once per call, by the body of \
  `vg_camellia_prepare_keys` (inlined), and each block is a call of `vg_camellia_crypt_prepared`. The mode is the \
  generic one of `Impl/Modes/PPC64LE/`, which keeps its state in `r29`–`r31`; the number of rounds \
  waits in `r28`, the caller's saved in the working space. Both functions use every callee-saved register, which they save in the working space and restore; while \
  the inlined body runs, which stores through a pointer that the analysis of constant time cannot place, the values \
  the mode must keep wait in registers it does not write. The working space (3376 bytes) is on the stack, zeroed before \
  returning."

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbEncrypt
    stack := 3408
    verified := Proof.Camellia.PPC64LE.cfbEnc_framed Proof.Camellia.PPC64LE.Modes.cfbEncrypt_verified },
  Spec.Camellia.cfbDecryptApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cfbDecrypt
    stack := 3408
    verified := Proof.Camellia.PPC64LE.cfbDec_framed Proof.Camellia.PPC64LE.Modes.cfbDecrypt_verified }]

end VG.Artifacts.CamelliaCfb.PPC64LE
