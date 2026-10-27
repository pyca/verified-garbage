module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit

/-! # Camellia-CTR artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.PPC64LE

/-- How the functions compute Camellia, and the mode. -/
def note : String :=
  "Baseline PPC64LE: one counter block at a time, bitsliced in general-purpose registers, each half as eight \
  64-bit planes, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which \
  the other seven are unused: the table of bitsliced subkeys is built once per call, by the body of \
  `vg_camellia_prepare_keys` (inlined), and each block is a call of `vg_camellia_crypt_prepared`. The mode is the \
  generic CTR of `Impl/Modes/PPC64LE/`, the counter incremented branch-free, which keeps its state \
  in `r29`–`r31`; the number of rounds waits in `r28`, the caller's saved in the working space. Both functions use every callee-saved register, which they save in the working space and restore; while \
  the inlined body runs, which stores through a pointer that the analysis of constant time cannot place, the values \
  the mode must keep wait in registers it does not write. The working space (3376 bytes) is on the stack, zeroed before \
  returning."

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ctr
    stack := 3408
    verified := Proof.Camellia.PPC64LE.ctr_framed Proof.Camellia.PPC64LE.Modes.ctr_verified }]

end VG.Artifacts.CamelliaCtr.PPC64LE
