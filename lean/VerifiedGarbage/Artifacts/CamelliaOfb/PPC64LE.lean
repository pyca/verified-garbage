module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit

/-! # Camellia-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.PPC64LE

/-- How the functions compute Camellia, and the mode. -/
def note : String :=
  "Baseline PPC64LE: one block at a time, through the bodies of `vg_camellia_prepare_keys` and \
  `vg_camellia_crypt_prepared` (inlined): bitsliced in general-purpose registers, each half as eight \
  64-bit planes, the S-boxes as Boolean circuits, with no table lookups, in a batch of eight of which \
  the other seven are unused; the table of bitsliced subkeys is built once per call. The mode is the \
  generic one of `Impl/Modes/PPC64LE/`, which keeps its state in `r29`–`r31`; the number of rounds \
  waits in `r28`, the caller's saved in the working space. The bodies use every callee-saved register, \
  which they save in the working space and restore, while the values the mode must keep wait in \
  registers they do not write. The working space (3376 bytes) is on the stack, zeroed before \
  returning."

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ofb
    stack := 3408
    verified := Proof.Camellia.PPC64LE.ofb_framed Proof.Camellia.PPC64LE.Modes.ofb_verified }]

end VG.Artifacts.CamelliaOfb.PPC64LE
