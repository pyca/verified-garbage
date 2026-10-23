module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-! # Triple DES-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.PPC64LE

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline PPC64LE: one block at a time, calling the verified block function (`vg_triple_des_encrypt_block`), \
  with Boolean S-box circuits and no table lookups, reading the schedule in place. The mode is the \
  generic OFB of `Impl/Modes/PPC64LE/`, which keeps its state in `r29`–`r31`."

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact PPC64LE.target {
    notes := [note]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.ofb
    stack := 608
    verified := Proof.TripleDes.PPC64LE.ofb_framed Proof.TripleDes.PPC64LE.Modes.ofb_verified }]

end VG.Artifacts.TripleDesOfb.PPC64LE
