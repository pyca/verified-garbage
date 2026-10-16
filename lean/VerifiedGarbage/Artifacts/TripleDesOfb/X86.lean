module

public import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.FbLit

/-! # Triple DES-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.X86

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, calling the verified block function (`vg_triple_des_encrypt_block`), \
  with Boolean S-box circuits and no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic OFB of `Impl/Modes/X86/`."

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofb
    stack := 984
    verified := Proof.TripleDes.X86.Fb.ofb_framed }]

end VG.Artifacts.TripleDesOfb.X86
