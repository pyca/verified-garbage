import VerifiedGarbage.Proof.TripleDes.X86.FbVerified

/-! # Triple DES-OFB artifacts on baseline x86 (32-bit) -/

namespace VG.Artifacts.TripleDesOfb.X86

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline IA-32: one block at a time, calling the verified block function (`vg_triple_des_encrypt_block`), \
  with Boolean S-box circuits and no table lookups; the schedule is copied into the working space once per call. \
  The mode is the generic OFB of `Impl/Modes/X86/`."

def artifacts : List Artifact := [
  { Spec.TripleDes.ofbApi with
    target := X86.target
    doc := Spec.TripleDes.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofb
    contract := Spec.TripleDes.ofbContract X86.abi 984
    stack := 984
    verified := Proof.TripleDes.X86.Fb.ofb_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.TripleDesOfb.X86
