import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified

/-! # Triple DES-OFB artifacts on baseline AArch64 -/

namespace VG.Artifacts.TripleDesOfb.AArch64

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time, through the scalar block function (`vg_triple_des_encrypt_block`'s \
  code, inlined), with Boolean S-box circuits and no table lookups; the schedule is copied into the working \
  space once per call. The mode is the generic OFB of `Impl/Modes/AArch64/`."

def artifacts : List Artifact := [
  { Spec.TripleDes.ofbApi with
    target := AArch64.target
    doc := Spec.TripleDes.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 Impl.TripleDes.AArch64.ofb
    contract := Spec.TripleDes.ofbContract AArch64.abi 1008
    stack := 1008
    verified := Proof.TripleDes.AArch64.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.TripleDesOfb.AArch64
