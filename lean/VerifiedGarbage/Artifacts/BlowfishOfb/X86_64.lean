import VerifiedGarbage.Proof.Blowfish.X86_64.FbVerified

/-! # Blowfish-OFB artifacts on baseline x86-64 -/

namespace VG.Artifacts.BlowfishOfb.X86_64

/-- How the functions compute Blowfish, and the mode. -/
def note : String :=
  "Baseline x86-64: one block at a time, through `vg_blowfish_ecb_encrypt`'s block code (inlined): \
  each S-box lookup scans every entry of the box in SSE2 registers, so no address depends on the key or \
  the data; the schedule is read where it is. The mode is the generic OFB of `Impl/Modes/X86_64/`."

def artifacts : List Artifact := [
  { Spec.Blowfish.ofbApi with
    target := X86_64.target
    doc := Spec.Blowfish.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.ofb
    contract := Spec.Blowfish.ofbContract X86_64.abi 96
    stack := 96
    verified := Proof.Blowfish.X86_64.ofb_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.BlowfishOfb.X86_64
