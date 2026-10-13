module

public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified

/-! # Camellia-OFB artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.AArch64

/-- How the functions compute Camellia, and the mode. -/
def note : String :=
  "Baseline AArch64: one block at a time (each block's input depends on the block before), encrypted bitsliced in \
  general-purpose registers (the S-boxes as Boolean circuits), with no table lookups, in a batch of eight of which \
  the other seven are unused; the subkeys are prepared once per call. The mode is the generic OFB of \
  `Impl/Modes/AArch64/`, over Camellia's ECB core, with the IV's address kept in a vector register across the \
  core's code."

def artifacts : List Artifact := [
  { Spec.Camellia.ofbApi with
    target := AArch64.target
    doc := Spec.Camellia.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x5 406 Impl.Camellia.AArch64.ofb
    contract := Spec.Camellia.ofbContract AArch64.abi 3248
    stack := 3248
    verified := Proof.Camellia.AArch64.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CamelliaOfb.AArch64
