import VerifiedGarbage.Proof.TripleDes.Arm.FbVerified

/-! # Triple DES-OFB artifacts on baseline ARMv7 -/

namespace VG.Artifacts.TripleDesOfb.Arm

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline ARMv7: the generic OFB of `Impl/Modes/Arm/`, calling the verified \
  `vg_triple_des_ecb_encrypt` on one block at a time, with the chaining block in a 56-byte working \
  space on the stack, zeroed on return."

def artifacts : List Artifact := [
  { Spec.TripleDes.ofbApi with
    target := Arm.target
    doc := Spec.TripleDes.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofb
    contract := Spec.TripleDes.ofbContract Arm.abi 1088
    stack := 1088
    verified := Proof.TripleDes.Arm.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.TripleDesOfb.Arm
