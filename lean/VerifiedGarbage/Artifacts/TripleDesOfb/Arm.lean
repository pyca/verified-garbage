module

public import VerifiedGarbage.Proof.TripleDes.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.Arm

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline ARMv7: the generic OFB of `Impl/Modes/Arm/`, calling the verified \
  `vg_triple_des_ecb_encrypt` on one block at a time, with the chaining block in a 56-byte working \
  space on the stack, zeroed on return."

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact Arm.target {
    notes := [note]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofb
    stack := 1088
    verified := Proof.TripleDes.Arm.ofb_framed }]

end VG.Artifacts.TripleDesOfb.Arm
