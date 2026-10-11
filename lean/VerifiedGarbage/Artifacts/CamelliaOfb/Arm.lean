import VerifiedGarbage.Proof.Camellia.Arm.FbVerified

/-! # Camellia-OFB artifacts on baseline ARMv7 -/

namespace VG.Artifacts.CamelliaOfb.Arm

def artifacts : List Artifact := [
  { Spec.Camellia.ofbApi with
    target := Arm.target
    doc := Spec.Camellia.ofbApi.doc
      (notes := ["Baseline ARMv7: the generic OFB of `Impl/Modes/Arm/`, one block at a time (each output block is the cipher of the one before), calling the verified `vg_camellia_ecb_encrypt` (bitsliced, in a batch of eight) on the chaining value with the number of rounds, in a 72-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ofb
    contract := Spec.Camellia.ofbContract Arm.abi 2904
    stack := 2904
    verified := Proof.Camellia.Arm.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CamelliaOfb.Arm
