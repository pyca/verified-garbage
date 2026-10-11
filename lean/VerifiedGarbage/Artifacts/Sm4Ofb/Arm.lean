import VerifiedGarbage.Proof.Sm4.Arm.FbVerified

/-! # SM4-OFB artifacts on baseline ARMv7 -/

namespace VG.Artifacts.Sm4Ofb.Arm

def artifacts : List Artifact := [
  { Spec.Sm4.ofbApi with
    target := Arm.target
    doc := Spec.Sm4.ofbApi.doc
      (notes := ["Baseline ARMv7: the generic OFB of `Impl/Modes/Arm/`, one block at a time (each output block is the cipher of the one before), calling the verified `vg_sm4_ecb_encrypt` on the chaining value in a 72-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.ofb
    contract := Spec.Sm4.ofbContract Arm.abi 1536
    stack := 1536
    verified := Proof.Sm4.Arm.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4Ofb.Arm
