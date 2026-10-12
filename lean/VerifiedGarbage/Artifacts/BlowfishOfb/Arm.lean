import VerifiedGarbage.Proof.Blowfish.Arm.FbVerified

/-! # Blowfish-OFB artifacts on baseline ARMv7 -/

namespace VG.Artifacts.BlowfishOfb.Arm

def artifacts : List Artifact := [
  { Spec.Blowfish.ofbApi with
    target := Arm.target
    doc := Spec.Blowfish.ofbApi.doc
      (notes := ["Baseline ARMv7: the generic OFB of `Impl/Modes/Arm/`, one block at a time (each output block is the cipher of the one before), calling the verified `vg_blowfish_ecb_encrypt` on the chaining value in a 56-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.ofb
    contract := Spec.Blowfish.ofbContract Arm.abi 320
    stack := 320
    verified := Proof.Blowfish.Arm.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.BlowfishOfb.Arm
