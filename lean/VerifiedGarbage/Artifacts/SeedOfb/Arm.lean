import VerifiedGarbage.Proof.Seed.Arm.FbVerified

/-! # SEED-OFB artifacts on baseline ARMv7 -/

namespace VG.Artifacts.SeedOfb.Arm

def artifacts : List Artifact := [
  { Spec.Seed.ofbApi with
    target := Arm.target
    doc := Spec.Seed.ofbApi.doc
      (notes := ["Baseline ARMv7: the generic OFB of `Impl/Modes/Arm/`, one block at a time (each output block is the cipher of the one before), calling the verified `vg_seed_ecb_encrypt` on the chaining value in a 72-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.ofb
    contract := Spec.Seed.ofbContract Arm.abi 832
    stack := 832
    verified := Proof.Seed.Arm.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.SeedOfb.Arm
