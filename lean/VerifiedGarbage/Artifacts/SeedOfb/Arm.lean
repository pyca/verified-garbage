module

public import VerifiedGarbage.Proof.Seed.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.Arm

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic OFB of `Impl/Modes/Arm/`, one block at a time (each output block is the cipher of the one before), calling the verified `vg_seed_ecb_encrypt` on the chaining value in a 72-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.ofb
    stack := 832
    verified := Proof.Seed.Arm.ofb_framed }]

end VG.Artifacts.SeedOfb.Arm
