module

public import VerifiedGarbage.Proof.Camellia.Arm.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.Arm

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic OFB of `Impl/Modes/Arm/`, one block at a time (each output block is the cipher of the one before), calling the verified `vg_camellia_ecb_encrypt` (bitsliced, in a batch of eight) on the chaining value with the number of rounds, in a 72-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ofb
    stack := 2904
    verified := Proof.Camellia.Arm.ofb_framed }]

end VG.Artifacts.CamelliaOfb.Arm
