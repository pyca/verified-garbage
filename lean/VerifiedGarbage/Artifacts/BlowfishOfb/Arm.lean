module

public import VerifiedGarbage.Proof.Blowfish.Arm.FbVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Blowfish.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Impl.Aes.Arm.Alloc
import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the generic OFB of `Impl/Modes/Arm/`, one block at a time (each output block is the cipher of the one before), calling the verified `vg_blowfish_ecb_encrypt` on the chaining value in a 56-byte working space on the stack, zeroed on return."]
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.ofb
    stack := 320
    verified := Proof.Blowfish.Arm.ofb_framed }]

end VG.Artifacts.BlowfishOfb.Arm
