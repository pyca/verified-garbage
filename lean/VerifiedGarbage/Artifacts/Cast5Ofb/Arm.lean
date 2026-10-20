module

public import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-OFB artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic OFB of `Impl/Modes/Arm/`, one block at a time, " ++
  "calling the verified `vg_cast5_ecb_encrypt` (which scans the S-boxes in the static `VG_CAST5_S1234`, so no secret is an address) on the chaining value with the number of rounds and, as its stack argument, the end of a 312-byte working space on the stack (the mode's 56 bytes, then the 256 the ECB function works in), zeroed on return."

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact Arm.target {
    notes := [note]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.ofb
    stack := 336
    verified := Proof.Cast5.Arm.ofb_framed }]

end VG.Artifacts.Cast5Ofb.Arm
