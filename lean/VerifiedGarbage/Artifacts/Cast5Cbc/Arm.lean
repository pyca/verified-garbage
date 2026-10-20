module

public import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CBC of `Impl/Modes/Arm/`, one block at a time, " ++
  "calling the verified `vg_cast5_ecb_encrypt` or `vg_cast5_ecb_decrypt` (which scans the S-boxes in the static `VG_CAST5_S1234`, so no secret is an address) on each block with the number of rounds and, as its stack argument, the end of a 312-byte working space on the stack (the mode's 56 bytes, then the 256 the ECB function works in), zeroed on return."

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact Arm.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.cbcEncryptChained
    stack := 336
    verified := Proof.Cast5.Arm.cbcEncryptChained_framed },
  Spec.Cast5.cbcDecryptChainedApi.artifact Arm.target {
    notes := [note, "The chaining value, the last ciphertext block, goes back to the IV at the end."]
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.cbcDecryptChained
    stack := 336
    verified := Proof.Cast5.Arm.cbcDecryptChained_framed }]

end VG.Artifacts.Cast5Cbc.Arm
