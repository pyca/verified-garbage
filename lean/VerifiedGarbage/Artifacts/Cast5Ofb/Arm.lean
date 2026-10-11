import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified

/-! # CAST5-OFB artifacts on baseline ARMv7 -/

namespace VG.Artifacts.Cast5Ofb.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic OFB of `Impl/Modes/Arm/`, one block at a time, " ++
  "calling the verified `vg_cast5_ecb_encrypt` (which scans the S-boxes written into its code, so no secret is an address) on the chaining value with the number of rounds and, as its stack argument, the end of a 312-byte working space on the stack (the mode's 56 bytes, then the 256 the ECB function works in), zeroed on return."

def artifacts : List Artifact := [
  { Spec.Cast5.ofbApi with
    target := Arm.target
    doc := Spec.Cast5.ofbApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.ofb
    contract := Spec.Cast5.ofbContract Arm.abi 336
    stack := 336
    verified := Proof.Cast5.Arm.ofb_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Cast5Ofb.Arm
