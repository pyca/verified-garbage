module

public import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Impl.Aes.Arm.Alloc

/-! # CAST5-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CBC of `Impl/Modes/Arm/`, one block at a time, " ++
  "calling the verified `vg_cast5_ecb_encrypt` or `vg_cast5_ecb_decrypt` (which scans the S-boxes in the static `VG_CAST5_S1234`, so no secret is an address) on each block with the number of rounds and, as its stack argument, the end of a 312-byte working space on the stack (the mode's 56 bytes, then the 256 the ECB function works in), zeroed on return."

def artifacts : List Artifact := [
  { Spec.Cast5.cbcEncryptApi with
    target := Arm.target
    doc := Spec.Cast5.cbcEncryptApi.doc (notes := [note])
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.cbcEncrypt
    contract := Spec.Cast5.cbcEncryptContract (Arm.abi.withConsts Impl.Cast5.ecbConsts) 336
    stack := 336
    verified := Proof.Cast5.Arm.cbcEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cast5.cbcDecryptApi with
    target := Arm.target
    doc := Spec.Cast5.cbcDecryptApi.doc (notes := [note])
    consts := Impl.Cast5.ecbConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 Impl.Cast5.Arm.cbcDecrypt
    contract := Spec.Cast5.cbcDecryptContract (Arm.abi.withConsts Impl.Cast5.ecbConsts) 336
    stack := 336
    verified := Proof.Cast5.Arm.cbcDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Cast5Cbc.Arm
