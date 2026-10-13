module

public import VerifiedGarbage.Proof.Blowfish.Arm.CbcVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Blowfish.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.Framework.TaintSum

/-! # Blowfish-CBC artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.Arm

def artifacts : List Artifact := [
  { Spec.Blowfish.cbcEncryptApi with
    target := Arm.target
    doc := Spec.Blowfish.cbcEncryptApi.doc
      (notes := ["Baseline ARMv7: the generic CBC encryption of `Impl/Modes/Arm/`, one block at a time (CBC encryption is sequential), calling the verified `vg_blowfish_ecb_encrypt` on each block in a 56-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cbcEncrypt
    contract := Spec.Blowfish.cbcEncryptContract Arm.abi 320
    stack := 320
    verified := Proof.Blowfish.Arm.cbcEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blowfish.cbcDecryptApi with
    target := Arm.target
    doc := Spec.Blowfish.cbcDecryptApi.doc
      (notes := ["Baseline ARMv7: the generic CBC decryption of `Impl/Modes/Arm/`, one block at a time, calling the verified `vg_blowfish_ecb_decrypt` on each block in place, with the chaining value in a 56-byte working space on the stack, zeroed on return."])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cbcDecrypt
    contract := Spec.Blowfish.cbcDecryptContract Arm.abi 320
    stack := 320
    verified := Proof.Blowfish.Arm.cbcDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.BlowfishCbc.Arm
