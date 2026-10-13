module

public import VerifiedGarbage.Proof.Sm4.Arm.FbVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! # SM4-CFB128 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB of `Impl/Modes/Arm/`, one block at a time (each block's input is the ciphertext \
  block before), calling the verified `vg_sm4_ecb_encrypt` on the chaining value in a 72-byte working space on the \
  stack, zeroed on return."

def artifacts : List Artifact := [
  { Spec.Sm4.cfbEncryptApi with
    target := Arm.target
    doc := Spec.Sm4.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbEncrypt
    contract := Spec.Sm4.cfbEncryptContract Arm.abi 1560
    stack := 1560
    verified := Proof.Sm4.Arm.cfbEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sm4.cfbDecryptApi with
    target := Arm.target
    doc := Spec.Sm4.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbDecrypt
    contract := Spec.Sm4.cfbDecryptContract Arm.abi 1560
    stack := 1560
    verified := Proof.Sm4.Arm.cfbDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sm4Cfb.Arm
