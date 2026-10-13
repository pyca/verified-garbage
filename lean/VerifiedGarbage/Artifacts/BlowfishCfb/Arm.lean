module

public import VerifiedGarbage.Proof.Blowfish.Arm.FbVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Blowfish.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms

/-! # Blowfish-CFB128 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.Arm

/-- How the functions compute the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB of `Impl/Modes/Arm/`, one block at a time (each block's input is the ciphertext \
  block before), calling the verified `vg_blowfish_ecb_encrypt` on the chaining value in a 56-byte working space on the \
  stack, zeroed on return."

def artifacts : List Artifact := [
  { Spec.Blowfish.cfbEncryptApi with
    target := Arm.target
    doc := Spec.Blowfish.cfbEncryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbEncrypt
    contract := Spec.Blowfish.cfbEncryptContract Arm.abi 320
    stack := 320
    verified := Proof.Blowfish.Arm.cfbEncrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blowfish.cfbDecryptApi with
    target := Arm.target
    doc := Spec.Blowfish.cfbDecryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.Blowfish.Arm.cfbDecrypt
    contract := Spec.Blowfish.cfbDecryptContract Arm.abi 320
    stack := 320
    verified := Proof.Blowfish.Arm.cfbDecrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.BlowfishCfb.Arm
