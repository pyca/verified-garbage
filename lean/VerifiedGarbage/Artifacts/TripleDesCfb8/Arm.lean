module

public import VerifiedGarbage.Proof.TripleDes.Arm.FbVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms

/-! # Triple DES-CFB8 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.Arm

/-- How the functions compute Triple DES, and the mode. -/
def note : String :=
  "Baseline ARMv7: the generic CFB8, a byte at a time, of `Impl/Modes/Arm/`, calling the verified \
  `vg_triple_des_ecb_encrypt` on one block per byte, with the chaining block in a 56-byte working \
  space on the stack, zeroed on return."

def artifacts : List Artifact := [
  { Spec.TripleDes.cfb8EncryptApi with
    target := Arm.target
    doc := Spec.TripleDes.cfb8EncryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Encrypt
    contract := Spec.TripleDes.cfb8EncryptContract Arm.abi 1088
    stack := 1088
    verified := Proof.TripleDes.Arm.cfb8Encrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.TripleDes.cfb8DecryptApi with
    target := Arm.target
    doc := Spec.TripleDes.cfb8DecryptApi.doc (notes := [note])
    code := Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Decrypt
    contract := Spec.TripleDes.cfb8DecryptContract Arm.abi 1088
    stack := 1088
    verified := Proof.TripleDes.Arm.cfb8Decrypt_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.TripleDesCfb8.Arm
