import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Cast5.Arm.EcbVerified
import VerifiedGarbage.Proof.Cast5.Arm.KeyVerified

/-! CAST5 key expansion and ECB on baseline ARMv7. -/

namespace VG.Artifacts.Cast5.Arm

/-- How ECB reads the S-boxes in constant time. -/
def scanNote : String :=
  "Baseline ARMv7 has no table addressing and no SIMD in this model, so each S-box lookup is a scan \
  of the whole table written into the code: for each of the 256 entries in order, each of the four \
  indices of a round function is compared with the entry's number (`eor`, then `(x - 1) >> 8` widened \
  to a mask that is all ones exactly on a match) and the entry's word, built with `movw`/`movt`, is \
  kept under the mask. No secret is an address or a branch condition. The rotation by the secret \
  `Kr` is five rotations by 1, 2, 4, 8 and 16, each kept or not under a mask made from a bit of \
  `Kr`. One block at a time, one round at a time; the round's type is a public count. `scratch` \
  holds the callee-saved registers and the loop's public state."

/-- How key expansion reads the S-boxes in constant time. -/
def keyNote : String :=
  "Key expansion keeps `x` and `z` in `scratch` and runs each half of §2.4 as 40 steps, each one scan \
  of `S5`–`S8` written into the code (as for ECB) for four lookups at once: a group of four lines' \
  extra lookups, or a line's main lookups. The step's bytes and what it does with the four values \
  are chosen by comparing the public step number. Only `key_len` decides the number of bytes copied."

def artifacts : List Artifact := [
  { Spec.Cast5.expandKeyApi with
    target := Arm.target
    doc := Spec.Cast5.expandKeyApi.doc (notes := [keyNote])
    code := Impl.Cast5.Arm.expandKey
    contract := Spec.Cast5.expandKeyContract Arm.abi
    stack := 0
    verified := Proof.Cast5.Arm.expandKey_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cast5.ecbEncryptApi with
    target := Arm.target
    doc := Spec.Cast5.ecbEncryptApi.doc (notes := [scanNote])
    code := Impl.Cast5.Arm.ecbEncrypt
    contract := Spec.Cast5.ecbEncryptContract Arm.abi
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.Cast5.ecbEncryptContract Spec.Cast5.ecbContract; rfl⟩
    verified := Proof.Cast5.Arm.ecbEncrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cast5.ecbDecryptApi with
    target := Arm.target
    doc := Spec.Cast5.ecbDecryptApi.doc (notes := [scanNote])
    code := Impl.Cast5.Arm.ecbDecrypt
    contract := Spec.Cast5.ecbDecryptContract Arm.abi
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.Cast5.ecbDecryptContract Spec.Cast5.ecbContract; rfl⟩
    verified := Proof.Cast5.Arm.ecbDecrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Cast5.Arm
