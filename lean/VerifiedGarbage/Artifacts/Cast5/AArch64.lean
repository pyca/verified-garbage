import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Cast5.AArch64.EcbVerified
import VerifiedGarbage.Proof.Cast5.AArch64.KeyVerified

/-! CAST5 key expansion and ECB on baseline AArch64. -/

namespace VG.Artifacts.Cast5.AArch64

/-- How the S-boxes are read in constant time. -/
def scanNote : String :=
  "Each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, entry `i` \
  the four words `S4[i], S3[i], S2[i], S1[i]`: every entry is loaded in order, compared with \
  the four indices in the lanes of an AdvSIMD register (`cmeq`) and kept under the resulting \
  mask, so the four lookups of a round function are made together and no secret is an address. \
  The rotation by the secret `Kr` is five rotations by 1, 2, 4, 8 and 16, each selected or not \
  by `csel` on a bit of `Kr`. One block at a time, rounds three at a time; `scratch` is not used."

/-- How key expansion reads the S-boxes in constant time. -/
def keyNote : String :=
  "Key expansion keeps `x` and `z` in `scratch` and makes the four main lookups of each line of \
  §2.4 together by a scan of the static `VG_CAST5_S5678`, entry `i` the four words \
  `S8[i], S7[i], S6[i], S5[i]`, like the scans of ECB; a group of four lines makes its four \
  extra lookups by one more scan, kept in an AdvSIMD register. Only `key_len` decides the number \
  of bytes copied."

def artifacts : List Artifact := [
  { Spec.Cast5.expandKeyApi with
    target := AArch64.target
    doc := Spec.Cast5.expandKeyApi.doc (notes := [keyNote])
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.AArch64.expandKey
    contract := Spec.Cast5.expandKeyContract (AArch64.abi.withConsts Impl.Cast5.keyConsts)
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.Cast5.expandKeyContract; rfl⟩
    verified := Proof.Cast5.AArch64.expandKey_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cast5.ecbEncryptApi with
    target := AArch64.target
    doc := Spec.Cast5.ecbEncryptApi.doc (notes := [scanNote])
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.AArch64.ecbEncrypt
    contract := Spec.Cast5.ecbEncryptContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts)
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.Cast5.ecbEncryptContract Spec.Cast5.ecbContract; rfl⟩
    verified := Proof.Cast5.AArch64.ecbEncrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cast5.ecbDecryptApi with
    target := AArch64.target
    doc := Spec.Cast5.ecbDecryptApi.doc (notes := [scanNote])
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.AArch64.ecbDecrypt
    contract := Spec.Cast5.ecbDecryptContract (AArch64.abi.withConsts Impl.Cast5.ecbConsts)
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.Cast5.ecbDecryptContract Spec.Cast5.ecbContract; rfl⟩
    verified := Proof.Cast5.AArch64.ecbDecrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Cast5.AArch64
