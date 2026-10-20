module

public import VerifiedGarbage.Proof.Cast5.AArch64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! CAST5 key expansion and ECB on baseline AArch64. -/

@[expose] public section

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
  Spec.Cast5.expandKeyApi.artifact AArch64.target {
    notes := [keyNote]
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.AArch64.expandKey
    stack := 0
    verified := Proof.Cast5.AArch64.expandKey_verified },
  Spec.Cast5.ecbEncryptApi.artifact AArch64.target {
    notes := [scanNote]
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.AArch64.ecbEncrypt
    stack := 0
    verified := Proof.Cast5.AArch64.ecbEncrypt_verified },
  Spec.Cast5.ecbDecryptApi.artifact AArch64.target {
    notes := [scanNote]
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.AArch64.ecbDecrypt
    stack := 0
    verified := Proof.Cast5.AArch64.ecbDecrypt_verified }]

end VG.Artifacts.Cast5.AArch64
