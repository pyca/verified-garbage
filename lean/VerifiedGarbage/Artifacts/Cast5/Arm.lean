module

public import VerifiedGarbage.Proof.Cast5.Arm.EcbVerified
public import VerifiedGarbage.Proof.Cast5.Arm.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! CAST5 key expansion and ECB on baseline ARMv7. -/

@[expose] public section

namespace VG.Artifacts.Cast5.Arm

/-- How ECB reads the S-boxes in constant time. -/
def scanNote : String :=
  "Each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, entry `i` the \
  four words `S4[i], S3[i], S2[i], S1[i]`: a loop over the 256 entries in order, at addresses that \
  depend only on the entry's number, loads each of the entry's words and keeps it under a mask that \
  is all ones exactly when the index of the corresponding lookup is the entry's number (`eor`, then \
  `(x - 1) >> 8` widened), so the four lookups of a round function are made together and no secret \
  is an address or a branch condition. The table's address is formed position-independently with \
  `movw`/`movt` and an `add` of `pc`. The rotation by the secret `Kr` is five rotations by 1, 2, 4, 8 \
  and 16, each kept or not under a mask made from a bit of `Kr`. One block at a time, one round at a \
  time; the round's type is a public count. `scratch` holds the callee-saved registers and the \
  loop's public state."

/-- How key expansion reads the S-boxes in constant time. -/
def keyNote : String :=
  "Key expansion keeps `x` and `z` in `scratch` and runs each half of §2.4 as 40 steps, each one scan \
  of the static `VG_CAST5_S5678`, entry `i` the four words `S8[i], S7[i], S6[i], S5[i]` (as for ECB), \
  for four lookups at once: a group of four lines' extra lookups, or a line's main lookups. The step's \
  bytes and what it does with the four values are chosen by comparing the public step number. Only \
  `key_len` decides the number of bytes copied."

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact Arm.target {
    notes := [keyNote]
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.Arm.expandKey
    stack := 0
    verified := Proof.Cast5.Arm.expandKey_verified },
  Spec.Cast5.ecbEncryptApi.artifact Arm.target {
    notes := [scanNote]
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.Arm.ecbEncrypt
    stack := 0
    verified := Proof.Cast5.Arm.ecbEncrypt_verified },
  Spec.Cast5.ecbDecryptApi.artifact Arm.target {
    notes := [scanNote]
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.Arm.ecbDecrypt
    stack := 0
    verified := Proof.Cast5.Arm.ecbDecrypt_verified }]

end VG.Artifacts.Cast5.Arm
