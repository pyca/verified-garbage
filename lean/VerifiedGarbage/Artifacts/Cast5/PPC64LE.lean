module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
public import VerifiedGarbage.Proof.Cast5.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit

/-! CAST5 key expansion and ECB on PPC64LE. -/

@[expose] public section

namespace VG.Artifacts.Cast5.PPC64LE

/-- How ECB reads the S-boxes in constant time. -/
def scanNote : String :=
  "Each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, entry `i` the \
  four words `S4[i], S3[i], S2[i], S1[i]`: a loop over the 256 entries in order, at addresses that \
  depend only on the entry's number, loads each of the entry's words and keeps it under a mask that \
  is all ones exactly when the index of the corresponding lookup is the entry's number (`xor`, then \
  `0 - ((x - 1) >> 63)`), so the four lookups of a round function are made together and no secret \
  is an address or a branch condition. The table's address is formed position-independently with \
  `bcl 20, 31` and `mflr`, then `addis`/`addi` of its offset. The rotation by the secret `Kr` is \
  five rotations by 1, 2, 4, 8 and 16, each kept or not under a mask made from a bit of `Kr`. One \
  block at a time, one round at a time; the round's type is a public count. `scratch` holds `LR` \
  and our caller's r14-r30."

/-- How key expansion reads the S-boxes in constant time. -/
def keyNote : String :=
  "Key expansion keeps `x` and `z` in `scratch` and runs each half of §2.4 as 40 steps, each one scan \
  of the static `VG_CAST5_S5678`, entry `i` the four words `S8[i], S7[i], S6[i], S5[i]` (as for ECB), \
  for four lookups at once: a group of four lines' extra lookups, or a line's main lookups. The step's \
  bytes and what it does with the four values are chosen by comparing the public step number. Only \
  `key_len` decides the number of bytes copied. `scratch` also holds `LR` and our caller's r14-r30."

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact PPC64LE.target {
    notes := [keyNote]
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.PPC64LE.expandKey
    verified := Proof.Cast5.PPC64LE.expandKey_verified },
  Spec.Cast5.ecbEncryptApi.artifact PPC64LE.target {
    notes := [scanNote]
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.PPC64LE.ecbEncrypt
    verified := Proof.Cast5.PPC64LE.ecbEncrypt_verified },
  Spec.Cast5.ecbDecryptApi.artifact PPC64LE.target {
    notes := [scanNote]
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.PPC64LE.ecbDecrypt
    verified := Proof.Cast5.PPC64LE.ecbDecrypt_verified }]

end VG.Artifacts.Cast5.PPC64LE
