module

public import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.KeyVerified
import VerifiedGarbage.Proof.Cast5.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! CAST5 key expansion and ECB on baseline x86-64. -/

@[expose] public section

namespace VG.Artifacts.Cast5.X86_64

/-- How the S-boxes are read in constant time. -/
def scanNote : String :=
  "Each S-box lookup scans the whole static `VG_CAST5_S1234` table, whose entry `i` contains \
  `S4[i], S3[i], S2[i], S1[i]`. SSE2 XOR/AND masks select among four adjacent entries using \
  the low two index bits, and `pcmpeqd` compares the remaining bits with the public group \
  number. Every entry is loaded in order, so no secret is an address. The four lookups of \
  a round function are made together. The rotation by secret `Kr` uses five masked rotations \
  by 1, 2, 4, 8 and 16. One block at a time, rounds three at a time; callee-saved registers \
  are saved in `scratch`."

/-- How key expansion reads the S-boxes in constant time. -/
def keyNote : String :=
  "Key expansion keeps `x` and `z` in `scratch` and makes the four main lookups of each line of \
  §2.4 together by a scan of the static `VG_CAST5_S5678`, entry `i` the four dwords \
  `S8[i], S7[i], S6[i], S5[i]`, like the scans of ECB; a group of four lines makes its four \
  extra lookups by one more scan. Each scan selects among four adjacent entries using SSE2 masks before updating its result. Only `key_len` decides the number of bytes copied."

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact X86_64.target {
    notes := [keyNote]
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.X86_64.expandKey
    stack := 0
    verified := Proof.Cast5.X86_64.expandKey_verified },
  Spec.Cast5.ecbEncryptApi.artifact X86_64.target {
    notes := [scanNote]
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.X86_64.ecbEncrypt
    stack := 0
    verified := Proof.Cast5.X86_64.ecbEncrypt_verified },
  Spec.Cast5.ecbDecryptApi.artifact X86_64.target {
    notes := [scanNote]
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.X86_64.ecbDecrypt
    stack := 0
    verified := Proof.Cast5.X86_64.ecbDecrypt_verified }]

end VG.Artifacts.Cast5.X86_64
