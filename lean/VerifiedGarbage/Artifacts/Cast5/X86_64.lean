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
  "Each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, entry `i` \
  the four dwords `S4[i], S3[i], S2[i], S1[i]`: every entry is loaded in order, compared with \
  the four indices in the lanes of an SSE2 register (`pcmpeqd`) and kept under the resulting \
  mask, with adjacent entries combined before updating the running result, so the four lookups of a round function are made together and no secret is an address. \
  The rotation by the secret `Kr` is five rotations by 1, 2, 4, 8 and 16, each kept or not \
  under a mask. One block at a time, rounds three at a time; the callee-saved registers are \
  saved in `scratch`."

/-- How key expansion reads the S-boxes in constant time. -/
def keyNote : String :=
  "Key expansion keeps `x` and `z` in `scratch` and makes the four main lookups of each line of \
  §2.4 together by a scan of the static `VG_CAST5_S5678`, entry `i` the four dwords \
  `S8[i], S7[i], S6[i], S5[i]`, like the scans of ECB; a group of four lines makes its four \
  extra lookups by one more scan. Each scan combines adjacent entries before updating its result. Only `key_len` decides the number of bytes copied."

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
