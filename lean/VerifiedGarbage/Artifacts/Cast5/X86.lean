import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Cast5.X86.EcbVerified
import VerifiedGarbage.Proof.Cast5.X86.KeyVerified

/-! CAST5 key expansion and ECB on baseline 32-bit x86. -/

namespace VG.Artifacts.Cast5.X86

/-- How the S-boxes are read in constant time. -/
def scanNote : String :=
  "Each S-box lookup is a scan of the whole table in the static `VG_CAST5_S1234`, entry `i` \
  the four dwords `S4[i], S3[i], S2[i], S1[i]`: every entry is loaded in order, ANDed with a mask \
  that is all ones in the SSE2 lanes whose index is `i` and ORed into the result, so the four \
  lookups of a round function are made together and no secret is an address. The mask of entry \
  `i` is built from `d = idx ^ i`, below 256: `(d - 1) >> 8`, ORed with itself shifted left by 8. \
  The rotation by the secret `Kr` is five rotations by 1, 2, 4, 8 and 16, each kept or not under \
  a mask. One block at a time, rounds three at a time; each scan obtains the table's address in a \
  position-independent four-byte CALL frame. `scratch` holds the callee-saved registers and the \
  loop's public state."

/-- How key expansion reads the S-boxes in constant time. -/
def keyNote : String :=
  "Key expansion keeps `x` and `z` in `scratch` and makes the four main lookups of each line of \
  §2.4 together by a scan of the static `VG_CAST5_S5678`, entry `i` the four dwords \
  `S8[i], S7[i], S6[i], S5[i]`, like the scans of ECB; a group of four lines makes its four \
  extra lookups by one more scan. Only `key_len` decides the number of bytes copied. The \
  callee-saved registers are saved in `scratch`."

def artifacts : List Artifact := [
  { Spec.Cast5.expandKeyApi with
    target := X86.target
    doc := Spec.Cast5.expandKeyApi.doc (notes := [keyNote])
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.X86.expandKey
    contract := Spec.Cast5.expandKeyContract (X86.abi.withConsts Impl.Cast5.keyConsts) 4
    stack := 4
    ofSig := by exact (⟨_, _, _, by unfold Spec.Cast5.expandKeyContract; rfl⟩)
    verified := Proof.Cast5.X86.expandKey_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Cast5.ecbEncryptApi with
    target := X86.target
    doc := Spec.Cast5.ecbEncryptApi.doc (notes := [scanNote])
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.X86.ecbEncrypt
    contract := Spec.Cast5.ecbEncryptContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 4
    stack := 4
    ofSig := by exact (⟨_, _, _, by unfold Spec.Cast5.ecbEncryptContract Spec.Cast5.ecbContract; rfl⟩)
    verified := Proof.Cast5.X86.ecbEncrypt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Cast5.ecbDecryptApi with
    target := X86.target
    doc := Spec.Cast5.ecbDecryptApi.doc (notes := [scanNote])
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.X86.ecbDecrypt
    contract := Spec.Cast5.ecbDecryptContract (X86.abi.withConsts Impl.Cast5.ecbConsts) 4
    stack := 4
    ofSig := by exact (⟨_, _, _, by unfold Spec.Cast5.ecbDecryptContract Spec.Cast5.ecbContract; rfl⟩)
    verified := Proof.Cast5.X86.ecbDecrypt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Cast5.X86
