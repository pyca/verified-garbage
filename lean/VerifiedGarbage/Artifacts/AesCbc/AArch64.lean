module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Lit

/-! # AES-CBC decryption with seven independent AES states -/

@[expose] public section

namespace VG.Artifacts.AesCbc.AArch64

def artifacts : List Artifact := [
  Spec.Cbc.aesDecryptApi.artifact VG.AArch64.target {
    suffix := "_aes_sha3"
    notes := ["With FEAT_AES and FEAT_SHA3: seven interleaved inverse-cipher states, with the inverse round keys prepared once and kept in registers. EOR3 combines the final round-key XOR and CBC chaining XOR. Remaining blocks use the same resident keys, one at a time. No stack or scratch memory is used."]
    code := Impl.AesCbc.AArch64.Decrypt.code
    verified := Proof.AesCbc.AArch64.Decrypt.verified
    features := ["aes","sha3"]
    written := [("scratch",0)]
    writtenOk := Proof.AesCbc.AArch64.Decrypt.written }]

end VG.Artifacts.AesCbc.AArch64
