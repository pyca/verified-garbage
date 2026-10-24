module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact PPC64LE.target {
    notes := ["This implementation writes `EM = 0x00 || 0x02 || PS || 0x00 || M` to its frame, collecting \
      whether `PS` has a zero byte without branching, calls `vg_rsa_public_precomputed_checked` with the \
      cached modulus values into `out`, then masks `out` and the result to zeros if `PS` has a zero byte \
      and zeroes `EM`. It uses 2224 bytes of stack, its frame (that of `vg_rsa_pkcs1_verify_precomputed`): \
      the call uses none."]
    code := Impl.RsaPkcs1Enc.PPC64LE.Precomputed.code
    stack := 2224
    verified := Proof.RsaPkcs1Enc.PPC64LE.Enc.code_verified },
  Spec.RsaPkcs1Enc.decryptApi.artifact PPC64LE.target {
    notes := ["This implementation computes `EM` into `out` with `vg_rsa_private_checked`, whose frame \
        lies below its own, then the implicit rejection's key derivation key from `d` and the \
        ciphertext with SHA-256 and HMAC-SHA-256 and the alternative message and length with \
        IRPRF, all in the working space. It scans `EM` for the padding without a branch on its \
        bytes, and selects the output and its length byte by byte under masks of the padding's \
        validity and of the private-key operation's success. Its frame of 304 bytes holds the \
        arguments, the private-key operation's result, the counters and the callee's stack \
        arguments."]
    code := Impl.RsaPkcs1Enc.PPC64LE.Decrypt.code
    stack := Proof.RsaPkcs1Enc.PPC64LE.Dec.stackBytes
    verified := Proof.RsaPkcs1Enc.PPC64LE.Dec.dec_verified }]

end VG.Artifacts.RsaPkcs1Enc.PPC64LE
