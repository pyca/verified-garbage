module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.PPC64LE

def artifacts : List Artifact := [
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
