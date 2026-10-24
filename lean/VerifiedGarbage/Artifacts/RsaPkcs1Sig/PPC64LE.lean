module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.VerifyVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PKCS #1 v1.5 verification and recovery with a precomputed RSA public key on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact PPC64LE.target {
    notes := ["This implementation calls `vg_rsa_public_precomputed_checked` with the cached modulus \
      values, then compares the recovered encoding with EMSA-PKCS1-v1_5's encoding of `digest`. It \
      combines the padding result with the public operation's status without branching on that status. \
      It uses 2224 bytes of stack, its frame: the call uses none."]
    code := Impl.RsaPkcs1Sig.PPC64LE.Precomputed.code
    stack := 2224
    verified := Proof.RsaPkcs1Sig.PPC64LE.Ver.code_verified },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact PPC64LE.target {
    notes := ["This implementation calls `vg_rsa_public_precomputed_checked` with the cached modulus \
      values into its frame, writes EMSA-PKCS1-v1_5's encoding of the last `out_len` bytes of the result \
      beside it and compares the two, then copies those bytes to `out` and masks them to zeros, and the \
      result to 0, unless the public operation succeeded and the two are equal: nothing after the call \
      branches on its result. It uses 2224 bytes of stack, its frame: the call uses none."]
    code := Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed.code
    stack := 2224
    verified := Proof.RsaPkcs1Sig.PPC64LE.Rec.code_verified }]

end VG.Artifacts.RsaPkcs1Sig.PPC64LE
