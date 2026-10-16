module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.PrecomputedCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecPcCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PKCS #1 v1.5 verification and recovery over precomputed RSA public variants -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.X86_64.RsaPkcs1Sig

open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.RsaPkcs1Sig.X86_64

def artifacts (v : PublicImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation calls `" ++ v.name ++
      "` with the cached modulus values, then compares the recovered encoding with EMSA-PKCS1-v1_5's \
      encoding of `digest`. It combines the padding result with the public operation's status without \
      branching on that status. It uses 2144 bytes of stack, including the call's return address."]
    code := Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code
    stack := verStack
    verified := PcCT.code_verified v
    spSafe := PcCT.code_spSafe v
    features := v.features },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation calls `" ++ v.name ++
      "` with the cached modulus values into its frame, writes EMSA-PKCS1-v1_5's encoding of the last \
      `out_len` bytes of the result beside it and compares the two, then copies those bytes to `out` and \
      masks them to zeros, and the result to 0, unless the public operation succeeded and the two are \
      equal: nothing after the call branches on its result. It uses 2144 bytes of stack, including \
      the call's return address."]
    code := Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code
    stack := verStack
    verified := RecPcCT.code_verified v
    spSafe := RecPcCT.code_spSafe v
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.X86_64.RsaPkcs1Sig
