module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.PrecomputedCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecPcCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-! # PKCS #1 v1.5 verification and recovery over precomputed RSA public variants -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.X86_64.RsaPkcs1Sig

open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.RsaPkcs1Sig.X86_64

def artifacts (v : PublicImpl) : List Artifact := [
  { Spec.RsaPkcs1Sig.verifyPrecomputedApi with
    name := Spec.RsaPkcs1Sig.verifyPrecomputedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.RsaPkcs1Sig.verifyPrecomputedApi.doc (notes := ["This implementation calls `" ++ v.name ++
      "` with the cached modulus values, then compares the recovered encoding with EMSA-PKCS1-v1_5's \
      encoding of `digest`. It combines the padding result with the public operation's status without \
      branching on that status. It uses 2144 bytes of stack, including the call's return address."])
    code := Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code
    contract := Spec.RsaPkcs1Sig.verifyPrecomputedContract X86_64.abi verStack
    stack := verStack
    verified := PcCT.code_verified v
    spSafe := PcCT.code_spSafe v
    features := v.features },
  { Spec.RsaPkcs1Sig.recoverPrecomputedApi with
    name := Spec.RsaPkcs1Sig.recoverPrecomputedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.RsaPkcs1Sig.recoverPrecomputedApi.doc (notes := ["This implementation calls `" ++ v.name ++
      "` with the cached modulus values into its frame, writes EMSA-PKCS1-v1_5's encoding of the last \
      `out_len` bytes of the result beside it and compares the two, then copies those bytes to `out` and \
      masks them to zeros, and the result to 0, unless the public operation succeeded and the two are \
      equal: nothing after the call branches on its result. It uses 2144 bytes of stack, as \
      `vg_rsa_pkcs1_recover` does."])
    code := Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code
    contract := Spec.RsaPkcs1Sig.recoverPrecomputedContract X86_64.abi verStack
    stack := verStack
    verified := RecPcCT.code_verified v
    spSafe := RecPcCT.code_spSafe v
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.X86_64.RsaPkcs1Sig
