import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.PrecomputedCT

/-! # PKCS #1 v1.5 verification over precomputed RSA public variants -/

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
      branching on that status. It uses 2152 bytes of stack, including the call's return address and that of its \
      calls of Montgomery multiplication."])
    code := Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code
    contract := Spec.RsaPkcs1Sig.verifyPrecomputedContract X86_64.abi verStack
    stack := verStack
    verified := PcCT.code_verified v
    spSafe := PcCT.code_spSafe v
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.X86_64.RsaPkcs1Sig
