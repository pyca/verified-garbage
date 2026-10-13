module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # PKCS #1 v1.5 encryption over precomputed RSA public variants -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.X86_64.RsaPkcs1Enc

open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.RsaPkcs1Enc.X86_64

def artifacts (v : PublicImpl) : List Artifact := [
  { Spec.RsaPkcs1Enc.encryptPrecomputedApi with
    name := Spec.RsaPkcs1Enc.encryptPrecomputedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.RsaPkcs1Enc.encryptPrecomputedApi.doc (notes := ["This implementation builds \
      `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its frame, finding whether `PS` has a zero byte without a \
      branch, and calls `" ++ v.name ++ "` on it with the cached modulus values. It then sets `out` to \
      zeros and the result to 0 under a mask if `PS` had a zero byte, without branching on the public \
      operation's result, and overwrites the frame's `EM` with zeros either way."])
    code := Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code
    contract := Spec.RsaPkcs1Enc.encryptPrecomputedContract X86_64.abi encStack
    stack := encStack
    verified := PcCT.code_verified v
    spSafe := PcCT.code_spSafe v
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.X86_64.RsaPkcs1Enc
