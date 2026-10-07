import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees

/-! # PKCS #1 v1.5 verification over precomputed RSA public variants on AArch64 -/

namespace VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Sig

open VG.Proof.Rsa.AArch64 (PublicImpl)
open VG.Proof.RsaPkcs1Sig.AArch64

def artifacts (v : PublicImpl) : List Artifact := [
  { Spec.RsaPkcs1Sig.verifyPrecomputedApi with
    name := Spec.RsaPkcs1Sig.verifyPrecomputedApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.RsaPkcs1Sig.verifyPrecomputedApi.doc (notes := ["This implementation calls `" ++ v.name ++
      "` with the cached modulus values, then compares the recovered encoding with EMSA-PKCS1-v1_5's \
      encoding of `digest`. It combines the padding result with the public operation's status without \
      branching on that status. It uses 2144 bytes of stack: its frame and 16 bytes below it for the \
      call."])
    code := Impl.RsaPkcs1Sig.AArch64.Precomputed.code (pdOf v).name (pdOf v).code
    contract := Spec.RsaPkcs1Sig.verifyPrecomputedContract AArch64.abi (Ver.stk (pdOf v).stack)
    stack := Ver.stk (pdOf v).stack
    verified := Pc.code_verified (pdOf v)
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Sig
