import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees

/-! # RSASSA-PKCS1-v1_5 signing on AArch64, for each implementation of the CRT -/

namespace VG.Generic.RsaPrivateCrt.AArch64.RsaPkcs1Sig

open VG.Proof.Rsa.AArch64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.AArch64

def artifacts (v : CrtImpl) : List Artifact := [
  { Spec.RsaPkcs1Sig.signApi with
    name := Spec.RsaPkcs1Sig.signApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.RsaPkcs1Sig.signApi.doc (notes := ["This implementation writes EMSA-PKCS1-v1_5's \
      encoding of `digest` into its frame and signs it with `" ++ (privOf v).name ++ "`, which checks the \
      signature against `e`. Only the lengths, the hash function and the public key decide a branch or \
      an address."])
    code := Impl.RsaPkcs1Sig.AArch64.Sign.code (privOf v).name (privOf v).code
    contract := Spec.RsaPkcs1Sig.signContract AArch64.abi (Sgn.stk (privOf v).stack)
    stack := Sgn.stk (privOf v).stack
    verified := Sgn.code_verified (privOf v)
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.RsaPrivateCrt.AArch64.RsaPkcs1Sig
