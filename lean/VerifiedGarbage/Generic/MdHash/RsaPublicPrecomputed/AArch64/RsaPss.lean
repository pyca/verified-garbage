import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees

/-!
# RSASSA-PSS verification using cached public-key values, on AArch64

Every hash compression variant combines with every precomputed RSA public
operation variant. The digest, signature and recovered encoding stay secret.

Its stack is its frame and 16 bytes below it, for the calls of the hash
function's and the public operation's functions (which have no frames).
-/

namespace VG.Generic.MdHash.RsaPublicPrecomputed.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.PublicImpl) : List Artifact := [
  { Spec.RsaPss.verifyPrecomputedApi v.mgf.G v.mgf.G with
    name := Emit.qualifiedName (Spec.RsaPss.verifyPrecomputedApi v.mgf.G v.mgf.G).name
      [(v.mgf.G.rust, v.suffix), ("rsa", c.suffix)]
    target := AArch64.target
    doc := (Spec.RsaPss.verifyPrecomputedApi v.mgf.G v.mgf.G).doc
      (notes := ["This implementation calls `" ++ c.name ++ "` with the cached public-key values, \
        then checks EMSA-PSS in its working space without branching on the encoding: `maskedDB` \
        is unmasked with MGF1, the salt is found and shifted into `M'` in constant time, and `M'` \
        is hashed over the blocks its longest length needs. Only the lengths, the expected salt \
        length and the public key decide a branch or an address."])
    code := Impl.RsaPss.AArch64.verifyPrecomputed v.H (pdOf c).name (pdOf c).code
    contract := Spec.RsaPss.verifyPrecomputedContract v.mgf.G v.mgf.G AArch64.abi (stk 16)
    stack := stk 16
    verified := Proof.RsaPss.AArch64.Vfy.code_verified v.ok v.mgf.hash v.mgf.len
      (Proof.RsaPss.AArch64.Vfy.mgf_valid v.mgf) v.pss (pdOf c) (by decide) (Nat.le_refl _)
      (Proof.RsaPss.AArch64.Vfy.verify_sat v.mgf.mem)
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPublicPrecomputed.AArch64.RsaPss
