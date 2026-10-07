import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.RsaPss.AArch64.SignVerified
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees

/-!
# RSASSA-PSS signing on AArch64

Generic over two interfaces: the hash function of an `MdHash` variant `v`
(with MGF1 over the same hash function) and an implementation `c` of
`vg_rsa_private_crt`. Its stack is its frame and `vg_rsa_private_checked`'s
3248 bytes.
-/

namespace VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (privOf)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact := [
  { Spec.RsaPss.signApi v.mgf.G v.mgf.G with
    name := Emit.qualifiedName (Spec.RsaPss.signApi v.mgf.G v.mgf.G).name
      [(v.mgf.G.rust, v.suffix), ("crt", c.suffix)]
    target := AArch64.target
    doc := (Spec.RsaPss.signApi v.mgf.G v.mgf.G).doc (notes := ["This implementation builds EMSA-PSS's \
      encoding in its working space: `M'` is hashed over the blocks its length needs, `DB` is \
      masked with MGF1, and the encoding is signed with `" ++ (privOf c).name ++ "`, which checks \
      the signature against `e`. Only the lengths, `salt_len` and the public key decide a branch \
      or an address."])
    code := Impl.RsaPss.AArch64.sign v.H (privOf c).name (privOf c).code
    contract := Spec.RsaPss.signContract v.mgf.G v.mgf.G AArch64.abi (stk (privOf c).stack)
    stack := stk (privOf c).stack
    verified := Proof.RsaPss.AArch64.Sgn.code_verified v.ok v.mgf.hash v.mgf.len
      (Proof.RsaPss.AArch64.Vfy.mgf_valid v.mgf) v.pss (privOf c) (show 16 ≤ Proof.Rsa.AArch64.stackBytes by decide)
      (Proof.RsaPss.AArch64.Sgn.sign_sat v.mgf.mem)
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPss
