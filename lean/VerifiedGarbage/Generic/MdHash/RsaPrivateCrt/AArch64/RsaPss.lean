module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS signing on AArch64

Generic over two interfaces: the hash function of an `MdHash` variant `v`
(with MGF1 over the same hash function) and an implementation `c` of
`vg_rsa_private_crt`. Its stack is its frame and `vg_rsa_private_checked`'s
3248 bytes.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (privOf)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("crt", c.suffix)]
    notes := ["This implementation builds EMSA-PSS's \
      encoding in its working space: `M'` is hashed over the blocks its length needs, `DB` is \
      masked with MGF1, and the encoding is signed with `" ++ (privOf c).name ++ "`, which checks \
      the signature against `e`. Only the lengths, `salt_len` and the public key decide a branch \
      or an address."]
    code := Impl.RsaPss.AArch64.sign v.H (privOf c).name (privOf c).code
    stack := stk (privOf c).stack
    verified := Proof.RsaPss.AArch64.sign_verified v c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPss
