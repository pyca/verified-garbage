module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees

/-!
# RSASSA-PSS signing on AArch64

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_pss_<H>_mgf1_<H>_sign`, for the hash function of an `MdHash` variant
`v` with MGF1 over the same hash function, calling `v`'s
`vg_rsa_pss_<H>_mgf1_<H>_encode` (`Generic/MdHash/AArch64/RsaPss.lean`), and
`vg_rsa_private_checked` calling an implementation `c` of
`vg_rsa_private_crt`. It is emitted once for each pair, named by
`Emit.qualifiedName` with the hash function's name and `crt` as tags, and
needs both's CPU features.

Its stack is its frame and `vg_rsa_private_checked`'s 3248 bytes, more than
`encode`'s.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (privOf)
open VG.Proof.RsaPss.AArch64 (encOf)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("crt", c.suffix)]
    notes := ["This implementation calls `" ++ (encOf v).name ++ "` for EMSA-PSS's encoding, \
      after a zero byte if the modulus' first byte is 1, and signs it with `" ++ (privOf c).name ++
      "`, which checks the signature against `e`. Only the lengths, `salt_len` and the public key \
      decide a branch or an address."]
    code := Impl.RsaPss.AArch64.signC (encOf v).name (encOf v).code (privOf c).name (privOf c).code
    stack := stk (privOf c).stack
    verified := Proof.RsaPss.AArch64.sign_verified v c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPrivateCrt.AArch64.RsaPss
