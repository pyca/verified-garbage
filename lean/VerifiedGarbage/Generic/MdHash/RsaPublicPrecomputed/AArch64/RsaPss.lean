module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees

/-!
# RSASSA-PSS verification using cached public-key values, on AArch64

Every hash compression variant combines with every precomputed RSA public
operation variant. The digest, signature and recovered encoding stay secret.

Its stack is its frame and `vg_rsa_pss_<H>_mgf1_<H>_check_encoding`'s 352
bytes, more than the public operation's.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPublicPrecomputed.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPss.AArch64 (chkOf)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.PublicImpl) : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("rsa", c.suffix)]
    notes := ["This implementation calls `" ++ c.name ++ "` with the cached public-key values, \
        then `" ++ (chkOf v).name ++ "` on the last `emLen` bytes of its output, and checks \
        that the bytes before them are zero."]
    code := Impl.RsaPss.AArch64.verifyC (chkOf v).name (chkOf v).code (pdOf c).name (pdOf c).code
    stack := stk 352
    verified := Proof.RsaPss.AArch64.verify_verified v c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPublicPrecomputed.AArch64.RsaPss
