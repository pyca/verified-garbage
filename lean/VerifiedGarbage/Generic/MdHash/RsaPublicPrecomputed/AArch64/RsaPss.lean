module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS verification using cached public-key values, on AArch64

Every hash compression variant combines with every precomputed RSA public
operation variant. The digest, signature and recovered encoding stay secret.

Its stack is its frame and 16 bytes below it, for the calls of the hash
function's and the public operation's functions (which have no frames).
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPublicPrecomputed.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.PublicImpl) : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi v.mgf.G v.mgf.G).artifact AArch64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("rsa", c.suffix)]
    notes := ["This implementation calls `" ++ c.name ++ "` with the cached public-key values, \
        then checks EMSA-PSS in its working space without branching on the encoding: `maskedDB` \
        is unmasked with MGF1 and its delimiter and salt length checked. A specified salt length \
        copies that many trailing bytes into `M'` and hashes only the blocks needed; an unknown \
        salt length retains the oblivious shift and maximum block count. Only public lengths, \
        salt-length mode and key data decide a branch or an address."]
    code := Impl.RsaPss.AArch64.verifyPrecomputed v.H (pdOf c).name (pdOf c).code
    stack := stk 16
    verified := Proof.RsaPss.AArch64.verify_verified v c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPublicPrecomputed.AArch64.RsaPss
