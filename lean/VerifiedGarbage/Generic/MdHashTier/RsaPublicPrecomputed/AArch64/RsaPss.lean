module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Tier
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS verification using cached public-key values, on AArch64

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_pss_verify_precomputed` calls the hash functions `hash` and
`mgf1_hash` name, of the tier `t` (`Variants/MdHashTier/AArch64/`), through
a dispatch on each number, and an implementation `c` of the precomputed RSA
public operation. It is emitted for each pair, named by
`Emit.qualifiedName` (`hash` for the tier, then `rsa`), and needs both's CPU
features. The digest, signature and recovered encoding stay secret.

Its stack is its frame and 16 bytes below it, for the calls of the hash
functions' and the public operation's functions (which have no frames).
-/

@[expose] public section

namespace VG.Generic.MdHashTier.RsaPublicPrecomputed.AArch64.RsaPss

open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPss.AArch64 (tierHs verify_verified)
open VG.Proof.RsaPss.AArch64.Inst (features)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

def artifacts (t : Proof.Pbkdf2.Md.AArch64.Tier) (c : Proof.Rsa.AArch64.PublicImpl) : List Artifact := [
  Spec.RsaPss.verifyAnyApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix), ("rsa", c.suffix)]
    notes := ["This implementation calls `" ++ c.name ++ "` with the cached public-key values, \
        then checks EMSA-PSS in its working space without branching on the encoding: `maskedDB` \
        is unmasked with MGF1 and its delimiter and salt length checked. A specified salt length \
        copies that many trailing bytes into `M'` and hashes only the blocks needed; an unknown \
        salt length retains the oblivious shift and maximum block count. The hash functions \
        `hash` and `mgf1_hash` name are called through a dispatch on each number. Only public \
        lengths, salt-length mode, the hash functions and key data decide a branch or an address."]
    code := Impl.RsaPss.AArch64.verifyPrecomputed (tierHs t) (pdOf c).name (pdOf c).code
    stack := stk 16
    verified := verify_verified t c
    features := features t c.features }]

end VG.Generic.MdHashTier.RsaPublicPrecomputed.AArch64.RsaPss
