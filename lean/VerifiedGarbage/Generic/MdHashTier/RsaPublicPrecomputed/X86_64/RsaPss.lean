module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Tier
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS verification on x86-64 using cached public-key values, with the hash functions as arguments

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_pss_verify_precomputed`, for the hash functions of a tier `t`
(`Variants/MdHashTier/X86_64/`), the digest's and MGF1's chosen by `hash`
and `mgf1_hash`, calling an implementation `c` of the precomputed public
operation (`Variants/RsaPublicPrecomputed/X86_64/`). It is emitted once for
each pair, named by `Emit.qualifiedName` with `hash` and `rsa` as tags
(e.g. `vg_rsa_pss_verify_precomputed_hash_shani_rsa_adx`), and needs
both's CPU features. The digest, signature and recovered encoding stay
secret.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.RsaPublicPrecomputed.X86_64.RsaPss

open VG.Proof.RsaPss.X86_64 (verifyStack)
open VG.Proof.RsaPss.X86_64.Any (tierHashes verifyAny_verified verifyAny_spAll)

def artifacts (t : Proof.Pbkdf2.Md.X86_64.Tier) (c : Proof.Rsa.X86_64.PublicImpl) : List Artifact := [
  Spec.RsaPss.verifyAnyApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix), ("rsa", c.suffix)]
    notes := ["This implementation calls `" ++ c.name ++ "` with the cached public-key values, \
        then checks EMSA-PSS's encoding in its working space. The hash functions are chosen by \
        comparing `hash` and `mgf1_hash` with each number in turn."]
    code := Impl.RsaPss.X86_64.AnyHash.verify (tierHashes t) c.name c.code
    stack := verifyStack
    verified := verifyAny_verified t c
    spSafe := verifyAny_spAll t c
    features := t.features ++ c.features.filter (!t.features.contains ·) }]

end VG.Generic.MdHashTier.RsaPublicPrecomputed.X86_64.RsaPss
