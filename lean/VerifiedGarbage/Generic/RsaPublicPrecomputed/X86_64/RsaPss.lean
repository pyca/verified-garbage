module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.X86_64.VSp
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS verification with a precomputed public key on x86-64

A generic file (see `TCB/Emit.lean`): `vg_rsa_pss_verify_precomputed`,
calling an implementation `v` of `vg_rsa_public_precomputed_checked`
(`Variants/RsaPublicPrecomputed/X86_64/`), is emitted once for each
implementation, named with its suffix, and needs its CPU features. It calls
the streaming functions of the hash functions `hash` and `mgf1_hash` name
through the tables `hash_fns` and `mgf1_fns`, which the caller chooses.

Its stack is its frame, a return address and what the hash functions'
calls use.
-/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.X86_64.RsaPss

open VG.Proof.RsaOaep.X86_64 (encStack)

def artifacts (v : Proof.Rsa.X86_64.PublicImpl) : List Artifact := [
  Spec.RsaPss.verifyAnyApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation calls the streaming functions of the tables `hash_fns` and \
        `mgf1_fns` through `r11`, choosing each table's digest length by comparing its number with \
        each one, and calls `" ++ v.name ++ "` with the cached modulus values. Its checks are masks \
        computed without branches; with `any_salt_len` set, a copy of the hash's state is finalized \
        for every length the salt found in `DB` could have, and the digest for the one it has is \
        selected by masks."]
    code := Impl.RsaPss.X86_64.verify v.name v.code
    stack := encStack
    verified := Proof.RsaPss.X86_64.ver_verified v
    spSafe := Proof.RsaPss.X86_64.ver_spSafe v
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.X86_64.RsaPss
