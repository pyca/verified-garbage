module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.X86_64.SSp
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS signing on x86-64

A generic file (see `TCB/Emit.lean`): `vg_rsa_pss_sign`, calling
`vg_rsa_private_checked` for an implementation `v` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/X86_64/`), is emitted once for each implementation,
named with its suffix, and needs its CPU features. It calls the streaming
functions of the hash functions `hash` and `mgf1_hash` name through the
tables `hash_fns` and `mgf1_fns`, which the caller chooses.

Its stack is its frame, a return address and `vg_rsa_private_checked`'s
3256 bytes, which are more than the hash functions' calls use.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.X86_64.RsaPss

open VG.Proof.RsaOaep.X86_64 (decStack)
open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)

def artifacts (v : Proof.Rsa.X86_64.CrtImpl) : List Artifact := [
  Spec.RsaPss.signAnyApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation calls the streaming functions of the tables `hash_fns` and \
        `mgf1_fns` through `r11`, choosing each table's digest length by comparing its number with \
        each one, builds EMSA-PSS's encoding in its working space (the salt hashed where it is), and \
        signs it with `" ++ (privOf v).name ++ "`, which checks the signature against `e`. Only the \
        lengths, the selectors and the public key decide a branch or an address."]
    code := Impl.RsaPss.X86_64.sign (privOf v).name (privOf v).code
    stack := decStack
    verified := Proof.RsaPss.X86_64.sign_verified (privOf v)
    spSafe := Proof.RsaPss.X86_64.sign_spSafe (privOf v)
    features := v.features }]

end VG.Generic.RsaPrivateCrt.X86_64.RsaPss
