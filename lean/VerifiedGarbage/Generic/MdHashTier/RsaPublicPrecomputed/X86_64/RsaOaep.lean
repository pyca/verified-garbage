module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcSp
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_oaep_encrypt_precomputed` calls the streaming functions of the hash
functions its arguments `hash` and `mgf1_hash` name, those of the tier `v`
(`Variants/MdHashTier/X86_64/`), and an implementation `v2` of
`vg_rsa_public_precomputed_checked` (`Variants/RsaPublicPrecomputed/X86_64/`).
It is named by `Emit.qualifiedName` (`hash`, then `rsa`), and needs both's
CPU features.

Its stack is its frame, a return address and what the hash functions'
calls use.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.RsaPublicPrecomputed.X86_64.RsaOaep

open VG.Proof.RsaOaep.X86_64 (encStack oaepHs)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.Tier) (v2 : Proof.Rsa.X86_64.PublicImpl) : List Artifact := [
  Spec.RsaOaep.encryptAnyApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("hash", v.suffix), ("rsa", v2.suffix)]
    notes := ["This implementation calls the streaming functions of the hash functions `hash` and \
        `mgf1_hash` name through a comparison of each with each number, and calls `" ++ v2.name ++
        "` with the cached modulus values. The message's length is public; its bytes, the label's \
        and the seed's are only copied, hashed and masked."]
    code := Impl.RsaOaep.X86_64.Precomputed.encrypt (oaepHs v) v2.name v2.code
    stack := encStack
    verified := Proof.RsaOaep.X86_64.Pc.code_verified v v2
    spSafe := Proof.RsaOaep.X86_64.Pc.code_spSafe v v2
    features := v.features ++ v2.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHashTier.RsaPublicPrecomputed.X86_64.RsaOaep
