module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Inst
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-OAEP encryption with a precomputed public key on AArch64

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_oaep_encrypt_precomputed` calls the streaming functions of the hash
functions `hash` and `mgf1_hash` name, of the tier `t`
(`Variants/MdHashTier/AArch64/`), through a dispatch on each number, and an
implementation `c` of `vg_rsa_public_precomputed_checked`
(`Variants/RsaPublicPrecomputed/AArch64/`). It is emitted for each pair,
named by `Emit.qualifiedName` (`hash` for the tier, then `rsa`), and needs
both's CPU features.

Its stack is its frames, 288 bytes, and 16 bytes below them for the calls,
whose callees use no more.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.RsaPublicPrecomputed.AArch64.RsaOaep

open VG.Proof.RsaOaep.AArch64 (enc_sat tierHs)
open VG.Proof.RsaOaep.AArch64.Inst (features)
open VG.Proof.RsaOaep.AArch64.Enc (encStack enc_verified)
open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)

def artifacts (t : Proof.Pbkdf2.Md.AArch64.Tier) (c : Proof.Rsa.AArch64.PublicImpl) : List Artifact := [
  Spec.RsaOaep.encryptAnyApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix), ("rsa", c.suffix)]
    notes := ["This implementation hashes the label and masks `DB` and the seed with MGF1 through the \
        streaming functions of the hash functions `hash` and `mgf1_hash` name, dispatched on each number, \
        which is public, and calls `" ++ c.name ++ "` with the cached modulus values. The message's length \
        is public; its bytes, the label's and the seed's are only copied, hashed and masked."]
    code := Impl.RsaOaep.AArch64.Precomputed.encrypt (tierHs t) (pdOf c).name (pdOf c).code
    stack := encStack (pdOf c)
    verified := enc_verified t (pdOf c) (enc_sat c)
    features := features t c.features }]

end VG.Generic.MdHashTier.RsaPublicPrecomputed.AArch64.RsaOaep
