module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Sp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCtx
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCT
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-OAEP decryption on x86-64

A generic file of two interfaces (see `TCB/Emit.lean`):
`vg_rsa_oaep_decrypt` calls the streaming functions of the hash functions
its arguments `hash` and `mgf1_hash` name, those of the tier `v`
(`Variants/MdHashTier/X86_64/`), and `vg_rsa_private_checked` calling an
implementation `v2` of `vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86_64/`).
It is named by `Emit.qualifiedName` (`hash`, then `crt`), and needs both's
CPU features.

Its stack is its frame, a return address and `vg_rsa_private_checked`'s
3256 bytes, which are more than the hash functions use.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.RsaPrivateCrt.X86_64.RsaOaep

open VG.Proof.RsaOaep.X86_64 (decStack dec_verified dec_spSafe oaepHs)
open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.Tier) (v2 : Proof.Rsa.X86_64.CrtImpl) : List Artifact := [
  Spec.RsaOaep.decryptAnyApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("hash", v.suffix), ("crt", v2.suffix)]
    notes := ["This implementation calls `" ++ (privOf v2).name ++ "`, and the streaming functions of \
        the hash functions `hash` and `mgf1_hash` name through a comparison of each with each number. \
        The checks of `Y`, `lHash'` and the separator, the scan for it and the shift of the message to \
        the start of `out` are masks computed without branches, reading every byte of `EM` whatever the \
        outcome."]
    code := Impl.RsaOaep.X86_64.decrypt (oaepHs v) (privOf v2).name (privOf v2).code
    stack := decStack
    verified := dec_verified v (privOf v2)
    spSafe := dec_spSafe v (privOf v2)
    features := v.features ++ v2.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHashTier.RsaPrivateCrt.X86_64.RsaOaep
