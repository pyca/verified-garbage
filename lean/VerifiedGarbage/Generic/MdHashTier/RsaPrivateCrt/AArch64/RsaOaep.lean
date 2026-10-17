module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Inst
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSAES-OAEP decryption on AArch64

A generic file of two interfaces (see `TCB/Emit.lean`): `vg_rsa_oaep_decrypt`
calls the streaming functions of the hash functions `hash` and `mgf1_hash`
name, of the tier `t` (`Variants/MdHashTier/AArch64/`), through a dispatch on
each number, and `vg_rsa_private_checked` calling an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/AArch64/`). It is emitted for
each pair, named by `Emit.qualifiedName` (`hash` for the tier, then `crt`),
and needs both's CPU features.

Its stack is its frames, 288 bytes, and `vg_rsa_private_checked`'s 3248
bytes, which are more than the hash functions use.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.RsaPrivateCrt.AArch64.RsaOaep

open VG.Proof.RsaOaep.AArch64 (dec_sat tierHs)
open VG.Proof.RsaOaep.AArch64.Inst (features)
open VG.Proof.RsaOaep.AArch64.Dec (decStack dec_verified)
open VG.Proof.RsaPkcs1Enc.AArch64 (privOf)

def artifacts (t : Proof.Pbkdf2.Md.AArch64.Tier) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact := [
  Spec.RsaOaep.decryptAnyApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" [("hash", t.suffix), ("crt", c.suffix)]
    notes := ["This implementation calls `" ++ (privOf c).name ++ "`, and the streaming functions of the hash \
        functions `hash` and `mgf1_hash` name through a dispatch on each number, which is public. The checks \
        of `Y`, `lHash'` and the separator, the scan for it and the shift of the message to the start of \
        `out` are masks computed without branches, reading every byte of `EM` whatever the outcome."]
    code := Impl.RsaOaep.AArch64.decrypt (tierHs t) (privOf c).name (privOf c).code
    stack := decStack (privOf c)
    verified := dec_verified t (privOf c) (dec_sat c)
    features := features t c.features }]

end VG.Generic.MdHashTier.RsaPrivateCrt.AArch64.RsaOaep
