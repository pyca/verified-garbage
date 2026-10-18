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

A generic file (see `TCB/Emit.lean`): `vg_rsa_oaep_decrypt`, calling
`vg_rsa_private_checked` for an implementation `v` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/X86_64/`), is emitted once for each implementation,
named with its suffix, and needs its CPU features. It calls the streaming
functions of the hash functions `hash` and `mgf1_hash` name through the
tables `hash_fns` and `mgf1_fns`, which the caller chooses.

Its stack is its frame, a return address and `vg_rsa_private_checked`'s
3256 bytes, which are more than the hash functions' calls use.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.X86_64.RsaOaep

open VG.Proof.RsaOaep.X86_64 (decStack dec_verified dec_spSafe)
open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)

def artifacts (v : Proof.Rsa.X86_64.CrtImpl) : List Artifact := [
  Spec.RsaOaep.decryptAnyApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation calls `" ++ (privOf v).name ++ "`, and the streaming functions \
        of the tables `hash_fns` and `mgf1_fns` through `r11`, choosing each table's digest length by \
        comparing its number with each one. The checks of `Y`, `lHash'` and the separator, the scan \
        for it and the shift of the message to the start of `out` are masks computed without \
        branches, reading every byte of `EM` whatever the outcome."]
    code := Impl.RsaOaep.X86_64.decrypt (privOf v).name (privOf v).code
    stack := decStack
    verified := dec_verified (privOf v)
    spSafe := dec_spSafe (privOf v)
    features := v.features }]

end VG.Generic.RsaPrivateCrt.X86_64.RsaOaep
