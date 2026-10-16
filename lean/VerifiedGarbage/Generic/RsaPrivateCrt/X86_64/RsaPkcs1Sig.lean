module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCT
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PKCS1-v1_5 signing on x86-64

A generic file (see `TCB/Emit.lean`): `vg_rsa_pkcs1_sign`, calling
`vg_rsa_private_checked` for an implementation `v` of `vg_rsa_private_crt`,
is emitted once for each implementation (`Variants/RsaPrivateCrt/X86_64/`),
named with its suffix (e.g. `vg_rsa_pkcs1_sign_adx`), and needs its CPU
features.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.X86_64.RsaPkcs1Sig

open VG.Proof.Rsa.X86_64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.X86_64

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.signApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation writes EMSA-PKCS1-v1_5's \
      encoding of `digest` into its frame, signs it with `" ++ Sgn.privName v ++ "`, which checks the \
      signature against `e`, and then overwrites the encoding with zeros. Only the lengths, `hash` and \
      the public key decide a branch or an address. It uses 4456 bytes of stack: a frame of 1192 bytes, \
      which holds the encoding and the stack arguments of the call, the call's return address, and the \
      3256 bytes its callee uses."]
    code := Impl.RsaPkcs1Sig.X86_64.Sign.code (Sgn.privName v) (Sgn.privCode v)
    stack := sigStack
    verified := Sgn.code_verified v
    spSafe := Sgn.code_spSafe v
    features := v.features }]

end VG.Generic.RsaPrivateCrt.X86_64.RsaPkcs1Sig
