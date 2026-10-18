module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignPcCT
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PKCS1-v1_5 signing on x86-64

A generic file (see `TCB/Emit.lean`): `vg_rsa_pkcs1_sign_precomputed`,
calling `vg_rsa_private_checked_precomputed` for an implementation `v` of
`vg_rsa_private_crt_precomputed`, is emitted once for each implementation
(`Variants/RsaPrivateCrt/X86_64/`), named with its suffix (e.g.
`vg_rsa_pkcs1_sign_precomputed_adx`), and needs its CPU features. The Rust
code signs with it on x86-64, so `vg_rsa_pkcs1_sign` is not emitted here.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.X86_64.RsaPkcs1Sig

open VG.Proof.Rsa.X86_64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.X86_64

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.signPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation writes EMSA-PKCS1-v1_5's \
      encoding of `digest` into its frame, signs it with `" ++ SgnPc.privName v ++ "`, which checks the \
      signature against `e`, and then overwrites the encoding with zeros. Only the lengths, `hash`, the \
      public key and the values of `n` in `pre` decide a branch or an address. It uses 2424 bytes of stack: \
      a frame of 1208 bytes, which holds the encoding and the stack arguments of the call, the call's return \
      address, and the 1208 bytes its callee uses."]
    code := Impl.RsaPkcs1Sig.X86_64.SignPc.code (SgnPc.privName v) (SgnPc.privCode v)
    stack := sigPcStack
    verified := SgnPc.code_verified v
    spSafe := SgnPc.code_spSafe v
    features := v.features }]

end VG.Generic.RsaPrivateCrt.X86_64.RsaPkcs1Sig
