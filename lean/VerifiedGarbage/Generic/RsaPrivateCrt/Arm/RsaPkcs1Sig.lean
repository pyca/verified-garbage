module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.SgVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PKCS1-v1_5 signing on ARMv7, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_pkcs1_sign`, calling
`vg_rsa_private_checked` over an implementation `v` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/Arm/`), is emitted once for each, named with its
suffix, and needs its CPU features.

It uses 4584 bytes of stack: the push of the registers (56 bytes), its
frame (1088 bytes) and the 3440 bytes of the call's.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaPkcs1Sig

open VG.Proof.Rsa.Arm (CrtImpl)

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.signApi.artifact Arm.target {
    suffix := v.suffix
    notes := ["This implementation writes EMSA-PKCS1-v1_5's encoding of `digest` into its frame and signs \
      it with `" ++ Proof.Rsa.Arm.privName v ++ "`, which checks the signature against `e`, then \
      overwrites the frame's encoding with zeros. Only the lengths, the hash function and the public key \
      decide a branch or an address."]
    code := Proof.RsaPkcs1Sig.Arm.Sg.signCode v
    stack := 4584
    verified := Proof.RsaPkcs1Sig.Arm.Sg.code_verified v
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaPkcs1Sig
