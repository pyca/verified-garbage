module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgVerified
public import VerifiedGarbage.Proof.RsaPss.Arm.SgSat
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512_224
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS signing with SHA-512/224 on ARMv7, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_pss_sha512_224_mgf1_sha512_224_sign`, calling
`vg_rsa_private_checked` over an implementation `v` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/Arm/`), is emitted once for each, named with its
suffix, and needs its CPU features.

It uses 3624 bytes of stack: the push of the registers (56 bytes), its
frame (128 bytes) and the 3440 bytes of the call's.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaPssSha512_224

open VG.Proof.Rsa.Arm (CrtImpl)

def artifacts (v : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.sha512_224 Spec.Mgf1.sha512_224).artifact Arm.target {
    suffix := v.suffix
    notes := ["This implementation builds EMSA-PSS's encoding in its working space: `M'` is hashed \
      over the blocks its length needs, `DB` is masked with MGF1, and the encoding is signed with `" ++
      Proof.Rsa.Arm.privName v ++ "`, which checks the signature against `e`. Only the lengths, \
      `salt_len` and the public key decide a branch or an address."]
    code := Proof.RsaPss.Arm.Sg.signCode Proof.RsaPss.Arm.sha512_224 v
    stack := 3624
    verified := Proof.RsaPss.Arm.Sg.sign_verified Proof.RsaPss.Arm.sha512_224 Proof.RsaPss.Arm.Sg.sign_sat_sha512_224 v
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaPssSha512_224
