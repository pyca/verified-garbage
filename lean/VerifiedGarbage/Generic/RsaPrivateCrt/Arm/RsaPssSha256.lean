module

import VerifiedGarbage.Proof.RsaPss.Arm.VfSat
public meta import VerifiedGarbage.Proof.RsaPss.Arm.VfSat
public import VerifiedGarbage.Proof.RsaPss.Arm.VfVerified
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.RsaPss.Precomputed
public import Init.Data.String.Defs
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha256
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.Arm.SgVerified
public import VerifiedGarbage.Proof.RsaPss.Arm.SgSat

/-!
# RSASSA-PSS signing with SHA-256 on ARMv7, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_pss_sha256_mgf1_sha256_sign`, calling
`vg_rsa_private_checked` over an implementation `v` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/Arm/`), is emitted once for each, named with its
suffix, and needs its CPU features.

It uses 3624 bytes of stack: the push of the registers (56 bytes), its
frame (128 bytes) and the 3440 bytes of the call's.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaPssSha256

open VG.Proof.Rsa.Arm (CrtImpl)

def artifacts (v : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.sha256 Spec.Mgf1.sha256).artifact Arm.target {
    suffix := v.suffix
    notes := ["This implementation builds EMSA-PSS's encoding in its working space: `M'` is hashed \
      over the blocks its length needs, `DB` is masked with MGF1, and the encoding is signed with `" ++
      Proof.Rsa.Arm.privName v ++ "`, which checks the signature against `e`. Only the lengths, \
      `salt_len` and the public key decide a branch or an address."]
    code := Proof.RsaPss.Arm.Sg.signCode Proof.RsaPss.Arm.sha256 v
    stack := 3624
    verified := (Proof.RsaPss.Arm.Sg.sign_verified Proof.RsaPss.Arm.sha256 Proof.RsaPss.Arm.Sg.sign_sat_sha256 v)
    features := v.features },
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha256 Spec.Mgf1.sha256).artifact Arm.target {
    suffix := v.suffix
    notes := ["ARMv7 with the selected RSA public implementation. This implementation calls `vg_rsa_public_precomputed_checked` with the \
        cached modulus values, then checks EMSA-PSS in its working space without branching on the \
        encoding: `maskedDB` is unmasked with MGF1, and the end of `DB`'s padding is found by a scan \
        of all its bytes. A specified salt length copies that many trailing bytes of `DB` into `M'` \
        and hashes only the blocks it needs; an unknown salt length shifts `DB` into place in ten \
        masked passes and hashes the blocks of the longest salt. Only the lengths, the salt-length \
        mode and the public key decide a branch or an address."]
    code := Proof.RsaPss.Arm.Vf.verifyCode Proof.RsaPss.Arm.sha256 (Proof.Rsa.Arm.pdOfCrt v)
    stack := 240
    verified := (Proof.RsaPss.Arm.Vf.verify_verified Proof.RsaPss.Arm.sha256 Proof.RsaPss.Arm.Vf.verify_sat_sha256
      (Proof.Rsa.Arm.pdOfCrt v))
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaPssSha256
