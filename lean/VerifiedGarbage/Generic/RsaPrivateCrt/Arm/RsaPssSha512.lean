module

import VerifiedGarbage.Proof.RsaPss.Arm.VfSat
public meta import VerifiedGarbage.Proof.RsaPss.Arm.VfSat
public import VerifiedGarbage.Proof.RsaPss.Arm.VfVerified
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.RsaPss.Precomputed
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.Arm.SgVerified
public import VerifiedGarbage.Proof.RsaPss.Arm.SgSat

/-!
# RSASSA-PSS signing with SHA-512 on ARMv7, for each implementation of the CRT

A generic file (see `TCB/Emit.lean`): `vg_rsa_pss_sha512_mgf1_sha512_sign`, calling
`vg_rsa_private_checked` over an implementation `v` of `vg_rsa_private_crt`
(`Variants/RsaPrivateCrt/Arm/`), is emitted once for each, named with its
suffix, and needs its CPU features.

It uses 3624 bytes of stack: the push of the registers (56 bytes), its
frame (128 bytes) and the 3440 bytes of the call's.
-/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaPssSha512

open VG.Proof.Rsa.Arm (CrtImpl)

def artifacts (v : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.sha512 Spec.Mgf1.sha512).artifact Arm.target {
    suffix := v.suffix
    code := Proof.RsaPss.Arm.Sg.signCode Proof.RsaPss.Arm.sha512 v
    stack := 3624
    verified := (Proof.RsaPss.Arm.Sg.sign_verified Proof.RsaPss.Arm.sha512 Proof.RsaPss.Arm.Sg.sign_sat_sha512 v)
    features := v.features },
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha512 Spec.Mgf1.sha512).artifact Arm.target {
    suffix := v.suffix
    code := Proof.RsaPss.Arm.Vf.verifyCode Proof.RsaPss.Arm.sha512 (Proof.Rsa.Arm.pdOfCrt v)
    stack := 240
    verified := (Proof.RsaPss.Arm.Vf.verify_verified Proof.RsaPss.Arm.sha512 Proof.RsaPss.Arm.Vf.verify_sat_sha512
      (Proof.Rsa.Arm.pdOfCrt v))
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaPssSha512
