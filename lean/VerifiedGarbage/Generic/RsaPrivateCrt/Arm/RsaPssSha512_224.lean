module

import VerifiedGarbage.Proof.RsaPss.Arm.VfSat
public meta import VerifiedGarbage.Proof.RsaPss.Arm.VfSat
public import VerifiedGarbage.Proof.RsaPss.Arm.VfVerified
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.RsaPss.Precomputed
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Proof.RsaPss.Arm.Hashes.Sha512_224
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.Arm.SgVerified
public import VerifiedGarbage.Proof.RsaPss.Arm.SgSat

/-! # RSASSA-PSS signing with SHA-512/224 on ARMv7, for each implementation of the CRT -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaPssSha512_224

open VG.Proof.Rsa.Arm (CrtImpl)

def artifacts (v : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.sha512_224 Spec.Mgf1.sha512_224).artifact Arm.target {
    suffix := v.suffix
    code := Proof.RsaPss.Arm.Sg.signCode Proof.RsaPss.Arm.sha512_224 v
    stack := 3624
    verified := (Proof.RsaPss.Arm.Sg.sign_verified Proof.RsaPss.Arm.sha512_224 Proof.RsaPss.Arm.Sg.sign_sat_sha512_224 v)
    features := v.features },
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha512_224 Spec.Mgf1.sha512_224).artifact Arm.target {
    suffix := v.suffix
    code := Proof.RsaPss.Arm.Vf.verifyCode Proof.RsaPss.Arm.sha512_224 (Proof.Rsa.Arm.pdOfCrt v)
    stack := 240
    verified := (Proof.RsaPss.Arm.Vf.verify_verified Proof.RsaPss.Arm.sha512_224 Proof.RsaPss.Arm.Vf.verify_sat_sha512_224
      (Proof.Rsa.Arm.pdOfCrt v))
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaPssSha512_224
