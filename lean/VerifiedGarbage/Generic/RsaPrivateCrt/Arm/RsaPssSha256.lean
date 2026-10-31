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

/-! # RSASSA-PSS signing with SHA-256 on ARMv7, for each implementation of the CRT -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaPssSha256

open VG.Proof.Rsa.Arm (CrtImpl)

def artifacts (v : CrtImpl) : List Artifact := [
  (Spec.RsaPss.signApi Spec.Mgf1.sha256 Spec.Mgf1.sha256).artifact Arm.target {
    suffix := v.suffix
    code := Proof.RsaPss.Arm.Sg.signCode Proof.RsaPss.Arm.sha256 v
    stack := 3624
    verified := (Proof.RsaPss.Arm.Sg.sign_verified Proof.RsaPss.Arm.sha256 Proof.RsaPss.Arm.Sg.sign_sat_sha256 v)
    features := v.features },
  (Spec.RsaPss.verifyPrecomputedApi Spec.Mgf1.sha256 Spec.Mgf1.sha256).artifact Arm.target {
    suffix := v.suffix
    code := Proof.RsaPss.Arm.Vf.verifyCode Proof.RsaPss.Arm.sha256 (Proof.Rsa.Arm.pdOfCrt v)
    stack := 240
    verified := (Proof.RsaPss.Arm.Vf.verify_verified Proof.RsaPss.Arm.sha256 Proof.RsaPss.Arm.Vf.verify_sat_sha256
      (Proof.Rsa.Arm.pdOfCrt v))
    features := v.features }]

end VG.Generic.RsaPrivateCrt.Arm.RsaPssSha256
