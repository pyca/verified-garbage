module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb8
import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB8 on ARMv7 -/

namespace VG.Artifacts.TripleDesCfb8.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.TripleDes.cfb8EncryptApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cfb8Encrypt
    verified := Proof.TripleDes.Arm.Fn.cfb8Encrypt },
  Spec.TripleDes.cfb8DecryptApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cfb8Decrypt
    verified := Proof.TripleDes.Arm.Fn.cfb8Decrypt }]

spec_apis artifacts

end VG.Artifacts.TripleDesCfb8.Arm
