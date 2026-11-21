module

public import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Triple DES-CFB8 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cfb8Encrypt
    verified := Proof.TripleDes.Arm.Fn.cfb8Encrypt },
  Spec.TripleDes.cfb8DecryptApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cfb8Decrypt
    verified := Proof.TripleDes.Arm.Fn.cfb8Decrypt }]

end VG.Artifacts.TripleDesCfb8.Arm
