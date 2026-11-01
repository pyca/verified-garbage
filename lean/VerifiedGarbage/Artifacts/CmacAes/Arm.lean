module

public import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Frame
public import VerifiedGarbage.Proof.CmacAes.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CMAC (NIST SP 800-38B) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CmacAes.Arm

open VG.Proof.CmacAes.Arm

def artifacts : List Artifact := [
  Spec.Cmac.aesInitApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratch 2304 .r3 Impl.CmacAes.Stream.Arm.init
    stack := 2312
    verified := Proof.CmacAes.Stream.Arm.init_framed },
  Spec.Cmac.aesAbsorbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2320 2 Impl.CmacAes.Stream.Arm.absorb
    stack := 2336
    verified := Proof.CmacAes.Stream.Arm.absorb_framed },
  Spec.Cmac.aesFinishApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2320 1 Impl.CmacAes.Stream.Arm.finish
    stack := 2336
    verified := Proof.CmacAes.Stream.Arm.finish_framed }]

end VG.Artifacts.CmacAes.Arm
