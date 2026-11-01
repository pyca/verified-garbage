module

public import VerifiedGarbage.Proof.Blake2.Arm.Blake2s
public import VerifiedGarbage.Proof.Blake2.Arm.CompressS.Compress
public import VerifiedGarbage.Proof.Framework.Registration

/-! # BLAKE2s (RFC 7693) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Blake2s.Arm

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Stream.init Spec.Blake2.s
    verified := Proof.Blake2.Arm.Blake2s.initS_verified },
  Spec.Blake2.updateSApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 592 2 (Impl.Blake2.Arm.Stream.update (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)
    stack := 16 + 592
    verified := Proof.Blake2.Arm.Blake2s.updateS_framed },
  Spec.Blake2.finalizeSApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 592 1 (Impl.Blake2.Arm.Stream.finalize (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)
    stack := 16 + 592
    verified := Proof.Blake2.Arm.Blake2s.finalizeS_framed }]

end VG.Artifacts.Blake2s.Arm
