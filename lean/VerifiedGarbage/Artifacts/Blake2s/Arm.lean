module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Blake2.Arm.Blake2s
import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.Proof.Framework.Registration

/-! # BLAKE2s (RFC 7693) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Blake2s.Arm

def artifacts : List Artifact := [
  Spec.Blake2.compressSApi.artifact Arm.target {
    code := Impl.Blake2.Arm.S.compress
    verified := Proof.Blake2.ArmS.compress_verified },
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
    verified := Proof.Blake2.Arm.Blake2s.finalizeS_framed },
  Spec.Blake2.updateSScratchApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Stream.update (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress
    stack := 16
    verified := Proof.Blake2.Arm.Blake2s.updateS_verified },
  Spec.Blake2.finalizeSScratchApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Stream.finalize (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress
    stack := 16
    verified := Proof.Blake2.Arm.Blake2s.finalizeS_verified }]

end VG.Artifacts.Blake2s.Arm
