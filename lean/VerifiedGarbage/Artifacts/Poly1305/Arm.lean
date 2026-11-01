module

public import VerifiedGarbage.Proof.Poly1305.Arm.Init
public import VerifiedGarbage.Proof.Poly1305.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Poly1305 (RFC 8439 §2.5) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.Poly1305.Arm

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact Arm.target {
    code := Impl.Poly1305.Arm.init
    verified := Proof.Poly1305.Arm.init_verified },
  Spec.Poly1305.blocksApi.artifact Arm.target {
    code := Impl.Poly1305.Arm.blocks
    verified := Proof.Poly1305.Arm.blocks_verified },
  Spec.Poly1305.updateApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 144 2 Impl.Poly1305.Arm.update
    stack := 144
    verified := Proof.Poly1305.Arm.update_framed },
  Spec.Poly1305.finalizeApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 144 1 Impl.Poly1305.Arm.finalize
    stack := 144
    verified := Proof.Poly1305.Arm.finalize_framed }]

end VG.Artifacts.Poly1305.Arm
