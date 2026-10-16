module

public import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.ApplyCT
public import VerifiedGarbage.Proof.ChaCha20.Arm.Stream.Init
public import VerifiedGarbage.Proof.Framework.Registration

/-! # The ChaCha20 block function (RFC 8439) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.Arm

def artifacts : List Artifact := [
  Spec.ChaCha20.blockApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.block
    verified := Proof.ChaCha20.Arm.block_verified },
  Spec.ChaCha20.xorApi.artifact Arm.target {
    notes := ["Calls `vg_chacha20_block` for each 64 bytes."]
    code := Impl.ChaCha20.Arm.Xor.xor
    verified := Proof.ChaCha20.Arm.Xor.xor_verified },
  Spec.ChaCha20.initApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Stream.init
    verified := Proof.ChaCha20.Arm.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Stream.setNonce
    verified := Proof.ChaCha20.Arm.Stream.setNonce_verified },
  Spec.ChaCha20.applyApi.artifact Arm.target {
    code := Impl.ChaCha20.Arm.Stream.apply
    verified := Proof.ChaCha20.Arm.Stream.apply_verified }]

end VG.Artifacts.ChaCha20.Arm
