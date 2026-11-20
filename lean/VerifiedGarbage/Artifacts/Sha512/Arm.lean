module

public import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sha512.Arm

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.init384
    verified := .scrubbed Proof.Sha512.Arm.Fn.init384 },
  Spec.Sha512.init512Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.init512
    verified := .scrubbed Proof.Sha512.Arm.Fn.init512 },
  Spec.Sha512.init512_224Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.init512_224
    verified := .scrubbed Proof.Sha512.Arm.Fn.init512_224 },
  Spec.Sha512.init512_256Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.init512_256
    verified := .scrubbed Proof.Sha512.Arm.Fn.init512_256 },
  Spec.Sha512.updateApi.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.update
    verified := .scrubbed Proof.Sha512.Arm.Fn.update },
  Spec.Sha512.finalizeApi.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.finalize
    verified := .scrubbed Proof.Sha512.Arm.Fn.finalize },
  Spec.Sha512.finalize384Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.finalize384
    verified := .scrubbed Proof.Sha512.Arm.Fn.finalize384 },
  Spec.Sha512.finalize512_256Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.finalize512_256
    verified := .scrubbed Proof.Sha512.Arm.Fn.finalize512_256 },
  Spec.Sha512.finalize512_224Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.finalize512_224
    verified := .scrubbed Proof.Sha512.Arm.Fn.finalize512_224 },
  Spec.Sha512.digest384Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.digest384
    verified := .scrubbed Proof.Sha512.Arm.Fn.digest384 },
  Spec.Sha512.digest512Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.digest512
    verified := .scrubbed Proof.Sha512.Arm.Fn.digest512 },
  Spec.Sha512.digest512_224Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.digest512_224
    verified := .scrubbed Proof.Sha512.Arm.Fn.digest512_224 },
  Spec.Sha512.digest512_256Api.artifact Arm.target {
    code := Impl.Sha512.Arm.Fn.digest512_256
    verified := .scrubbed Proof.Sha512.Arm.Fn.digest512_256 }]

end VG.Artifacts.Sha512.Arm
