module
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit

public import VerifiedGarbage.Proof.Sha3.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # SHA-3 and SHAKE (FIPS 202) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sha3.X86_64

def artifacts : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_224.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_224 },
  Spec.Sha3.finalizeSha3_224Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
    stack := 680
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_224 },
  Spec.Sha3.updateSha3_256Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_256.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_256 },
  Spec.Sha3.finalizeSha3_256Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
    stack := 680
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_256 },
  Spec.Sha3.updateSha3_384Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_384.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_384 },
  Spec.Sha3.finalizeSha3_384Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
    stack := 680
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_384 },
  Spec.Sha3.updateSha3_512Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_512.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_512 },
  Spec.Sha3.finalizeSha3_512Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
    stack := 680
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_512 },
  Spec.Sha3.updateShake128Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.xofShake128.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_shake128 },
  Spec.Sha3.finalizeShake128Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake128.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.finalize_shake128 },
  Spec.Sha3.squeezeShake128Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.squeeze_shake128 },
  Spec.Sha3.finalizeShake256Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake256.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.finalize_shake256 },
  Spec.Sha3.squeezeShake256Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.squeeze_shake256 }]

end VG.Artifacts.Sha3.X86_64
