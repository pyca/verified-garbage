module
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit

public import VerifiedGarbage.Proof.Sha3.X86_64.Instances
public import VerifiedGarbage.Proof.Sha3.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # SHA-3 and SHAKE (FIPS 202) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sha3.X86_64

def artifacts : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.updateSha3_224Reg,
  Spec.Sha3.finalizeSha3_224Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
    stack := 680
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_224 },
  Spec.Sha3.updateSha3_256Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.updateSha3_256Reg,
  Spec.Sha3.finalizeSha3_256Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
    stack := 680
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_256 },
  Spec.Sha3.updateSha3_384Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.updateSha3_384Reg,
  Spec.Sha3.finalizeSha3_384Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
    stack := 680
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_384 },
  Spec.Sha3.updateSha3_512Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.updateSha3_512Reg,
  Spec.Sha3.finalizeSha3_512Api.artifact X86_64.target {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
    stack := 680
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_512 },
  Spec.Sha3.updateShake128Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.updateShake128Reg,
  Spec.Sha3.finalizeShake128Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.finalizeShake128Reg,
  Spec.Sha3.squeezeShake128Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.squeezeShake128Reg,
  Spec.Sha3.finalizeShake256Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.finalizeShake256Reg,
  Spec.Sha3.squeezeShake256Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.squeezeShake256Reg]

end VG.Artifacts.Sha3.X86_64
