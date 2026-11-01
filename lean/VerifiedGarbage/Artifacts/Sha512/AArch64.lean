module

public import VerifiedGarbage.Proof.Sha512.AArch64.Shared
public import VerifiedGarbage.Proof.Sha512.AArch64.Sha3.Compress
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha512.AArch64

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact AArch64.target {
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_384
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_384 },
  Spec.Sha512.init512Api.artifact AArch64.target {
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512 },
  Spec.Sha512.init512_224Api.artifact AArch64.target {
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_224
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512_224 },
  Spec.Sha512.init512_256Api.artifact AArch64.target {
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_256
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512_256 }]

end VG.Artifacts.Sha512.AArch64
