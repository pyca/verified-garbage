module

public import VerifiedGarbage.Proof.Sha256.AArch64.Shared
public import VerifiedGarbage.Proof.Sha256.AArch64.Sha2.Compress
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-256 (FIPS 180-4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha256.AArch64

def artifacts : List Artifact := [
  Spec.Sha256.initApi.artifact AArch64.target {
    code := Impl.Sha256.AArch64.Stream.init
    verified := Proof.Sha256.AArch64.Shared.init }]

end VG.Artifacts.Sha256.AArch64
