module

public import VerifiedGarbage.Proof.Sha1.AArch64.Shared
public import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Compress
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-1 (FIPS 180-4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha1.AArch64

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact AArch64.target {
    code := Impl.Sha1.AArch64.Stream.init
    verified := Proof.Sha1.AArch64.Shared.init }]

end VG.Artifacts.Sha1.AArch64
