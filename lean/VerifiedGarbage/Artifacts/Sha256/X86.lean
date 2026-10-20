module

public import VerifiedGarbage.Proof.Sha256.X86.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-256 (FIPS 180-4) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sha256.X86

def artifacts : List Artifact := [
  Spec.Sha256.initApi.artifact X86.target {
    code := Impl.Sha256.X86.Stream.init
    verified := Proof.Sha256.X86.Shared.init }]

end VG.Artifacts.Sha256.X86
