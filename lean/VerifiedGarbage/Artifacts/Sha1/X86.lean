module

public import VerifiedGarbage.Proof.Sha1.X86.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-1 (FIPS 180-4) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sha1.X86

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact X86.target {
    code := Impl.Sha1.X86.Stream.init
    verified := Proof.Sha1.X86.Shared.init }]

end VG.Artifacts.Sha1.X86
