module

public import VerifiedGarbage.Proof.Sha1.X86_64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-1 (FIPS 180-4) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sha1.X86_64

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact X86_64.target {
    code := Impl.Sha1.X86_64.Stream.init
    verified := Proof.Sha1.X86_64.Shared.init }]

end VG.Artifacts.Sha1.X86_64
