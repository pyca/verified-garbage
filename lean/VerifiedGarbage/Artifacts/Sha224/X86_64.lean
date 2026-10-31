module

public import VerifiedGarbage.Proof.Sha256.X86_64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-224 (FIPS 180-4) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sha224.X86_64

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact X86_64.target {
    code := Impl.Sha256.X86_64.Stream.init224
    verified := Proof.Sha256.X86_64.Shared.init224 }]

end VG.Artifacts.Sha224.X86_64
