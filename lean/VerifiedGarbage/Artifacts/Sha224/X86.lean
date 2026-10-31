module

public import VerifiedGarbage.Proof.Sha256.X86.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-224 (FIPS 180-4) on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Sha224.X86

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact X86.target {
    code := Impl.Sha256.X86.Stream.init224
    verified := Proof.Sha256.X86.Shared.init224 }]

end VG.Artifacts.Sha224.X86
