module

public import VerifiedGarbage.Proof.Sha512.X86_64.Shared
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sha512.X86_64

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact X86_64.target {
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_384 },
  Spec.Sha512.init512Api.artifact X86_64.target {
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512 },
  Spec.Sha512.init512_224Api.artifact X86_64.target {
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512_224 },
  Spec.Sha512.init512_256Api.artifact X86_64.target {
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512_256 }]

end VG.Artifacts.Sha512.X86_64
