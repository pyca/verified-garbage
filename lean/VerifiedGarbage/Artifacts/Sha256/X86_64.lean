module

public import VerifiedGarbage.Proof.Sha256.X86_64.Shared
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Sha256.X86_64.Lit

/-! # SHA-256 (FIPS 180-4) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sha256.X86_64

def artifacts : List Artifact := [
  Spec.Sha256.compressApi.artifact X86_64.target {
    code := Impl.Sha256.X86_64.compress
    verified := Proof.Sha256.X86_64.Shared.compress },
  Spec.Sha256.initApi.artifact X86_64.target {
    code := Impl.Sha256.X86_64.Stream.init
    verified := Proof.Sha256.X86_64.Shared.init },
  Spec.Sha256.compressApi.artifact X86_64.target {
    suffix := "_shani"
    code := Impl.Sha256.X86_64.ShaNi.compress
    verified := Proof.Sha256.X86_64.Shared.compress_shani
    features := ["sha", "ssse3"] },
  Spec.Sha256.compressApi.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.Sha256.X86_64.Avx2.compress
    verified := Proof.Sha256.X86_64.Shared.compress_avx2
    features := ["avx", "avx2", "bmi1", "bmi2"] }]

end VG.Artifacts.Sha256.X86_64
