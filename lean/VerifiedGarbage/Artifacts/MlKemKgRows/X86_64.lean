module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

public import VerifiedGarbage.Proof.MlKem.X86_64.KgNttV
public import VerifiedGarbage.Proof.MlKem.X86_64.KgRowV
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlKem.X86_64.Lit

/-! # ML-KEM-768 (FIPS 203) on x86-64: K-PKE key generation a row at a time -/

@[expose] public section

namespace VG.Artifacts.MlKemKgRows.X86_64

def artifacts : List Artifact := [
  Spec.MlKem.kpkeKeyGenNttApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.KpkeKgRows.kgNtt Impl.MlKem.X86_64.kem768 .avx2
    verified := Proof.MlKem.X86_64.kgNtt768_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.kpkeKeyGenRowApi.artifact X86_64.target {
    code := Impl.MlKem.X86_64.KpkeKgRows.kgRow Impl.MlKem.X86_64.kem768 .avx2
    verified := Proof.MlKem.X86_64.kgRow768_verified
    features := ["avx", "avx2"] }]

end VG.Artifacts.MlKemKgRows.X86_64
