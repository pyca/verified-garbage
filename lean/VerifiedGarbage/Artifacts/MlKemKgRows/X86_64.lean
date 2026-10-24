module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

public import VerifiedGarbage.Proof.MlKem.X86_64.KgNttV
public import VerifiedGarbage.Proof.MlKem.X86_64.KgRowV
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlKem.X86_64.Lit

/-! # ML-KEM-768 (FIPS 203) on x86-64: K-PKE key generation a row at a time -/

@[expose] public section

namespace VG.Artifacts.MlKemKgRows.X86_64

/-- What a half of K-PKE key generation computing with `fns` does. -/
def notes (fns : String) : List String :=
  [s!"The function computes with the code of {fns} and its encoding inlined, on AVX2 registers, \
    with 16-bit polynomials, and calls nothing. It sets MXCSR to `0x1FBF` once around all its \
    multiplications (Intel's mitigation of MXCSR-configuration-dependent timing) and loads the \
    caller's MXCSR back before returning."]

def artifacts : List Artifact := [
  Spec.MlKem.kpkeKeyGenNttApi.artifact X86_64.target {
    notes := notes "`vg_mlkem_ntt_avx2`"
    code := Impl.MlKem.X86_64.KpkeKgRows.kgNtt Impl.MlKem.X86_64.kem768 .avx2
    verified := Proof.MlKem.X86_64.kgNtt768_verified
    features := ["avx", "avx2"] },
  Spec.MlKem.kpkeKeyGenRowApi.artifact X86_64.target {
    notes := notes "`vg_mlkem_multiply_ntts_avx2`"
    code := Impl.MlKem.X86_64.KpkeKgRows.kgRow Impl.MlKem.X86_64.kem768 .avx2
    verified := Proof.MlKem.X86_64.kgRow768_verified
    features := ["avx", "avx2"] }]

end VG.Artifacts.MlKemKgRows.X86_64
