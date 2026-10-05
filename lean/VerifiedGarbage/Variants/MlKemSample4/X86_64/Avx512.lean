import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl

/-! ML-KEM four-way sampling with AVX-512VL quadword rotates. -/

namespace VG.Variants.MlKemSample4.X86_64.Avx512

def variant : Proof.MlKem.X86_64.Sample4Impl := .avx512

end VG.Variants.MlKemSample4.X86_64.Avx512
