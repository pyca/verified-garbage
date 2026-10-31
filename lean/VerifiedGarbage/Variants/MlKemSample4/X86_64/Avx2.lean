module

public import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl

/-! # `vg_mlkem_sample_ntt4` on x86-64: with AVX2 -/

@[expose] public section

namespace VG.Variants.MlKemSample4.X86_64.Avx2

def variant : Proof.MlKem.X86_64.Sample4Impl := .avx2

end VG.Variants.MlKemSample4.X86_64.Avx2
