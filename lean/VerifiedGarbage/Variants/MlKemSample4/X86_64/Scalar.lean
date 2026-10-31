module

public import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl

/-! # `vg_mlkem_sample_ntt4` on x86-64: the baseline -/

@[expose] public section

namespace VG.Variants.MlKemSample4.X86_64.Scalar

def variant : Proof.MlKem.X86_64.Sample4Impl := .scalar

end VG.Variants.MlKemSample4.X86_64.Scalar
