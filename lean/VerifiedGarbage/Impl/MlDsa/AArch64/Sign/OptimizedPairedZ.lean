module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedResponse
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

/-- Process both response polynomials before incorporating their joint norm. -/
def zPair (p : Params) (i : Nat) : Prog isa :=
  .seq (callAt "vg_mldsa_fused_pair_z" (VG.Impl.MlDsa.AArch64.Optimized.Paired.selected .z)
    [(.x0,.ptr cP),(.x1,.ptr (s1P p i)),(.x2,.ptr (yP p i)),(.x3,.ptr t1P),(.x4,.ptr t1P),
      (.x5,.imm p.γ₁),(.x6,.imm (p.γ₁-p.β))]) (.block and24)

end VG.Impl.MlDsa.AArch64.Sign.Optimized
