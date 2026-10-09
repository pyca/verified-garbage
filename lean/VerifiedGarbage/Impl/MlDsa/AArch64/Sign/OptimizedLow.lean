import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedResponse

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

/-- Retain high and signed low parts for the following hint phase; every
row contributes to the same strict rejection accumulator. -/
def r0R (p : Params) (i : Nat) : Prog isa :=
  .seq (responseProduct t1P (s2P p i))
    (.seq (callAt "vg_mldsa_signed_sub_low_norm" VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
      [(.x0,.ptr (wP p i)),(.x1,.ptr t1P),(.x2,.ptr (hP i)),
       (.x3,.imm p.γ₂),(.x4,.imm (p.γ₂-p.β))]) (.block and24))

end VG.Impl.MlDsa.AArch64.Sign.Optimized
