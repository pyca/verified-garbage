import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MultiplyInverse
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

/-- Challenge product with the raw inverse result retained for the fused check. -/
def responseProduct (out secret : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_inverse_raw"
    (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true)
    [(.x0,.ptr out),(.x1,.ptr cP),(.x2,.ptr secret),(.x3,.ptr (sc oPS))]

/-- No rejection branch: every response polynomial contributes to x24. -/
def zR (p : Params) (r : Nat) : Prog isa :=
  .seq (responseProduct t1P (s1P p r))
    (.seq (callAt "vg_mldsa_signed_add_norm" VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
      [(.x0,.ptr (yP p r)),(.x1,.ptr t1P),(.x2,.imm (p.γ₁-p.β))]) (.block and24))

end VG.Impl.MlDsa.AArch64.Sign.Optimized
