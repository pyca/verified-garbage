module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedResponse
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedHintFinish

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

def hintRow (p : Params) (i : Nat) : Prog isa :=
  .seq (responseProduct t1P (t0P p i))
    (callAt "vg_mldsa_signed_hint_norm" VG.Impl.MlDsa.AArch64.Optimized.Response.hintNorm
      [(.x0,.ptr (hP i)),(.x1,.ptr t1P),(.x2,.ptr (wP p i)),(.x3,.imm p.γ₂)])

/-- Every hint row updates the count and rejection flag without branching. -/
def hR (p : Params) (i : Nat) : Prog isa :=
  .seq (hintRow p i) (.block hintFinish)

end VG.Impl.MlDsa.AArch64.Sign.Optimized
