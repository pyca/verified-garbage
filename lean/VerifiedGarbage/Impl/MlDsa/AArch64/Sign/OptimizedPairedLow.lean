import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLow
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

/-- Two low-part checks share the inverse transform schedule; both update
one rejection accumulator only after all their coefficients are checked.
The work buffer spans private temporaries, leaving the challenge intact. -/
def r0Pair (p : Params) (i : Nat) : Prog isa :=
  .seq (callAt "vg_mldsa_fused_pair_r0" (VG.Impl.MlDsa.AArch64.Optimized.Paired.selected .r0)
    [(.x0,.ptr cP),(.x1,.ptr (s2P p i)),(.x2,.ptr (wP p i)),(.x3,.ptr (hP i)),
      (.x4,.ptr t1P),(.x5,.imm p.γ₂),(.x6,.imm (p.γ₂-p.β))]) (.block and24)

def pairedLowPhase (p : Params) : Prog isa :=
  .seq (seqR (fun j => r0Pair p (2*j)) 0 (p.k/2))
    (if p.k%2=0 then .block [] else r0R p (p.k-1))

end VG.Impl.MlDsa.AArch64.Sign.Optimized
