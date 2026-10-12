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

/-- The odd final polynomial uses the existing single response path. -/
def zPairedVector (p : Params) : Prog isa :=
  .seq (seqR (fun j => zPair p (2*j)) 0 (p.ℓ/2))
    (if p.ℓ%2=1 then zR p (p.ℓ-1) else .block [])

end VG.Impl.MlDsa.AArch64.Sign.Optimized
