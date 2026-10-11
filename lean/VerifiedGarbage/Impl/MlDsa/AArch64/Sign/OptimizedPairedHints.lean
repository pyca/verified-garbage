module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedHints
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

def hintPairRow (p : Params) (i : Nat) : Prog isa :=
  callAt "vg_mldsa_fused_pair_h" (VG.Impl.MlDsa.AArch64.Optimized.Paired.selected .h)
    [(.x0,.ptr cP),(.x1,.ptr (t0P p i)),(.x2,.ptr (hP i)),(.x3,.ptr (wP p i)),(.x4,.ptr t1P),
      (.x5,.imm p.γ₂),(.x6,.imm p.γ₂)]

def hintPair (p : Params) (i : Nat) : Prog isa := .seq (hintPairRow p i) (.block hintFinish)

def hintPairedVector (p : Params) : Prog isa := seqR (fun j=>hintPair p (2*j)) 0 (p.k/2)

end VG.Impl.MlDsa.AArch64.Sign.Optimized
