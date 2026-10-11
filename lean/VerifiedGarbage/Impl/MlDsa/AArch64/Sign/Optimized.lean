module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.DotInverse

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa

/-- Preserve the sampled mask and transform directly into its working slot.
The destination coefficients are positive representatives below three q. -/
def maskFinish (p : Params) (r : Nat) : Prog isa :=
  callAt "vg_mldsa_ntt_positive_from" VG.Impl.MlDsa.AArch64.Optimized.Ntt.outNtt
    [(.x0,.ptr (yhP p r)),(.x1,.ptr (yP p r))]

/-- Accumulate a complete matrix row before one compensated inverse. -/
def rowW (p : Params) (i : Nat) : Prog isa :=
  callAt ("vg_mldsa_dot_inverse" ++ toString p.ℓ)
    (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode p.ℓ)
    [(.x0,.ptr (wP p i)),(.x1,.ptr (aP p i 0)),(.x2,.ptr (yhP p 0)),(.x3,.ptr (sc oPS))]

end VG.Impl.MlDsa.AArch64.Sign.Optimized
