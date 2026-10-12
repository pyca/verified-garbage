module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call

/-- Decode to canonical coefficients, then use the measured lazy transform.
The existing decoder layout check is sufficient; the transform needs less
scratch than its predecessor. -/
def positiveDecode (P : Prims) (src : Ptr) (len x y j : Nat) : Prog isa :=
  .seq (bitUnpackAt P src len x y (pS j))
    (callAt "vg_mldsa_ntt_positive" VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      [(.x0,.ptr (pS j))])

end VG.Impl.MlDsa.AArch64.Sign
