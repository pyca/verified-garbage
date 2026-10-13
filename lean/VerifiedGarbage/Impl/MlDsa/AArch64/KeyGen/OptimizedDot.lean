module

public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.KeyGen
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.DotInverse

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call

def dotRow (p : Spec.MlDsa.Params) (i : Nat) : Prog isa :=
  callAt ("vg_mldsa_dot_inverse" ++ toString p.ℓ)
    (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode p.ℓ)
    [(.x0,.ptr (tP p)),(.x1,.ptr (aP (p.ℓ*i))),(.x2,.ptr (sP p 0)),(.x3,.ptr (sc oSS))]

end VG.Impl.MlDsa.AArch64.KeyGen.Optimized
