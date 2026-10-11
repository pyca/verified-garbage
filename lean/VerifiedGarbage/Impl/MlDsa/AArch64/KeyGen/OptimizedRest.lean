module

public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedNtt
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedRow

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call

def restWith (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Spec.MlDsa.Params) : Prog isa :=
  .seq (.block copies) (.seq (seqR (packSecret P p) 0 (p.ℓ+p.k))
    (.seq (seqR (nttSecret p) 0 p.ℓ)
      (.seq (seqR (row P p) 0 p.k) (trHashWith c p))))

end VG.Impl.MlDsa.AArch64.KeyGen.Optimized
