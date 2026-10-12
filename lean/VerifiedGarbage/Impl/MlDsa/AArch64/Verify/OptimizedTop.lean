module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Optimized
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.OptimizedSamples

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call

def bodyWith (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (hint P p) (ifOk (.seq (seqR (zOne P p) 0 p.ℓ)
    (ifOk (.seq (OptimizedSamples.samples P p) (computeWith c P p)))))

def verifyWith (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq (bodyWith c P p) (.block epi))

end VG.Impl.MlDsa.AArch64.Verify.Optimized
