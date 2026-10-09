import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedMasks

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa

def commitWith (c : VG.Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (masks P p) (.seq (seqR (rowW p) 0 p.k)
    (.seq (seqR (w1R P p) 0 p.k)
      (shakeAtWith c [⟨.x26,0,64⟩,⟨.x28,oW1,p.k*w1Len p⟩] ⟨.x28,oCT,cLen p⟩)))

end VG.Impl.MlDsa.AArch64.Sign.Optimized
