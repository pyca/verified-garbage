module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLoop
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedInitialization
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedOutput

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa

def restWith (c : VG.Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) (checks : Prog isa) : Prog isa :=
  .seq (positiveDecodeWith c P p) (.seq (signLoopWith c P p checks) (ifOk (output P p)))

def signWith (c : VG.Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) (checks : Prog isa) : Prog isa :=
  .seq (.block pro) (.seq (expandA P p) (.seq (ifOk (restWith c P p checks)) (.block epi)))

end VG.Impl.MlDsa.AArch64.Sign.Optimized
