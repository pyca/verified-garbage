import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedMatrix
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedSecrets
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedRest

namespace VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64

def prefixWith (c : Impl.Sha3.AArch64.Callee) (P : Prims) (two : Prog isa) (p : Spec.MlDsa.Params) : Prog isa :=
  .seq (.block pro) (.seq (seedsWith c p) (.seq (matrixWith two P p) (secretsWith c p)))

def codeWith (c : Impl.Sha3.AArch64.Callee) (P : Prims) (two : Prog isa) (p : Spec.MlDsa.Params) : Prog isa :=
  .seq (prefixWith c P two p) (.seq (restWith c P p) (.block epi))

end VG.Impl.MlDsa.AArch64.KeyGen.Optimized
