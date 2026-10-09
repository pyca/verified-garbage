import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.KeyGen
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt

namespace VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call

def nttSecret (p : Spec.MlDsa.Params) (j : Nat) : Prog isa :=
  callAt "vg_mldsa_ntt_positive" VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
    [(.x0,.ptr (sP p j))]

end VG.Impl.MlDsa.AArch64.KeyGen.Optimized
