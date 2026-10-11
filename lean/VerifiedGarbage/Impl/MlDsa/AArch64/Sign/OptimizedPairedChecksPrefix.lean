module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedZ
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedLow
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

def pairedChecksPrefix (p : Params) : Prog isa :=
  .seq (.seq (callAt "vg_mldsa_ntt_positive" VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      [(.x0,.ptr cP)])
    (.seq (.block (([.movz .x .x24 1 0] : List Instr)++setQ (sc oONES) 0)) (zPairedVector p))) (pairedLowPhase p)

end VG.Impl.MlDsa.AArch64.Sign.Optimized
