module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedHints

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

/-- Stop after a complete vector norm check rejects the attempt. No branch
identifies an individual polynomial or coefficient. -/
def pairedChecks (p : Params) : Prog isa :=
  .seq (.seq (callAt "vg_mldsa_ntt_positive" VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      [(.x0,.ptr cP)])
    (.seq (.block (([.movz .x .x24 1 0] : List Instr)++setQ (sc oONES) 0)) (zPairedVector p)))
    (ifOkElse
      (.seq (pairedLowPhase p)
        (ifOkElse
          (.seq (hintPairedVector p)
            (.seq (.block (onesOk p))
              (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p)))))
          (.block (kapAdd p))))
      (.block (kapAdd p)))

end VG.Impl.MlDsa.AArch64.Sign.Optimized
