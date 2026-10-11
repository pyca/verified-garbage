module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedHints

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

/-- Paired strict checks retain the full norm and hint rejection schedule. -/
def pairedChecks (p : Params) : Prog isa :=
  .seq (pairedChecksPrefix p) (.seq (hintPairedVector p)
    (.seq (.block (onesOk p))
      (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p)))))

end VG.Impl.MlDsa.AArch64.Sign.Optimized
