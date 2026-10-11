module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedHints
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLow
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

/-- All response and low-part norms run before constructing hints. -/
def checksPrefix (p : Params) : Prog isa :=
  .seq (.seq (callAt "vg_mldsa_ntt_positive" VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      [(.x0,.ptr cP)])
    (.seq (.block (([.movz .x .x24 1 0] : List Instr)++setQ (sc oONES) 0)) (seqR (zR p) 0 p.ℓ)))
    (seqR (r0R p) 0 p.k)

/-- Complete strict checks followed by the existing accept/reject loop update. -/
def checks (p : Params) : Prog isa :=
  .seq (checksPrefix p) (.seq (seqR (hR p) 0 p.k)
    (.seq (.block (onesOk p))
      (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p)))))

end VG.Impl.MlDsa.AArch64.Sign.Optimized
