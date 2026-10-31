module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedHints

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

/-- Run a phase until the first polynomial fails its norm check. -/
def seqOk (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n+1 => .seq (f a) (ifOk (seqOk f (a+1) n))

/-- Stop at the first failing response or low-part polynomial. Every
coefficient of each reached polynomial is checked. -/
def pairedChecks (p : Params) : Prog isa :=
  .seq (.seq (callAt "vg_mldsa_ntt_positive" VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      [(.x0,.ptr cP)])
    (.seq (.block (([.movz .x .x24 1 0] : List Instr)++setQ (sc oONES) 0)) (seqOk (zR p) 0 p.ℓ)))
    (ifOkElse
      (.seq (seqOk (r0R p) 0 p.k)
        (ifOkElse
          (.seq (hintPairedVector p)
            (.seq (.block (onesOk p))
              (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p)))))
          (.block (kapAdd p))))
      (.block (kapAdd p)))

end VG.Impl.MlDsa.AArch64.Sign.Optimized
