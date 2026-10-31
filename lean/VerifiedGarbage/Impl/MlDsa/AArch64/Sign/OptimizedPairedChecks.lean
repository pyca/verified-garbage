module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedHints

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

/-- Check fused polynomial pairs until one fails; an odd tail uses the
single-polynomial helper. Both polynomials of each reached pair are complete. -/
def seqPairedOk (one two : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | 1 => one a
  | n+2 => .seq (two a) (ifOk (seqPairedOk one two (a+2) n))

/-- Stop at the first failing response or low-part pair, preserving the
fused inverse transforms. Every coefficient of each reached pair is checked. -/
def pairedChecks (p : Params) : Prog isa :=
  .seq (.seq (callAt "vg_mldsa_ntt_positive" VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      [(.x0,.ptr cP)])
    (.seq (.block (([.movz .x .x24 1 0] : List Instr)++setQ (sc oONES) 0)) (seqPairedOk (zR p) (zPair p) 0 p.ℓ)))
    (ifOkElse
      (.seq (seqPairedOk (r0R p) (r0Pair p) 0 p.k)
        (ifOkElse
          (.seq (hintPairedVector p)
            (.seq (.block (onesOk p))
              (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p)))))
          (.block (kapAdd p))))
      (.block (kapAdd p)))

end VG.Impl.MlDsa.AArch64.Sign.Optimized
