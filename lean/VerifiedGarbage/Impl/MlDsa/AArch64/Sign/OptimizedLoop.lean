import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedCommitment

namespace VG.Impl.MlDsa.AArch64.Sign.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

/-- The existing bounded rejection schedule around the optimized phases. -/
def iterWith (c : VG.Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) (checks : Prog isa) : Prog isa :=
  .seq (commitWith c P p) (.seq (ballAt P (cLen p) p.τ cP)
    (.seq (.ite (.nonzero .w .x0) checks
      (.block (([.movz .x .x24 0 0] : List Instr)++setQ (sc oCNT) 1))) (.block cntDec)))

def signLoopWith (c : VG.Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) (checks : Prog isa) : Prog isa :=
  .seq (.block (setQ (sc oKAP) 0++setQ (sc oCNT) 814))
    (.loop (iterWith c P p checks) (.nonzero .x .x9))

end VG.Impl.MlDsa.AArch64.Sign.Optimized
