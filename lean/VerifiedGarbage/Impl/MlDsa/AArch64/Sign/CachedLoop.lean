import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedCommitment
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedMatrix
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest

namespace VG.Impl.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

def iter (P : Prims) (p : Params) (checks : Prog isa) : Prog isa :=
  .seq (commit P p) (.seq (ballAt P (cLen p) p.τ cP)
    (.seq (.ite (.nonzero .w .x0) checks
      (.block (([.movz .x .x24 0 0] : List Instr)++setQ (sc oCNT) 1))) (.block cntDec)))

def signLoop (P : Prims) (p : Params) (checks : Prog isa) : Prog isa :=
  .seq (.block (setQ (sc oKAP) 0++setQ (sc oCNT) 814))
    (.loop (iter P p checks) (.nonzero .x .x9))

def restWith (c : VG.Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) (checks : Prog isa) : Prog isa :=
  .seq (positiveDecodeWith c P p) (.seq (signLoop P p checks) (ifOk (Optimized.output P p)))

def signWith (c : VG.Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) (checks : Prog isa) : Prog isa :=
  .seq (.block pro) (.seq (CachedMatrix.expandA P p) (.seq (ifOk (restWith c P p checks)) (.block epi)))

end VG.Impl.MlDsa.AArch64.Sign.Cached
