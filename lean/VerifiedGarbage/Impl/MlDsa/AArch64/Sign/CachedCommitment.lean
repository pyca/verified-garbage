import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedCommitment
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CommitTail

namespace VG.Impl.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call

/-- Copy the cached odd mask in the measured 128-word loop. -/
def copyBody : List Instr :=
  [.ldr .x .x9 .x1 0,.str .x .x9 .x0 0,.addImm .x .x0 .x0 8,
    .addImm .x .x1 .x1 8,.subImm .x .x2 .x2 1]

def copyMask (p : Params) : Prog isa :=
  .seq (.block (lea .x0 .x28 (yP p (p.ℓ-1)).2 ++ lea .x1 .x28 t4P.2 ++ movV .x2 128))
    (.loop (.block copyBody) (.nonzero .x .x2))

/-- The first attempt samples its odd mask; later attempts consume the
mask computed alongside the previous commitment. κ is a public index. -/
def tailMask (P : Prims) (p : Params) : Prog isa :=
  .seq (.block [.ldr .x .x9 .x28 oKAP])
    (.seq (.ite (.nonzero .x .x9) (copyMask p)
      (.seq (.block (setKappa (p.ℓ-1))) (maskAt P p.γ₁ (yP p (p.ℓ-1)))))
      (Optimized.maskFinish p (p.ℓ-1)))

def masks (P : Prims) (p : Params) : Prog isa :=
  .seq (seqR (fun j=>Optimized.maskPairR p "vg_mldsa_expand_mask_pair_sha3" P.expandMaskPair (2*j))
    0 (p.ℓ/2)) (tailMask P p)

def hashArgs (_p : Params) : List (Reg × Arg) :=
  [(.x0,.ptr (.x26,0)),(.x1,.ptr (sc oW1)),(.x2,.ptr (sc oCT)),
    (.x3,.ptr t1P),(.x4,.ptr (sc oMS)),(.x5,.ptr (.x9,0)),(.x6,.ptr t4P)]

/-- Hash the commitment while sampling the odd mask of the next attempt. -/
def hash (p : Params) : Prog isa :=
  .seq (.block [.ldr .x .x9 .x28 oKAP,.addImm .x .x9 .x9 (2*p.ℓ-1)])
    (callAt (if p.ℓ=5 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87")
      (CommitTail.code (p.k*w1Len p) (cLen p))
      (hashArgs p))

def commit (P : Prims) (p : Params) : Prog isa :=
  .seq (masks P p) (.seq (seqR (Optimized.rowW p) 0 p.k)
    (.seq (seqR (w1R P p) 0 p.k) (hash p)))

end VG.Impl.MlDsa.AArch64.Sign.Cached
