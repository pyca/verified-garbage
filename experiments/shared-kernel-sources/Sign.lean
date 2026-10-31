module

public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedLoop
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest

/-! # Shared signing body for ordinary and prepared ML-DSA keys -/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.Call

namespace Sign
open VG.Impl.MlDsa.AArch64.Sign

def restoreSecrets (p : Params) : Prog isa :=
  .seq (seqR (fun i => copy (s1P p i) (.x21, 1024 * i) 1024) 0 p.ℓ)
    (.seq (seqR (fun i => copy (s2P p i) (.x21, 1024 * (p.ℓ + i)) 1024) 0 p.k)
      (seqR (fun i => copy (t0P p i) (.x21, 1024 * (p.ℓ + p.k + i)) 1024) 0 p.k))

def initialization (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .ite (.nonzero .x .x22)
    (.seq (restoreSecrets p)
      (shakeAtWith c [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, oMS, 64⟩))
    (positiveDecodeWith c P p)

def core (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  let checks := Optimized.pairedChecks p
  let paired := c.pairedSha3 && p.k != 4
  let rest := .seq (initialization c P p)
    (.seq (if paired then Cached.signLoop P p checks else Optimized.signLoopWith c P p checks)
      (ifOk (Optimized.output P p)))
  .seq (.block pro)
    (.seq (if paired then CachedMatrix.expandA P p else expandA P p)
      (.seq (ifOk rest) (.block epi)))

/-- `x5` is the optional cache pointer; `x6` is its public slice length.
The original ABI's `x21` and `x22` are saved outside the existing workspace. -/
def withCache (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .frame (.push .x21)
    (.frame (.push .x22)
      (.seq (.block [.addImm .x .x21 .x5 0, .addImm .x .x22 .x6 0])
        (core c P p)) (.pop .x22)) (.pop .x21)

def entry (name : String) (code : Prog isa) (p : Params) (prepared : Bool) : Prog isa :=
  .frame (.push .x30)
    (.seq (.block (if prepared then
      lea .x5 .x0 p.skLen ++ movV .x6 (1024 * (p.ℓ + 2 * p.k))
      else [.addImm .x .x5 .x0 0] ++ movV .x6 0)) (.call name code)) (.pop .x30)

end Sign
end VG.Impl.MlDsa.AArch64.PreparedKey
