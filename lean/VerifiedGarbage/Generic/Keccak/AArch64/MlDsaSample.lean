module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSelected
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSelected
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMask
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejSelected
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSelected
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatchTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailReadyTiming
public import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFirst
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFrame
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallTry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTTop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
public import VerifiedGarbage.Proof.MlKem.Compress
public import VerifiedGarbage.Proof.MlKem.Encode
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds
public import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
public import VerifiedGarbage.Proof.Sha3.Arith
public import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFirst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallTry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseAddress
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBodyTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTail
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTimingDone
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStream
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackConst
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTTop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ProArgs
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveG
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Round.Mem
import VerifiedGarbage.Proof.MlDsa.Sample.LeNat
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Spec.MlDsa.RejNTT2
import VerifiedGarbage.TCB.Axioms

/-! # ML-DSA (FIPS 204) on AArch64: the sampling primitives -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaSample

open VG

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlDsa.rejNTT4Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlDsa.AArch64.Optimized.ResidentRej.selected v.callee.pairedSha3
    verified := Proof.MlDsa.AArch64.Optimized.ResidentRej.selected_verified v.callee.pairedSha3 },
  Spec.MlDsa.sampleInBallApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlDsa.AArch64.Optimized.Ball.selected v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.Optimized.Ball.selected_verified v }] ++
  -- Only the SHA-3 extension's signing calls `ExpandMask` one polynomial at a
  -- time (`vg_mldsa_expand_mask_poly_sha3`).
  if v.callee.pairedSha3 then [
    Spec.MlDsa.expandMaskApi.artifact AArch64.target {
      suffix := v.callee.suffix
      features := v.features
      code := Impl.MlDsa.AArch64.Sample.expandMaskWith v.callee
      stack := 16
      verified := Proof.MlDsa.AArch64.Sample.expandMask_verifiedWith v }] else []

end VG.Generic.Keccak.AArch64.MlDsaSample
