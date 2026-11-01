module

import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallResident
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BallDispatch
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.Ball

theorem selected_verified (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target
    (selected v.callee) (Proof.MlDsa.sampleInBallContract AArch64.abi 16) := by
  unfold selected
  split
  · exact resident_verified
  · exact Sample.sampleInBall_verifiedWith v

theorem selected_correct (v : Proof.Sha3.AArch64.Permutation) (σ : State) (hp : sbK.pre σ) :
    WP isa (selected v.callee) σ (fun u => abiPreserved σ u ∧ sbK.post σ u) := by
  unfold selected
  split
  · exact correctWith Proof.Sha3.AArch64.Sha3.ResidentBackend.backend σ hp
  · exact Sample.Ball.correctWith v σ hp

theorem codeWith_depth (v : Proof.Sha3.AArch64.Permutation) : (codeWith v.callee).aarch64Depth=1 := by
  simp only [codeWith,zeroWide,first,second,loop,earlyBody,Impl.MlDsa.AArch64.Sample.bTry,
    Code.aarch64Depth,sponge_depth v,v.squeeze_depth,Nat.max_self,Nat.max_zero,Nat.zero_max]

theorem selected_depth (v : Proof.Sha3.AArch64.Permutation) : (selected v.callee).aarch64Depth=1 := by
  unfold selected
  split
  · exact codeWith_depth Proof.Sha3.AArch64.Sha3.ResidentBackend.backend
  · exact Sample.ball_depth v
end VG.Proof.MlDsa.AArch64.Optimized.Ball
