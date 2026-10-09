import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopCorrect

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

theorem pairedCommit_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp3 : Sign.Ok3 p) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.commitWith v.callee (Sign.primsWith v.callee) p) := by
  have C := Sign.prims_okWith (keccak := v)
  obtain ⟨ha,hp,hs⟩ := keccak_dle v
  have hm := DLe.of_fd C.expandMask.fd
  have hm2 := DLe.of_fd C.expandMaskPair.fd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.outNtt := ⟨by decide +kernel⟩
  have hd : DLe 1 (Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode p.ℓ) := by
    rcases hp3 with rfl|rfl|rfl <;> exact ⟨by decide +kernel⟩
  have hh : DLe 1 ((Sign.primsWith v.callee).highPack p.γ₂) := by
    dsimp only [Sign.primsWith,Impl.MlDsa.AArch64.Optimized.HighPack.code]
    dle_tac
  unfold Impl.MlDsa.AArch64.Sign.Optimized.commitWith
  dle_tac
  unfold Impl.MlDsa.AArch64.Sign.Optimized.masks
  split <;> dle_tac

theorem pairedBall_dle (v : Proof.Sha3.AArch64.Permutation) (p : Spec.MlDsa.Params) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.ballAt (Sign.primsWith v.callee)
      (Impl.MlDsa.AArch64.Sign.cLen p) p.τ Impl.MlDsa.AArch64.Sign.cP) := by
  have hb := DLe.of_fd (Sign.prims_okWith (keccak := v)).ball.fd
  dle_tac

theorem pairedInitialization_dle (v : Proof.Sha3.AArch64.Permutation) (p : Spec.MlDsa.Params) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.positiveDecodeWith v.callee (Sign.primsWith v.callee) p) := by
  have C := Sign.prims_okWith (keccak:=v)
  have hu := DLe.of_fd C.bitUnpack.fd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt := ⟨by decide +kernel⟩
  obtain ⟨ha,hp,hs⟩ := keccak_dle v
  unfold Impl.MlDsa.AArch64.Sign.positiveDecodeWith
  dle_tac

end VG.Proof.MlDsa.AArch64.Message

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem selectedPairedSignLoop_ok (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : Ok3 p) {σ s : State}
    (h : PositiveIK p 16 σ s) (roots : PairedRoots 16 s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith v.callee (primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) s fun u=>
      PositiveXS p 16 σ u ∧ PairedRoots 16 u := by
  apply pairedSignLoop_ok (keccak:=v) (prims_okWith (keccak:=v)) hp (bChk_ok hp)
    (checks:=Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) _ _ _ h roots
  · have hd := (Message.pairedCommit_dle v hp).le
    change 16 * _ ≤ 16
    omega
  · have hd := (Message.pairedBall_dle v p).le
    change 16 * _ ≤ 16
    omega
  · intro σ s t hi ri h1
    exact positivePairedChecks_ok hp (by rcases hp with rfl|rfl|rfl <;> decide)
      (by decide) (by decide) ri hi h1

end VG.Proof.MlDsa.AArch64.Sign
