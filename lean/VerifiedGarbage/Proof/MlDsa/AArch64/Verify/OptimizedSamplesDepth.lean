import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamples
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Message

/-- Replacing scalar rejection tails by the resident pair adds no stack depth. -/
theorem samples_depth {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params) :
    16*(Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p).aarch64Depth≤S := by
  have h1 : DLe (S/16) P.rejNtt := ⟨by have := hP.rejNtt.fd;omega⟩
  have h4 : DLe (S/16) P.rej4 := ⟨by have := hP.rej4.fd;omega⟩
  have hb : DLe (S/16) P.ball := ⟨by have := hP.ball.fd;omega⟩
  have h2 : DLe (S/16) Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code := by
    have hd : Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code.aarch64Depth=0 := by decide +kernel
    exact ⟨by rw [hd];omega⟩
  have hd : DLe (S/16) (Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p) := by
    unfold Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples
      Impl.MlDsa.AArch64.Verify.OptimizedSamples.expAll
    split
    · unfold Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4
        Impl.MlDsa.AArch64.Verify.OptimizedSamples.tail2
        Impl.MlDsa.AArch64.Optimized.MatrixMask.code
      dle_tac
    · unfold Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4
        Impl.MlDsa.AArch64.Optimized.MatrixMask.code
      dle_tac
  have := hd.le
  omega

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
