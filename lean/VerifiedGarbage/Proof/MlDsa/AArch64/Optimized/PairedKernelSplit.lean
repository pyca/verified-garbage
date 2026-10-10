import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstKernel
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalReturn
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMiddle
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Only reassociate the measured blocks; no scheduling or arithmetic changes. -/
theorem checkKernel_wp (hint : Bool) (g : Nat) {s : State} {Q : State→Prop}
    (h : WP isa (.seq firstKernel (.seq
      (.block (middleMoves++constants (if hint then .h else .z) g)) (finalKernel hint))) s Q) :
    WP isa (kernel (if hint then .h else .z) g) s Q := by
  have he : kernel (if hint then .h else .z) g=
      .seq (.block init) (.seq
      (.loop (.block VG.Impl.MlDsa.AArch64.Optimized.PairedBase.firstBlock) (.nonzero .x .x11))
      (.seq (.block (middleMoves++constants (if hint then .h else .z) g)) (finalKernel hint))) := by
    cases hint
    · rw [show (if false then Kind.h else Kind.z)=Kind.z by rfl]
      simp only [kernel,finalKernel,final_z_eq,init,middleMoves,
        VG.Impl.MlDsa.AArch64.Optimized.Paired.vc,List.append_assoc]
      rfl
    · rw [show (if true then Kind.h else Kind.z)=Kind.h by rfl]
      simp only [kernel,finalKernel,final_h_eq,init,middleMoves,
        VG.Impl.MlDsa.AArch64.Optimized.Paired.vc,List.append_assoc]
      rfl
  rw [he]
  exact WP.assoc h

theorem lowKernel_wp (g : Nat) {s : State} {Q : State→Prop}
    (h : WP isa (.seq firstKernel (.seq (.block (middleMoves++constants .r0 g)) (lowKernel g))) s Q) :
    WP isa (kernelPaired g) s Q := by
  have he : kernelPaired g=.seq (.block init) (.seq
      (.loop (.block VG.Impl.MlDsa.AArch64.Optimized.PairedBase.firstBlock) (.nonzero .x .x11))
      (.seq (.block (middleMoves++constants .r0 g)) (lowKernel g))) := by
    simp only [kernelPaired,lowKernel,final_r0_eq,init,middleMoves,
      VG.Impl.MlDsa.AArch64.Optimized.Paired.vc,List.append_assoc]
    rfl
  rw [he]
  exact WP.assoc h

end VG.Proof.MlDsa.AArch64.Optimized.Paired
