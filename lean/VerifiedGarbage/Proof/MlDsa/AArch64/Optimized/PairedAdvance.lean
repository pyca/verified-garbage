import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirst
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem firstAdvance_ok (s : State) : WP isa (.block firstAdvance) s fun t =>
    ((t.gpr .x0=s.gpr .x0+128 ∧ t.gpr .x1=s.gpr .x1+480 ∧
      t.gpr .x13=s.gpr .x13+128 ∧ t.gpr .x14=s.gpr .x14+128 ∧
      t.gpr .x11=s.gpr .x11-1 ∧ t.mem=s.mem) ∧
      Keep [.x0,.x1,.x11,.x13,.x14] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold firstAdvance
  arun
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
