import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackAdvance

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem fourAdvance_ok (s : State) :
    WP isa (.block (advance 4 16)) s fun t =>
      ((t.gpr .x0=s.gpr .x0+64 ∧ t.gpr .x2=s.gpr .x2+8 ∧
        t.gpr .x15=s.gpr .x15-1 ∧ t.mem=s.mem) ∧ Keep [.x0,.x2,.x15] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  arun [advance]
  exact ⟨rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
