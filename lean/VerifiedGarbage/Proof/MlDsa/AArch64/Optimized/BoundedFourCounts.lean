import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejCounts
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchGeometry

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

theorem initCounts_ok {s : State} {b : Addr} (hb : s.gpr .x19=b)
    (hw : ∀i<4,InRegions s.wr (countAt b i) 8) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.initCounts) s fun t=>
      (Keep [.x4] s t ∧
      Frame [⟨b+7904#64,32⟩] s.mem t.mem ∧
      ∀i<4,t.mem.readW (countAt b i) 64=256) ∧ t.v=s.v := by
  apply WP.keepV (by rfl)
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.initCounts
  refine wp_movz fun a ha h4=>?_
  refine WP.mono (ResidentRej.countsStore_ok 4 (by decide) (s := a) (p := b)
    (by rw [ha.get .x19]; exact hb) h4 (fun i hi=>by rw [ha.wr]; exact hw i hi))
    fun t ⟨ht,hf,hc⟩=>?_
  refine ⟨?_,?_,hc⟩
  · exact ⟨fun r hr=>by rw [ht.gpr]; exact ha.gpr r hr,
      ht.rd.trans ha.rd,ht.wr.trans ha.wr,ht.sp.trans ha.sp,
      fun r hr=>by rw [ht.vec]; exact ha.vcs r hr⟩
  · rw [ha.mem] at hf
    exact hf

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
