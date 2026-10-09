import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailAdjust
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample (coeffAddr)

theorem tailSetup_ok {v k len : Nat} {σ s : State} (hp : Pre v σ) (he : Env v σ s)
    (hk : k<v) (hl : len<256) (hc : (s.gpr .x4).toNat=256-len) :
    WP isa (.block (tailCursor k++tailRead k++tailAdjust)) s fun t =>
      Only [.x3,.x4,.x6,.x7,.x9] s t ∧
      ∃skip≤1,t.gpr .x3=coeffAddr (polyP σ k) (len+skip) ∧
        (t.gpr .x4).toNat=256-(len+skip) ∧ t.gpr .x9=0 := by
  have hk4 : k<4 := by have := hp.streams; omega
  rw [List.append_assoc,WP.block_append_iff]
  apply WP.mono (tailCursor_ok hk4 (by omega) hc)
  intro a ha
  rw [WP.block_append_iff]
  have hr : InRegions (a.rd++a.wr)
      (a.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4 := by
    rw [ha.1.rd,ha.1.wr,ha.1.get .x19,he.x19]
    exact in_scr_rd hp he.wr (by omega)
  apply WP.mono (tailRead_ok hk4 hr)
  intro b hb
  apply WP.mono (tailAdjust_ok hl (p := polyP σ k) (by
    rw [hb.get .x3,ha.2,he.x21]; rfl) (by rw [hb.get .x4,ha.1.get .x4]; exact hc))
  intro t ht
  exact ⟨((ha.1.trans hb).trans ht.1).mono (by decide),ht.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
