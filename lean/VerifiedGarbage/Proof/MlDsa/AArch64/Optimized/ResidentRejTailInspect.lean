import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailReadValue

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample (coeffAddr)

theorem tailInspect_ok {s : State} {k len : Nat} (hk : k<4) (hl : len≤256)
    (hc : (s.gpr .x4).toNat=256-len)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4) :
    WP isa (.block (tailCursor k++tailRead k)) s fun t =>
      Only [.x3,.x6,.x7] s t ∧
      t.gpr .x3=coeffAddr (s.gpr .x21+BitVec.ofNat 64 (1024*k)) len ∧
      (t.gpr .x6).toNat=candidate s.mem (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) ∧
      (t.gpr .x7).toNat=8380417 := by
  rw [WP.block_append_iff]
  refine WP.mono (tailCursor_ok hk hl hc) fun a ⟨ha,h3⟩ => ?_
  refine WP.mono (tailRead_value hk (by rw [ha.rd,ha.wr,ha.get .x19]; exact hr))
    fun t ⟨ht,h6,h7⟩ => ?_
  refine ⟨(ha.trans ht).mono (by decide),?_,?_,h7⟩
  · rw [ht.get .x3]; exact h3
  · rw [ha.mem,ha.get .x19] at h6
    exact h6

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
