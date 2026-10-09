import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourStep

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (acc accept_ok)
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- One scalar tail iteration has the same accepted-prefix semantics as
one candidate of either vector path. -/
theorem scalarStep_ok {s : State} {p : Addr} {L : List Zq}
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2) 4)
    (h10 : s.gpr .x10=0x7fffff)
    (h9 : (s.gpr .x9).toNat=q)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length) (hL : L.length<256)
    (hst : Stored s.mem p L) (hw : InRegions s.wr (s.gpr .x3) 4) :
    WP isa (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr))) s fun t =>
      Keep [.x11,.x2,.x5,.x3,.x4,.x13,.x14,.x15,.x16] s t ∧
      t.v=s.v ∧ Frame [polyR p] s.mem t.mem ∧
      t.gpr .x2=s.gpr .x2+3 ∧ t.gpr .x5=s.gpr .x5-1 ∧
      t.gpr .x3=coeffAddr p (acc L (candidate s.mem (s.gpr .x2))).length ∧
      (t.gpr .x4).toNat=256-(acc L (candidate s.mem (s.gpr .x2))).length ∧
      t.gpr .x16=t.gpr .x4*t.gpr .x5 ∧
      Stored t.mem p (acc L (candidate s.mem (s.gpr .x2))) := by
  refine WP.mono (WP.keepV (Q := fun t =>
    Keep [.x11,.x2,.x5,.x3,.x4,.x13,.x14,.x15,.x16] s t ∧
    Frame [polyR p] s.mem t.mem ∧
    t.gpr .x2=s.gpr .x2+3 ∧ t.gpr .x5=s.gpr .x5-1 ∧
    t.gpr .x3=coeffAddr p (acc L (candidate s.mem (s.gpr .x2))).length ∧
    (t.gpr .x4).toNat=256-(acc L (candidate s.mem (s.gpr .x2))).length ∧
    t.gpr .x16=t.gpr .x4*t.gpr .x5 ∧
    Stored t.mem p (acc L (candidate s.mem (s.gpr .x2)))) (by decide) ?_)
    (fun t ⟨⟨hk,hf,h2,h5,h3',h4',h16,hs⟩,hv⟩ => ⟨hk,hv,hf,h2,h5,h3',h4',h16,hs⟩)
  rw [WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (scalarChunk_ok hr) fun a ⟨ha,h2,h5,h11⟩ => ?_
  have hz : (a.gpr .x11).toNat=candidate s.mem (s.gpr .x2) := by
    rw [h11,h10]
    exact scalar_candidate _ _
  refine WP.mono (accept_ok (aP := p) (L := L) hz (candidate_bound _ _)
    (by rw [ha.get .x9]; exact h9) (by rw [ha.get .x3]; exact h3)
    (by rw [ha.get .x4]; exact h4) hL (by rw [ha.mem]; exact hst)
    (by rw [ha.wr,←h3]; exact hw)) fun b ⟨hb,hf,hp,hc,hs⟩ => ?_
  refine wp_mul fun t ht et => wp_nil ?_
  refine ⟨((ha.keep.trans hb).trans ht.keep).mono (by decide),?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.mem,←ha.mem]; exact hf
  · rw [ht.get .x2,hb.get .x2]; exact h2
  · rw [ht.get .x5,hb.get .x5]; exact h5
  · rw [ht.get .x3]; exact hp
  · rw [ht.get .x4]; exact hc
  · rw [et,ht.get .x4,ht.get .x5]
  · rw [ht.mem]; exact hs

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
