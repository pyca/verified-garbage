import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailRestoreG

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_mov)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- The outer helper restores its captured nonvolatile vectors and scalar
registers without changing any result or workspace bytes. -/
theorem epi_ok {σ s : State} (hs : Saved σ s.mem) (hptr : s.gpr .x19=σ.gpr .x3)
    (hv : ∀i<8, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (16*i)) 16)
    (hg : ∀i<4, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (128+8*i)) 8) :
    WP isa (.block epi) s fun t =>
      RegKeep (.x3::saved) s t ∧ t.mem=s.mem ∧
      (∀i<8,t.v (vreg (8+i))=σ.v (vreg (8+i))) ∧
      (∀i<4,t.gpr saved[i]! =σ.gpr saved[i]!) := by
  unfold epi
  change WP isa (.block (Impl.MlKem.AArch64.mov .x3 .x19 ::
    (restore ++ (List.range 4).map fun i => .ldr .x saved[i]! .x3 (128+8*i)))) s _
  refine wp_mov fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (restoreV_ok (by rw [ha.mem]; exact hs) (ha.gpr.trans hptr)
    (fun i hi => by rw [ha.rd,ha.wr]; exact hv i hi)) fun b ⟨hb,hmb,hvb⟩ => ?_
  refine WP.mono (restoreG_ok (by rw [hmb,ha.mem]; exact hs)
    ((hb.gpr .x3 (by simp)).trans (ha.gpr.trans hptr))
    (fun i hi => by rw [hb.rd,hb.wr,ha.rd,ha.wr]; exact hg i hi))
    fun t ⟨ht,hmt,hvt,hgt⟩ => ?_
  refine ⟨(((RegKeep.upd ha).trans hb).trans ht).mono (by simp),
    hmt.trans (hmb.trans ha.mem),?_,hgt⟩
  intro i hi
  rw [hvt]
  exact hvb i hi

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
