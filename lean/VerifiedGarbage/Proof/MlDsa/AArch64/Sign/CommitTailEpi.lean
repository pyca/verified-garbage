import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailPro

/-! ## From `CommitTailRestoreV.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_ldrq)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Restores every nonvolatile vector from the untouched save area. -/
theorem restoreV_ok {σ s : State} (hs : Saved σ s.mem) (hptr : s.gpr .x3=σ.gpr .x3)
    (hin : ∀i<8, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block restore) s fun t => RegKeep [] s t ∧ t.mem=s.mem ∧
      ∀i<8,t.v (vreg (8+i))=σ.v (vreg (8+i)) := by
  unfold restore
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep [] s t ∧ t.mem=s.mem ∧ ∀i<k,t.v (vreg (8+i))=σ.v (vreg (8+i)))
    (fun k t hk ht => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,fun _ h => by omega⟩
  refine wp_ldrq ⟨by omega,by omega⟩ (by rw [ht.1.gpr .x3 (by simp),hptr])
    (by rw [ht.1.rd,ht.1.wr]; exact hin k hk) fun u hu => WP.block_nil_iff.mpr ?_
  refine ⟨(ht.1.trans (RegKeep.vupd hu)).mono (by simp),hu.mem.trans ht.2.1,?_⟩
  intro i hi
  by_cases he : i=k
  · subst i
    rw [hu.v,ht.2.1,hs.vec k hk]
  · have hne : vreg (8+i)≠vreg (8+k) := by
      rw [ne_eq,vreg_inj (8+i) (by omega) (8+k) (by omega)]; omega
    rw [hu.get _ hne]
    exact ht.2.2 i (by omega)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailRestoreG.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

private theorem saved_mem : ∀i<4,saved[i]!∈saved := by decide
private theorem saved_inj : ∀i<4,∀j<4,saved[i]! =saved[j]! ↔ i=j := by decide

/-- Restores all four scalar saves, including the incoming return address. -/
theorem restoreG_ok {σ s : State} (hs : Saved σ s.mem) (hptr : s.gpr .x3=σ.gpr .x3)
    (hin : ∀i<4, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (128+8*i)) 8) :
    WP isa (.block ((List.range 4).map fun i => .ldr .x saved[i]! .x3 (128+8*i))) s fun t =>
      RegKeep saved s t ∧ t.mem=s.mem ∧ t.v=s.v ∧
      ∀i<4,t.gpr saved[i]! =σ.gpr saved[i]! := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep saved s t ∧ t.mem=s.mem ∧ t.v=s.v ∧
      ∀i<k,t.gpr saved[i]! =σ.gpr saved[i]!)
    (fun k t hk ht => ?_) 4 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,rfl,fun _ h => by omega⟩
  refine wp_ldr ⟨by omega,by omega⟩ (by rw [ht.1.gpr .x3 (by decide),hptr])
    (by rw [ht.1.rd,ht.1.wr]; exact hin k hk) fun u hu => WP.block_nil_iff.mpr ?_
  refine ⟨(ht.1.trans (RegKeep.upd hu)).mono ?_,hu.mem.trans ht.2.1,hu.vec.trans ht.2.2.1,?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · rcases List.mem_singleton.mp hr with rfl
      exact saved_mem k hk
  · intro i hi
    by_cases he : i=k
    · subst i
      rw [hu.gpr,ht.2.1,hs.regs k hk]
    · have hne : saved[i]!≠saved[k]! := by
        rw [ne_eq,saved_inj i (by omega) k hk]; exact he
      rw [hu.other _ hne]
      exact ht.2.2.2 i (by omega)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailEpi.lean` -/

section

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

end
