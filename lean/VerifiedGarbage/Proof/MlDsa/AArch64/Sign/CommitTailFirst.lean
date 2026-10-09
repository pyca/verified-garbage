import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailLoadEnd

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (low Lanes)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3 (laneAddr)

def firstState (m : Mem) (mu w1 : Addr) : Spec.Sha3.State :=
  Vector.ofFn fun i => if i.val<8 then m.readW (laneAddr mu i.val) 64
    else if i.val<17 then m.readW (laneAddr w1 (i.val-8)) 64 else 0

/-- Initializes the complete low-lane first block from μ and packed w₁. -/
theorem first_ok {s : State}
    (hmu : ∀j<4, InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hw : ∀j<4, InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*j)) 16)
    (hl : InRegions (s.rd++s.wr) (s.gpr .x1+64) 8) :
    WP isa (.block first) s fun t => RegKeep [.x6] s t ∧ t.mem=s.mem ∧
      Lanes t (firstState s.mem (s.gpr .x0) (s.gpr .x1)) := by
  unfold first
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (loadWords_ok (r:=.x0) 0 4 (by decide) hmu) fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadWords_ok (r:=.x1) 8 4 (by decide) ?_) fun b hb => ?_
  · intro j hj
    rw [ha.keep.rd,ha.keep.wr,ha.keep.gpr .x1 (by simp)]
    exact hw j hj
  · rw [WP.block_append_iff]
    refine WP.mono (loadLast_ok ?_) fun c ⟨hc,hmc,hlc⟩ => ?_
    · rw [hb.keep.rd,hb.keep.wr,hb.keep.gpr .x1 (by simp),ha.keep.rd,ha.keep.wr,
        ha.keep.gpr .x1 (by simp)]
      exact hl
    · refine WP.mono (zeroCapacity_ok c) fun t ht => ?_
      refine ⟨(((ha.keep.trans hb.keep).trans hc).trans ht.keep).mono (by simp),
        ht.mem.trans (hmc.trans (hb.mem.trans ha.mem)),?_⟩
      intro i hi
      rw [ht.lanes i hi,hlc i hi,hb.lanes i hi,ha.lanes i hi,hb.mem,ha.mem,
        hb.keep.gpr .x1 (by simp),ha.keep.gpr .x1 (by simp)]
      simp only [firstState,Vector.getElem_ofFn,Nat.zero_add,Nat.sub_zero]
      by_cases h8 : i<8
      · rw [ite_eq_right (by omega : ¬ (17≤i ∧ i<17+8)),
          ite_eq_right (by omega : ¬ i=16),
          ite_eq_right (by omega : ¬ (8≤i ∧ i<8+2*4)),
          ite_eq_left (by omega : 0≤i ∧ i<2*4),ite_eq_left h8]
      · by_cases h16 : i<16
        · rw [ite_eq_right (by omega : ¬ (17≤i ∧ i<17+8)),
            ite_eq_right (by omega : ¬ i=16),
            ite_eq_left (by omega : 8≤i ∧ i<8+2*4),ite_eq_right h8,
            ite_eq_left (by omega : i<17)]
        · by_cases he : i=16
          · subst i
            rw [ite_eq_right (by decide : ¬ (17≤16 ∧ 16<17+8)),ite_eq_left rfl,
              ite_eq_right (by decide : ¬ (16:Nat)<8),ite_eq_left (by decide : (16:Nat)<17)]
            rfl
          · rw [ite_eq_left (by omega : 17≤i ∧ i<17+8),ite_eq_right h8,
              ite_eq_right (by omega : ¬ i<17)]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
