module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Block
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bytes
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # A block, from start to end -/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.TripleDes.RISCV64
open VG.Spec.TripleDes (Direction Schedule)

theorem saved_region (B : Addr) : ∀ p ∈ savedSlots,
    Region.Sub ⟨B + BitVec.ofNat 64 p.2, 8⟩ ⟨B + BitVec.ofNat 64 56, 64⟩ := by
  intro p hp
  have := savedSlots_in p hp
  exact Offset.sub B this.1 (by omega)

theorem block_ok (k : Schedule) (d : Direction) (dp : Reg) (doff : Nat) (s : State)
    (hp : BlockPre k dp doff s) :
    WP isa (block d dp doff) s (BlockPost k d dp doff s) := by
  have hdpK : dp ∈ blockKept := by have := hp.dpKept; revert this; cases dp <;> decide
  let B := s.gpr sb
  let q := s.gpr dp + BitVec.ofNat 64 doff
  have hsub56 : Region.Sub ⟨B + BitVec.ofNat 64 56, 64⟩ (workRegion s) :=
    Offset.sub B (by decide) (by decide)
  have hsubSp : Region.Sub ⟨B + BitVec.ofNat 64 120, 128⟩ (workRegion s) :=
    Offset.sub B (by decide) (by decide)
  have hdsep56 : (⟨q, 8⟩ : Region).Disjoint ⟨B + BitVec.ofNat 64 56, 64⟩ :=
    hp.sep.sub_right hsub56
  have hin_slot : ∀ p ∈ savedSlots, InRegions s.wr (B + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    have h := savedSlots_in p hp'
    have h8 : p.2 % 8 = 0 := (savedSlots_fits.1 p hp').1
    have := hp.wr (p.2 / 8) (by omega)
    rwa [show 8 * (p.2 / 8) = p.2 by omega] at this
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_wp (b := sb) hp.al savedSlots_fits.1 hin_slot) fun s₁ hs₁ => ?_
  have hframe₁ : Frame [⟨B + BitVec.ofNat 64 56, 64⟩] s.mem s₁.mem := by
    rw [hs₁.mem]
    exact Spill.saveMem_frame savedSlots_in (by decide) _ _ _
  have hg₁ : ∀ r, s₁.gpr r = s.gpr r := fun r => by rw [hs₁.gpr]
  have hdata₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr dp + BitVec.ofNat 64 doff) 8 := by
    rw [hs₁.rd, hs₁.wr, hg₁]
    obtain ⟨r, hr, hc⟩ := hp.data
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (blockLoad_ok dp doff hp.dpKept (by have := hp.doffLt; omega) s₁ hdata₁)
    fun t₁ ⟨hw₁, hm₁, hrd₁, hwr₁, hsp₁, hk₁⟩ => ?_
  have hB₁ : t₁.gpr sb = B := (hk₁ sb (by decide)).trans (hg₁ sb)
  have hblock₁ : Spec.TripleDes.blockAt s₁.mem (s₁.gpr dp + BitVec.ofNat 64 doff) =
      Spec.TripleDes.blockAt s.mem q := by
    rw [hg₁]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hframe₁
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hdsep56)
  rw [hblock₁] at hw₁
  have hready₁ : Ready (Spec.TripleDes.componentSchedule k) (B + BitVec.ofNat 64 keyOff) t₁ := by
    have hr := ready_of (s := t₁) (k := k) (by rw [hB₁]; exact hp.al)
      (by rw [hwr₁, hs₁.wr, hB₁]; exact hp.wr) (by
        rw [hB₁, hm₁, VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hframe₁ (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint B (Or.inr (by decide)) (by decide) (by decide))]
        exact hp.keys)
    rwa [hB₁] at hr
  have hsaved₁ : Spill.Saved B s.gpr savedSlots t₁.mem := by
    rw [hm₁, hs₁.mem]
    exact Spill.saveMem_saved savedSlots_fits s.mem B s.gpr
  apply WP.seq
  refine WP.mono (blockBody_ok _ _ t₁ _ d hready₁ hw₁) fun t₂ ⟨hw₂, _, hst₂⟩ => ?_
  have hB₂ : t₂.gpr sb = B := (hst₂.regs sb (by decide)).trans hB₁
  have hspill₂ : spillRegion t₁ = ⟨B + BitVec.ofNat 64 120, 128⟩ := by
    simp only [spillRegion, hB₁]
  have hframe₂ : Frame [⟨B + BitVec.ofNat 64 120, 128⟩] t₁.mem t₂.mem := by
    rw [← hspill₂]; exact hst₂.frame
  have hsaved₂ : Spill.Saved B s.gpr savedSlots t₂.mem :=
    hsaved₁.frame_in savedSlots_in hframe₂ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint B (Or.inl (by decide)) (by decide) (by decide))
  have hdp₂ : t₂.gpr dp = s.gpr dp :=
    (hst₂.regs dp hp.dpKept).trans ((hk₁ dp hdpK).trans (hg₁ dp))
  rw [WP.block_append_iff]
  refine WP.mono (blockStore_ok dp doff hp.dpKept hp.doffLt t₂ _ hw₂ (by
      rw [hst₂.wr, hwr₁, hs₁.wr, hdp₂]; exact hp.data))
    fun t₃ ⟨hm₃, hrd₃, hwr₃, hsp₃, hk₃⟩ => ?_
  rw [hdp₂] at hm₃
  have hB₃ : t₃.gpr sb = B := (hk₃ sb (by decide)).trans hB₂
  have hframe₃ : Frame [⟨q, 8⟩] t₂.mem t₃.mem := by rw [hm₃]; exact stored_frame _ _ _
  have hsaved₃ : Spill.Saved B s.gpr savedSlots t₃.mem :=
    hsaved₂.frame_in savedSlots_in hframe₃ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hdsep56.symm)
  have hrd₃' : t₃.rd = s.rd := hrd₃.trans (hst₂.rd.trans (hrd₁.trans hs₁.rd))
  have hwr₃' : t₃.wr = s.wr := hwr₃.trans (hst₂.wr.trans (hwr₁.trans hs₁.wr))
  refine WP.mono (Spill.restore_wp hp.al hB₃ savedSlots_fits.1 savedSlots_restorable (fun p hp' => by
      rw [hrd₃', hwr₃']
      obtain ⟨r, hr, hc⟩ := hin_slot p hp'
      exact ⟨r, List.mem_append_right _ hr, hc⟩) hsaved₃) fun t₄ h₄ => ?_
  refine ⟨?_, fun r hr => ?_, h₄.rd.trans hrd₃', h₄.wr.trans hwr₃',
    h₄.sp.trans (hsp₃.trans (hst₂.sp.trans (hsp₁.trans hs₁.sp))), ?_⟩
  · rw [h₄.mem, hm₃, stored_block]
    exact blockResult_core k d _
  · by_cases hs : r ∈ savedSlots.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      exact h₄.gpr p hp'
    · have hpk : r ∈ passKept := by revert hr hs; cases r <;> decide
      rw [h₄.other r hs, hk₃ r hr, hst₂.regs r hpk, hk₁ r hr, hg₁]
  · rw [h₄.mem]
    have f₁ := hframe₁.sub (rs' := [⟨q, 8⟩, workRegion s]) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hsub56⟩)
    have f₂ := hframe₂.sub (rs' := [⟨q, 8⟩, workRegion s]) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hsubSp⟩)
    have f₃ := hframe₃.mono (rs' := [⟨q, 8⟩, workRegion s]) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact List.mem_cons_self)
    rw [hm₁] at f₂
    exact f₁.trans (f₂.trans f₃)

end VG.Proof.TripleDes.RISCV64
