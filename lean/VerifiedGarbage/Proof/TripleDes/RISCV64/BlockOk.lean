module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Block
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bytes
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.RISCV64.Consts

/-! # A block, from start to end -/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.TripleDes.RISCV64
open VG.Spec.TripleDes (Direction Schedule)

theorem saved_region (B : Addr) : ∀ p ∈ savedSlots,
    Region.Sub ⟨B + BitVec.ofNat 64 p.2, 8⟩ ⟨B + BitVec.ofNat 64 56, 48⟩ := by
  intro p hp
  have := savedSlots_in p hp
  exact Offset.sub B this.1 (by omega)

theorem roundConsts_length : roundConsts.length = 55 := by
  rw [roundConsts.lit_eq]; decide +kernel

theorem block_ok (k : Schedule) (d : Direction) (dp : Reg) (doff : Nat) (s : State)
    (hp : BlockPre k dp doff s) :
    WP isa (block d dp doff) s (BlockPost k d dp doff s) := by
  have hdpK : dp ∈ blockKept := by have := hp.dpKept; revert this; cases dp <;> decide
  have hdpT : dp ≠ .t0 ∧ dp ≠ .t1 := by have := hp.dpKept; revert this; cases dp <;> decide
  let B := s.gpr sb
  let q := s.gpr dp + BitVec.ofNat 64 doff
  have hsub56 : Region.Sub ⟨B + BitVec.ofNat 64 56, 48⟩ (workRegion s) :=
    Offset.sub B (by decide) (by decide)
  have hsubC : Region.Sub ⟨B + BitVec.ofNat 64 constOff, 8 * roundConsts.length⟩ (workRegion s) := by
    rw [roundConsts_length]; exact Offset.sub B (by decide) (by decide)
  have hin_slot : ∀ p ∈ savedSlots, InRegions s.wr (B + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    have h := savedSlots_in p hp'
    have h8 : p.2 % 8 = 0 := (savedSlots_fits.1 p hp').1
    have := hp.wr (p.2 / 8) (by omega)
    rwa [show 8 * (p.2 / 8) = p.2 by omega] at this
  apply WP.seq
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Spill.save_wp (b := sb) hp.al savedSlots_fits.1 hin_slot) fun s₀ hs₀ => ?_
  have hg₀ : ∀ r, s₀.gpr r = s.gpr r := fun r => by rw [hs₀.gpr]
  refine storeConsts_wp roundConsts constOff s₀ _ (by rw [hg₀]; exact hp.al) (by decide)
    (by rw [roundConsts_length]; decide) (fun c hc => by
      rw [hs₀.wr, hg₀]
      have := hp.wr (15 + c) (by rw [roundConsts_length] at hc; omega)
      rwa [show 8 * (15 + c) = constOff + 8 * c by simp only [constOff]; omega] at this)
    fun s₁ hm₁ hrd₁ hwr₁ hsp₁ hg₁' => ?_
  have hg₁ : ∀ r, r ≠ .t0 → r ≠ .t1 → s₁.gpr r = s.gpr r := fun r h0 h1 =>
    (hg₁' r h0 h1).trans (hg₀ r)
  have hB₁ : s₁.gpr sb = B := hg₁ sb (by decide) (by decide)
  have hframe₁ : Frame [workRegion s] s.mem s₁.mem := by
    have f₀ : Frame [workRegion s] s.mem s₀.mem := by
      rw [hs₀.mem]
      exact (Spill.saveMem_frame savedSlots_in (by decide) _ _ _).sub fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, List.mem_singleton_self _, hsub56⟩
    have f₁ : Frame [workRegion s] s₀.mem s₁.mem := by
      rw [hm₁, hg₀]
      exact (constMem_frame B roundConsts s₀.mem constOff (by rw [roundConsts_length]; decide)).sub
        fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact ⟨_, List.mem_singleton_self _, hsubC⟩
    exact f₀.trans f₁
  have hconsts₁ : ConstsAt s₁ := by
    intro c hc
    rw [hm₁, hB₁, hg₀]
    have h := constMem_read B roundConsts s₀.mem constOff
      (by rw [roundConsts_length]; decide) c (by rw [roundConsts_length]; exact hc)
    simp only [Straight.wordAddr]
    rw [show 8 * (15 + c) = constOff + 8 * c by simp only [constOff]; omega]
    exact h
  have hdata₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr dp + BitVec.ofNat 64 doff) 8 := by
    rw [hrd₁, hwr₁, hs₀.rd, hs₀.wr, hg₁ dp hdpT.1 hdpT.2]
    obtain ⟨r, hr, hc⟩ := hp.data
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (blockLoad_ok dp doff hp.dpKept (by have := hp.doffLt; omega) s₁ hdata₁)
    fun t₁ ⟨hw₁, hmt₁, hrdt₁, hwrt₁, hspt₁, hk₁⟩ => ?_
  have hBt₁ : t₁.gpr sb = B := (hk₁ sb (by decide)).trans hB₁
  have hblock₁ : Spec.TripleDes.blockAt s₁.mem (s₁.gpr dp + BitVec.ofNat 64 doff) =
      Spec.TripleDes.blockAt s.mem q := by
    rw [hg₁ dp hdpT.1 hdpT.2]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hframe₁
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hp.sep)
  rw [hblock₁] at hw₁
  have hready₁ : Ready (Spec.TripleDes.componentSchedule k) (B + BitVec.ofNat 64 keyOff) t₁ := by
    have hr := ready_of (s := t₁) (k := k) (by rw [hBt₁]; exact hp.al)
      (by rw [hwrt₁, hwr₁, hs₀.wr, hBt₁]; exact hp.wr) (by
        rw [hBt₁, hmt₁, VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hframe₁ (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint B (Or.inr (by decide)) (by decide) (by decide))]
        exact hp.keys)
      (fun c hc => by rw [hmt₁, hBt₁, ← hB₁]; exact hconsts₁ c hc)
    rwa [hBt₁] at hr
  have hsaved₁ : Spill.Saved B s.gpr savedSlots t₁.mem := by
    have h₀ : Spill.Saved B s.gpr savedSlots s₀.mem := by
      rw [hs₀.mem]; exact Spill.saveMem_saved savedSlots_fits s.mem B s.gpr
    rw [hmt₁, hm₁, hg₀]
    exact h₀.frame_in savedSlots_in
      (constMem_frame B roundConsts s₀.mem constOff (by rw [roundConsts_length]; decide))
      (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        rw [roundConsts_length]
        exact Offset.disjoint B (Or.inl (by decide)) (by decide) (by decide))
  apply WP.seq
  refine WP.mono (blockBody_ok _ _ t₁ _ d hready₁ hw₁) fun t₂ ⟨hw₂, _, hst₂⟩ => ?_
  have hB₂ : t₂.gpr sb = B := (hst₂.regs sb (by decide)).trans hBt₁
  have hdp₂ : t₂.gpr dp = s.gpr dp :=
    (hst₂.regs dp hp.dpKept).trans ((hk₁ dp hdpK).trans (hg₁ dp hdpT.1 hdpT.2))
  rw [WP.block_append_iff]
  refine WP.mono (blockStore_ok dp doff hp.dpKept hp.doffLt t₂ _ hw₂ (by
      rw [hst₂.wr, hwrt₁, hwr₁, hs₀.wr, hdp₂]; exact hp.data))
    fun t₃ ⟨hm₃, hrd₃, hwr₃, hsp₃, hk₃⟩ => ?_
  rw [hdp₂] at hm₃
  have hB₃ : t₃.gpr sb = B := (hk₃ sb (by decide)).trans hB₂
  have hframe₃ : Frame [⟨q, 8⟩] t₂.mem t₃.mem := by rw [hm₃]; exact stored_frame _ _ _
  have hsaved₃ : Spill.Saved B s.gpr savedSlots t₃.mem := by
    have h₂ : Spill.Saved B s.gpr savedSlots t₂.mem := by rw [hst₂.mem]; exact hsaved₁
    exact h₂.frame_in savedSlots_in hframe₃ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (hp.sep.sub_right hsub56).symm)
  have hrd₃' : t₃.rd = s.rd := hrd₃.trans (hst₂.rd.trans (hrdt₁.trans (hrd₁.trans hs₀.rd)))
  have hwr₃' : t₃.wr = s.wr := hwr₃.trans (hst₂.wr.trans (hwrt₁.trans (hwr₁.trans hs₀.wr)))
  refine WP.mono (Spill.restore_wp hp.al hB₃ savedSlots_fits.1 savedSlots_restorable (fun p hp' => by
      rw [hrd₃', hwr₃']
      obtain ⟨r, hr, hc⟩ := hin_slot p hp'
      exact ⟨r, List.mem_append_right _ hr, hc⟩) hsaved₃) fun t₄ h₄ => ?_
  refine ⟨?_, fun r hr => ?_, h₄.rd.trans hrd₃', h₄.wr.trans hwr₃',
    h₄.sp.trans (hsp₃.trans (hst₂.sp.trans (hspt₁.trans (hsp₁.trans hs₀.sp)))), ?_⟩
  · rw [h₄.mem, hm₃, stored_block]
    exact blockResult_core k d _
  · by_cases hs : r ∈ savedSlots.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      exact h₄.gpr p hp'
    · have hpk : r ∈ passKept := by revert hr hs; cases r <;> decide
      have hrT : r ≠ .t0 ∧ r ≠ .t1 := by revert hr; cases r <;> decide
      rw [h₄.other r hs, hk₃ r hr, hst₂.regs r hpk, hk₁ r hr, hg₁ r hrT.1 hrT.2]
  · rw [h₄.mem]
    have f₁ := hframe₁.mono (rs' := [⟨q, 8⟩, workRegion s]) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have f₂ : Frame [⟨q, 8⟩, workRegion s] s₁.mem t₂.mem := by
      rw [hst₂.mem, hmt₁]; exact Frame.refl _ _
    have f₃ := hframe₃.mono (rs' := [⟨q, 8⟩, workRegion s]) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact List.mem_cons_self)
    exact f₁.trans (f₂.trans f₃)

end VG.Proof.TripleDes.RISCV64
