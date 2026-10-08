import VerifiedGarbage.Proof.Seed.AArch64.KeyBody
import VerifiedGarbage.Proof.Seed.AArch64.Ecb

/-!
# Key expansion on AArch64

`expandKey_ok`: after saving the callee-saved registers, `expandKey` loads
the key, computes the schedule (`keyBody_ok`) and restores the registers.
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Impl.Aes.AArch64
  VG.Proof.Seed

/-- What key expansion needs: the scratch buffer and the schedule writable,
the key readable, apart from each other. -/
structure KeyPre (s : State) : Prop where
  scratch : (⟨s.gpr .x2, 8 * scratchSlots⟩ : Region) ∈ s.wr
  schedIn : (⟨s.gpr .x1, 128⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .x0, 16⟩ : Region) ∈ s.rd
  keySched : (⟨s.gpr .x0, 16⟩ : Region).Disjoint ⟨s.gpr .x1, 128⟩
  keyBuf : (⟨s.gpr .x0, 16⟩ : Region).Disjoint ⟨s.gpr .x2, 8 * scratchSlots⟩
  schedBuf : (⟨s.gpr .x1, 128⟩ : Region).Disjoint ⟨s.gpr .x2, 8 * scratchSlots⟩

structure KeyPost (s s' : State) : Prop where
  saved : ∀ p ∈ Impl.Seed.AArch64.savedRegs, s'.gpr p.1 = s.gpr p.1
  sched : Spec.Seed.scheduleAt s'.mem (s.gpr .x1) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .x0))
  frame : Frame [⟨s.gpr .x2, 8 * scratchSlots⟩, ⟨s.gpr .x1, 128⟩] s.mem s'.mem

theorem expandKey_eq_code : expandKey = .block (([movR .x5 .x2] ++
    (Impl.Seed.AArch64.savedRegs.map fun p => (p.2, p.1)).map (fun p => stS p.1 p.2)) ++
    (keyLoad2 .x3 0 ++ keyLoad2 .x4 8) ++ keyBody ++ restore) := by
  simp only [expandKey, keyBody, Impl.Seed.AArch64.keyLoad, List.append_assoc]
  rfl

theorem expandKey_ok {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let key := Spec.Seed.blockAt s.mem (s.gpr .x0)
  rw [expandKey_eq_code]
  -- `x5 := x2`
  let s₁ := s.write .x .x5 (s.gpr .x2)
  have e₁ : runBlock isa [movR .x5 .x2] s = some s₁ := by
    rw [runBlock_cons, exec_movR, runStep_some, runBlock_nil]
  have r9₁ : s₁.gpr .x5 = s.gpr .x2 := by simp [s₁, gpr_write]
  have g₁ : ∀ r, r ≠ .x5 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  have scr₁ : scratchR s₁ = ⟨s.gpr .x2, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  have room₁ : Room s₁ := by unfold Room; rw [scr₁]; exact h.scratch
  -- the saved registers
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, -, f₂, set₂, -⟩ := stores_ok room₁
    (Impl.Seed.AArch64.savedRegs.map fun p => (p.2, p.1)) (by decide) (by decide)
  have G₂ : ∀ r, r ≠ .x5 → s₂.gpr r = s.gpr r := fun r a => by rw [g₂, g₁ r a]
  have r9₂ : s₂.gpr .x5 = s.gpr .x2 := by rw [g₂, r9₁]
  have f₂' : Frame [⟨s.gpr .x2, 8 * scratchSlots⟩] s.mem s₂.mem := by rw [← scr₁]; exact f₂
  have rd₂' : s₂.rd = s.rd := by rw [rd₂]; rfl
  have wr₂' : s₂.wr = s.wr := by rw [wr₂]; rfl
  -- the key
  have x0₂ : s₂.gpr .x0 = s.gpr .x0 := G₂ _ (by decide)
  have hkey : ∀ k, k + 4 ≤ 16 → InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 k) 4 := fun k hk => by
    rw [rd₂', wr₂', x0₂]
    exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨s₃, e₃, v₃, g₃, m₃, rd₃, wr₃, -⟩ := keyLoad2_ok (s := s₂) (d := .x3) (by decide) (k := 0) (by decide)
    (by decide) (hkey 0 (by decide)) (hkey 4 (by decide))
  have x0₃ : s₃.gpr .x0 = s.gpr .x0 := by rw [g₃ _ (by decide) (by decide), x0₂]
  obtain ⟨s₄, e₄, v₄, g₄, m₄, rd₄, wr₄, -⟩ := keyLoad2_ok (s := s₃) (d := .x4) (by decide) (k := 8) (by decide)
    (by decide)
    (by rw [rd₃, wr₃, x0₃, ← x0₂]; exact hkey 8 (by decide))
    (by rw [rd₃, wr₃, x0₃, ← x0₂]; exact hkey 12 (by decide))
  have key₂ : Spec.Seed.blockAt s₂.mem (s.gpr .x0) = key := blockAt_frame f₂' fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf
  have G₄ : ∀ r, r ≠ .x14 → r ≠ .x3 → r ≠ .x4 → s₄.gpr r = s₂.gpr r := fun r a b c => by
    rw [g₄ r a c, g₃ r a b]
  have h3 : s₄.gpr .x3 = kx (keyWords key 0) := by
    rw [g₄ _ (by decide) (by decide), v₃, x0₂, key₂]; rfl
  have h4 : s₄.gpr .x4 = ky (keyWords key 0) := by
    rw [v₄, x0₃, m₃, key₂]; rfl
  have r9₄ : s₄.gpr .x5 = s.gpr .x2 := by rw [G₄ _ (by decide) (by decide) (by decide), r9₂]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂']
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂']
  have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  have scr₄ : scratchR s₄ = ⟨s.gpr .x2, 8 * scratchSlots⟩ := by simp only [scratchR, r9₄]
  have room₄ : Room s₄ := by unfold Room; rw [scr₄, wr₄']; exact h.scratch
  have x1₄ : s₄.gpr .x1 = s.gpr .x1 := by rw [G₄ _ (by decide) (by decide) (by decide), G₂ _ (by decide)]
  -- the schedule
  obtain ⟨s₆, e₆, v₆, g₆, rd₆, wr₆, f₆⟩ := keyBody_ok key room₄ h3 h4
    (by rw [x1₄, wr₄']; exact h.schedIn) (by rw [x1₄, scr₄]; exact h.schedBuf)
  have r9₆ : s₆.gpr .x5 = s₄.gpr .x5 := g₆ _ (by simp)
  have room₆ : Room s₆ := room_congr room₄ r9₆ wr₆
  obtain ⟨s', e', m', -, set', -⟩ := loads_ok room₆ Impl.Seed.AArch64.savedRegs
    (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
  refine WP.of_runBlock ⟨s', runBlock_trans (runBlock_trans (runBlock_trans
    (runBlock_trans e₁ e₂) (runBlock_trans e₃ e₄)) e₆) (by rw [restore_eq]; exact e'), ?_⟩
  rw [x1₄] at v₆ f₆
  have workR₄ : workR s₄ = ⟨s.gpr .x2, 8 * 112⟩ := by simp only [workR, r9₄]
  rw [workR₄] at f₆
  have frame : Frame [⟨s.gpr .x2, 8 * scratchSlots⟩, ⟨s.gpr .x1, 128⟩] s.mem s'.mem := by
    rw [m']
    refine (f₂'.mono (by simp)).trans ?_
    rw [← mem₄]
    refine f₆.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by unfold scratchSlots; omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  refine ⟨fun q hq => ?_, ?_, frame⟩
  · have hq' := savedRegs_ok q hq
    rw [set' q hq]
    have e6 : slotW s₆ q.2 = slotW s₄ q.2 := by
      show s₆.mem.readW (Straight.wordAddr (s₆.gpr .x5) q.2) 64 =
        s₄.mem.readW (Straight.wordAddr (s₄.gpr .x5) q.2) 64
      rw [r9₆, r9₄]
      refine f₆.readW (r := ⟨Straight.wordAddr (s.gpr .x2) q.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by omega) (by unfold scratchSlots at hq'; omega)
      · exact (h.schedBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots at hq' ⊢; omega))).symm
    have e4 : slotW s₄ q.2 = slotW s₂ q.2 := by
      show s₄.mem.readW (Straight.wordAddr (s₄.gpr .x5) q.2) 64 =
        s₂.mem.readW (Straight.wordAddr (s₂.gpr .x5) q.2) 64
      rw [mem₄, r9₄, r9₂]
    rw [e6, e4, set₂ (q.2, q.1) (List.mem_map_of_mem hq), g₁ _ hq'.2.1]
  · rw [Proof.Seed.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [scheduleAt_readW _ _ i hi, m', v₆ i hi, Vector.getElem_ofFn]

end VG.Proof.Seed.AArch64
