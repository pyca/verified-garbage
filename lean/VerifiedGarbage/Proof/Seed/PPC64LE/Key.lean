module

public import VerifiedGarbage.Proof.Seed.PPC64LE.KeyBody
import VerifiedGarbage.Proof.Seed.PPC64LE.Ecb
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Seed.PPC64LE.KeyLoad
import VerifiedGarbage.Proof.Seed.PPC64LE.Setup
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.SplitIfs

/-!
# Key expansion on PPC64LE

`expandKey_ok`: after saving the callee-saved registers, `expandKey` loads
the key, computes the schedule (`keyBody_ok`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Impl.Aes.PPC64LE
  VG.Proof.Seed

/-- What key expansion needs: the scratch buffer and the schedule writable,
the key readable, apart from each other. -/
structure KeyPre (s : State) : Prop where
  scratch : (⟨s.gpr .r5, 8 * scratchSlots⟩ : Region) ∈ s.wr
  schedIn : (⟨s.gpr .r4, 128⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .r3, 16⟩ : Region) ∈ s.rd
  keySched : (⟨s.gpr .r3, 16⟩ : Region).Disjoint ⟨s.gpr .r4, 128⟩
  keyBuf : (⟨s.gpr .r3, 16⟩ : Region).Disjoint ⟨s.gpr .r5, 8 * scratchSlots⟩
  schedBuf : (⟨s.gpr .r4, 128⟩ : Region).Disjoint ⟨s.gpr .r5, 8 * scratchSlots⟩

structure KeyPost (s s' : State) : Prop where
  saved : ∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s'.gpr p.1 = s.gpr p.1
  sched : Spec.Seed.scheduleAt s'.mem (s.gpr .r4) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .r3))
  frame : Frame [⟨s.gpr .r5, 8 * scratchSlots⟩, ⟨s.gpr .r4, 128⟩] s.mem s'.mem

theorem expandKey_eq_code : expandKey = .seq (.block (([movR .r8 .r5] ++
    (Impl.Seed.PPC64LE.savedRegs.map fun p => (p.2, p.1)).map (fun p => stS p.1 p.2)) ++
    (keyLoad2 .r6 0 ++ keyLoad2 .r7 8) ++ keyPre)) (.seq (.loop keyHalf (.nonzero .d .r6)) (.block restore)) := by
  simp only [expandKey, keyPre, Impl.Seed.PPC64LE.keyLoad, List.append_assoc]
  rfl

theorem expandKey_ok {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let key := Spec.Seed.blockAt s.mem (s.gpr .r3)
  rw [expandKey_eq_code]
  -- `r8 := r5`
  let s₁ := s.write .r8 (s.gpr .r5)
  have e₁ : runBlock isa [movR .r8 .r5] s = some s₁ := by
    rw [runBlock_cons, exec_movR, runStep_some, runBlock_nil]
  have r9₁ : s₁.gpr .r8 = s.gpr .r5 := by simp [s₁, gpr_write]
  have g₁ : ∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  have scr₁ : scratchR s₁ = ⟨s.gpr .r5, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  have room₁ : Room s₁ := .of_mem (by rw [scr₁]; exact h.scratch)
  -- the saved registers
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, -, f₂, set₂, -⟩ := stores_ok room₁
    (Impl.Seed.PPC64LE.savedRegs.map fun p => (p.2, p.1)) (by decide) (by decide)
  have G₂ : ∀ r, r ≠ .r8 → s₂.gpr r = s.gpr r := fun r a => by rw [g₂, g₁ r a]
  have r9₂ : s₂.gpr .r8 = s.gpr .r5 := by rw [g₂, r9₁]
  have f₂' : Frame [⟨s.gpr .r5, 8 * scratchSlots⟩] s.mem s₂.mem := by rw [← scr₁]; exact f₂
  have rd₂' : s₂.rd = s.rd := by rw [rd₂]; rfl
  have wr₂' : s₂.wr = s.wr := by rw [wr₂]; rfl
  -- the key
  have r3₂ : s₂.gpr .r3 = s.gpr .r3 := G₂ _ (by decide)
  have hkey : ∀ k, k + 4 ≤ 16 → InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r3 + BitVec.ofNat 64 k) 4 := fun k hk => by
    rw [rd₂', wr₂', r3₂]
    exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨s₃, e₃, v₃, g₃, m₃, rd₃, wr₃, -⟩ := keyLoad2_ok (s := s₂) (d := .r6) (by decide) (by decide) (k := 0) (by decide)
    (by decide) (hkey 0 (by decide)) (hkey 4 (by decide))
  have r3₃ : s₃.gpr .r3 = s.gpr .r3 := by rw [g₃ _ (by decide) (by decide), r3₂]
  obtain ⟨s₄, e₄, v₄, g₄, m₄, rd₄, wr₄, -⟩ := keyLoad2_ok (s := s₃) (d := .r7) (by decide) (by decide) (k := 8) (by decide)
    (by decide)
    (by rw [rd₃, wr₃, r3₃, ← r3₂]; exact hkey 8 (by decide))
    (by rw [rd₃, wr₃, r3₃, ← r3₂]; exact hkey 12 (by decide))
  have key₂ : Spec.Seed.blockAt s₂.mem (s.gpr .r3) = key := blockAt_frame f₂' fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf
  have G₄ : ∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r7 → s₄.gpr r = s₂.gpr r := fun r a b c => by
    rw [g₄ r a c, g₃ r a b]
  have h3 : s₄.gpr .r6 = kx (keyWords key 0) := by
    rw [g₄ _ (by decide) (by decide), v₃, r3₂, key₂]; rfl
  have h4 : s₄.gpr .r7 = ky (keyWords key 0) := by
    rw [v₄, r3₃, m₃, key₂]; rfl
  have r9₄ : s₄.gpr .r8 = s.gpr .r5 := by rw [G₄ _ (by decide) (by decide) (by decide), r9₂]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂']
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂']
  have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  have scr₄ : scratchR s₄ = ⟨s.gpr .r5, 8 * scratchSlots⟩ := by simp only [scratchR, r9₄]
  have room₄ : Room s₄ := .of_mem (by rw [scr₄, wr₄']; exact h.scratch)
  have r4₄ : s₄.gpr .r4 = s.gpr .r4 := by rw [G₄ _ (by decide) (by decide) (by decide), G₂ _ (by decide)]
  -- the rounds, and the count of halves
  obtain ⟨s₅, e₅, room₅, cur₅, next₅, r6₅, g₅, rd₅, wr₅, f₅⟩ := keyPre_ok key room₄ h3 h4
  have r9₅ : s₅.gpr .r8 = s₄.gpr .r8 := g₅ _ (by simp)
  have r4₅ : s₅.gpr .r4 = s.gpr .r4 := (g₅ _ (by simp)).trans r4₄
  have scr₅ : scratchR s₅ = ⟨s.gpr .r5, 8 * scratchSlots⟩ := by simp only [scratchR, r9₅, r9₄]
  have h0 : HalfInv key s₅ (s.gpr .r4) 0 s₅ :=
    ⟨room₅, rfl, by rw [r4₅]; exact (BitVec.add_zero _).symm, r6₅,
      fun w hw => by rw [cur₅ w hw, Nat.mul_zero, Nat.zero_add], fun _ => next₅, fun i hi => by omega, rfl, rfl,
      Frame.refl _ _⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, runBlock_trans (runBlock_trans (runBlock_trans e₁ e₂)
    (runBlock_trans e₃ e₄)) e₅, WP.seq (keyHalves_wp key
      (by rw [wr₅, wr₄']; exact h.schedIn) (by rw [scr₅]; exact h.schedBuf) h0
      fun s₆ v₆ r9₆ rd₆ wr₆ f₆ => ?_)⟩)
  have room₆ : Room s₆ := room_congr room₅ r9₆ wr₆
  obtain ⟨s', e', m', -, set', -⟩ := loads_ok room₆ Impl.Seed.PPC64LE.savedRegs
    (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
  refine WP.of_runBlock ⟨s', by rw [restore_eq]; exact e', ?_⟩
  have workR₅ : workR s₅ = ⟨s.gpr .r5, 8 * 112⟩ := by simp only [workR, r9₅, r9₄]
  rw [workR₅] at f₆
  have arr₄ : Region.Sub (arraysR s₄) ⟨s.gpr .r5, 8 * 112⟩ := by
    have := arraysR_sub_work s₄; simp only [workR, r9₄] at this; exact this
  have f₄₆ : Frame [⟨s.gpr .r5, 8 * 112⟩, ⟨s.gpr .r4, 128⟩] s₄.mem s₆.mem :=
    (f₅.sub fun r hr => ⟨_, List.mem_cons_self, by simp at hr; subst hr; exact arr₄⟩).trans f₆
  have frame : Frame [⟨s.gpr .r5, 8 * scratchSlots⟩, ⟨s.gpr .r4, 128⟩] s.mem s'.mem := by
    rw [m']
    refine (f₂'.mono (by simp)).trans ?_
    rw [← mem₄]
    refine f₄₆.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by unfold scratchSlots; omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  refine ⟨fun q hq => ?_, ?_, frame⟩
  · have hq' := savedRegs_ok q hq
    rw [set' q hq]
    have e6 : slotW s₆ q.2 = slotW s₄ q.2 := by
      show s₆.mem.readW (StraightK.wordAddr (s₆.gpr .r8) q.2) 64 =
        s₄.mem.readW (StraightK.wordAddr (s₄.gpr .r8) q.2) 64
      rw [r9₆, r9₅, r9₄]
      refine f₄₆.readW (r := ⟨StraightK.wordAddr (s.gpr .r5) q.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by omega) (by unfold scratchSlots at hq'; omega)
      · exact (h.schedBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots at hq' ⊢; omega))).symm
    have e4 : slotW s₄ q.2 = slotW s₂ q.2 := by
      show s₄.mem.readW (StraightK.wordAddr (s₄.gpr .r8) q.2) 64 =
        s₂.mem.readW (StraightK.wordAddr (s₂.gpr .r8) q.2) 64
      rw [mem₄, r9₄, r9₂]
    rw [e6, e4, set₂ (q.2, q.1) (List.mem_map_of_mem hq), g₁ _ hq'.2.1]
  · rw [Proof.Seed.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [scheduleAt_readW _ _ i hi, m', v₆ i hi, Vector.getElem_ofFn]

end VG.Proof.Seed.PPC64LE
