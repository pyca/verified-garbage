import VerifiedGarbage.Proof.Seed.X86_64.KeyBody
import VerifiedGarbage.Proof.Seed.X86_64.Ecb

/-!
# Key expansion on x86-64

`expandKey_ok`: after saving the callee-saved registers and writing the
masks, `expandKey` loads the key, computes the schedule (`keyBody_ok`) and
restores the registers.
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Impl.Aes.X86_64 VG.Proof.Seed

/-- What key expansion needs: the scratch buffer and the schedule writable,
the key readable, apart from each other and the return address. -/
structure KeyPre (s : State) : Prop where
  scratch : (⟨s.gpr .rdx, 8 * scratchSlots⟩ : Region) ∈ s.wr
  schedIn : (⟨s.gpr .rsi, 128⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .rdi, 16⟩ : Region) ∈ s.rd
  keySched : (⟨s.gpr .rdi, 16⟩ : Region).Disjoint ⟨s.gpr .rsi, 128⟩
  keyBuf : (⟨s.gpr .rdi, 16⟩ : Region).Disjoint ⟨s.gpr .rdx, 8 * scratchSlots⟩
  schedBuf : (⟨s.gpr .rsi, 128⟩ : Region).Disjoint ⟨s.gpr .rdx, 8 * scratchSlots⟩
  retSched : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 128⟩
  retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8 * scratchSlots⟩

structure KeyPost (s s' : State) : Prop where
  gpr : gprPreserved s s'
  sched : Spec.Seed.scheduleAt s'.mem (s.gpr .rsi) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .rdi))
  frame : Frame [⟨s.gpr .rdx, 8 * scratchSlots⟩, ⟨s.gpr .rsi, 128⟩] s.mem s'.mem

theorem expandKey_eq_code : expandKey = .block (([movR .r9 .rdx] ++
    (Impl.Seed.X86_64.savedRegs.map fun p => (p.2, p.1)).map (fun p => st p.1 p.2) ++ setG16Masks) ++
    Impl.Seed.X86_64.keyLoad ++ keyBody ++ restore) := by
  simp only [expandKey, keyBody, List.append_assoc]
  rfl

theorem expandKey_ok {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let key := Spec.Seed.blockAt s.mem (s.gpr .rdi)
  rw [expandKey_eq_code]
  -- `r9 := rdx`
  let s₁ := s.setReg .r9 (s.gpr .rdx)
  have e₁ : runBlock isa [movR .r9 .rdx] s = some s₁ := rfl
  have r9₁ : s₁.gpr .r9 = s.gpr .rdx := gpr_setReg_self (s := s) _ _
  have g₁ : ∀ r, r ≠ .r9 → s₁.gpr r = s.gpr r := fun r hr => gpr_setReg_of_ne (s := s) _ hr
  have scr₁ : scratchR s₁ = ⟨s.gpr .rdx, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  have room₁ : Room s₁ := by unfold Room; rw [scr₁]; exact h.scratch
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, f₂, set₂, keep₂⟩ := stores_ok room₁
    (Impl.Seed.X86_64.savedRegs.map fun p => (p.2, p.1)) (by decide) (by decide)
  have room₂ : Room s₂ := room_congr room₁ (by rw [g₂]) wr₂
  obtain ⟨s₃, e₃, g₃, rd₃, wr₃, f₃, set₃, keep₃⟩ := masks_ok room₂ maskSlots (by decide) (by decide)
  have G₃ : ∀ r, r ≠ .r9 → r ≠ t0 → s₃.gpr r = s.gpr r := fun r a b => by rw [g₃ r b, g₂, g₁ r a]
  have r9₃ : s₃.gpr .r9 = s.gpr .rdx := by rw [g₃ _ (by decide), g₂, r9₁]
  have f₃' : Frame [⟨s.gpr .rdx, 8 * scratchSlots⟩] s.mem s₃.mem := by
    rw [← scr₁]
    refine f₂.trans ?_
    have : scratchR s₂ = scratchR s₁ := by simp only [scratchR, g₂]
    rw [← this]; exact f₃
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂]; rfl
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂]; rfl
  have room₃ : Room s₃ := by unfold Room; rw [scratchR, r9₃, wr₃']; exact h.scratch
  -- the key
  have rdi₃ : s₃.gpr .rdi = s.gpr .rdi := G₃ _ (by decide) (by decide)
  have hkey : ∀ k, k + 4 ≤ 16 → InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .rdi + BitVec.ofNat 64 k) 4 := fun k hk => by
    rw [rd₃', wr₃', rdi₃]
    exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨s₄, e₄, v₄, g₄, m₄, rd₄, wr₄⟩ := keyLoad2_ok (s := s₃) (d := .r10) (by decide) (k := 0) (by decide)
    (hkey 0 (by decide)) (hkey 4 (by decide))
  have rdi₄ : s₄.gpr .rdi = s.gpr .rdi := by rw [g₄ _ (by decide) (by decide), rdi₃]
  obtain ⟨s₅, e₅, v₅, g₅, m₅, rd₅, wr₅⟩ := keyLoad2_ok (s := s₄) (d := .r11) (by decide) (k := 8) (by decide)
    (by rw [rd₄, wr₄, rdi₄, ← rdi₃]; exact hkey 8 (by decide))
    (by rw [rd₄, wr₄, rdi₄, ← rdi₃]; exact hkey 12 (by decide))
  have key₃ : Spec.Seed.blockAt s₃.mem (s.gpr .rdi) = key := blockAt_frame f₃' fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf
  have G₅ : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s₅.gpr r = s₃.gpr r := fun r a b c => by
    rw [g₅ r a c, g₄ r a b]
  have h10 : s₅.gpr .r10 = kx (keyWords key 0) := by
    rw [g₅ _ (by decide) (by decide), v₄, rdi₃, key₃]; rfl
  have h11 : s₅.gpr .r11 = ky (keyWords key 0) := by
    rw [v₅, rdi₄, m₄, key₃]; rfl
  have r9₅ : s₅.gpr .r9 = s.gpr .rdx := by rw [G₅ _ (by decide) (by decide) (by decide), r9₃]
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, rd₄, rd₃']
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, wr₄, wr₃']
  have mem₅ : s₅.mem = s₃.mem := by rw [m₅, m₄]
  have scr₅ : scratchR s₅ = ⟨s.gpr .rdx, 8 * scratchSlots⟩ := by simp only [scratchR, r9₅]
  have room₅ : Room s₅ := by unfold Room; rw [scr₅, wr₅']; exact h.scratch
  have masks₅ : MasksIn s₅ := fun kv hkv => by
    rw [← set₃ kv hkv]
    show s₅.mem.readW (Straight.wordAddr (s₅.gpr .r9) kv.1) 64 = s₃.mem.readW (Straight.wordAddr (s₃.gpr .r9) kv.1) 64
    rw [mem₅, r9₅, r9₃]
  have rsi₅ : s₅.gpr .rsi = s.gpr .rsi := by rw [G₅ _ (by decide) (by decide) (by decide), G₃ _ (by decide) (by decide)]
  -- the schedule
  obtain ⟨s₆, e₆, v₆, g₆, rd₆, wr₆, f₆⟩ := keyBody_ok key room₅ masks₅ h10 h11
    (by rw [rsi₅, wr₅']; exact h.schedIn) (by rw [rsi₅, scr₅]; exact h.schedBuf)
  have r9₆ : s₆.gpr .r9 = s₅.gpr .r9 := g₆ _ (by simp)
  have room₆ : Room s₆ := room_congr room₅ r9₆ wr₆
  obtain ⟨s', e', m', set', keep'⟩ := loads_ok room₆ Impl.Seed.X86_64.savedRegs
    (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
  refine WP.of_runBlock ⟨s', runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans
    (runBlock_trans e₁ e₂) e₃) (runBlock_trans e₄ e₅)) e₆) (by rw [restore_eq]; exact e'), ?_⟩
  rw [rsi₅] at v₆ f₆
  have workR₅ : workR s₅ = ⟨s.gpr .rdx, 8 * 125⟩ := by simp only [workR, r9₅]
  rw [workR₅] at f₆
  have frame : Frame [⟨s.gpr .rdx, 8 * scratchSlots⟩, ⟨s.gpr .rsi, 128⟩] s.mem s'.mem := by
    rw [m']
    refine (f₃'.mono (by simp)).trans ?_
    rw [← mem₅]
    refine f₆.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by unfold scratchSlots; omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, frame⟩
  · have saved : ∀ q ∈ Impl.Seed.X86_64.savedRegs, s'.gpr q.1 = s.gpr q.1 := by
      intro q hq
      have hq' := savedRegs_ok q hq
      rw [set' q hq]
      have e6 : slotW s₆ q.2 = slotW s₅ q.2 := by
        show s₆.mem.readW (Straight.wordAddr (s₆.gpr .r9) q.2) 64 =
          s₅.mem.readW (Straight.wordAddr (s₅.gpr .r9) q.2) 64
        rw [r9₆, r9₅]
        refine f₆.readW (r := ⟨Straight.wordAddr (s.gpr .rdx) q.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint_base _ (by omega) (by unfold scratchSlots at hq'; omega)
        · exact (h.schedBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots at hq' ⊢; omega))).symm
      have e5 : slotW s₅ q.2 = slotW s₃ q.2 := by
        show s₅.mem.readW (Straight.wordAddr (s₅.gpr .r9) q.2) 64 =
          s₃.mem.readW (Straight.wordAddr (s₃.gpr .r9) q.2) 64
        rw [mem₅, r9₅, r9₃]
      rw [e6, e5, keep₃ _ hq'.1 (fun p hp => by have := maskSlots_lt p hp; omega),
        set₂ (q.2, q.1) (List.mem_map_of_mem hq), g₁ _ hq'.2.1]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact saved (.rbx, 125) (by decide)
    · exact saved (.rbp, 126) (by decide)
    · rw [keep' .rsp (by decide), g₆ _ (by simp), G₅ _ (by decide) (by decide) (by decide),
        G₃ _ (by decide) (by decide)]
    · exact saved (.r12, 127) (by decide)
    · exact saved (.r13, 128) (by decide)
    · exact saved (.r14, 129) (by decide)
    · exact saved (.r15, 130) (by decide)
  · refine frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.retBuf
    · exact h.retSched
  · rw [Proof.Seed.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [scheduleAt_readW _ _ i hi, m', v₆ i hi, Vector.getElem_ofFn]

end VG.Proof.Seed.X86_64
