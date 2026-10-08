import VerifiedGarbage.Proof.Seed.X86_64.Batch

/-!
# Storing to scratch slots

`stores_ok`: stores of registers to distinct slots; `masks_ok`: `setMasks`,
constants through `t0` to distinct slots. Both write only the scratch
buffer.
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Impl.Aes.X86_64

theorem slot_in_scratch (s : State) {j : Nat} (hj : j < scratchSlots) :
    (scratchR s).Contains (wordAddr (s.gpr .r9) j) (64 / 8) :=
  slot_contains (s.gpr .r9) (n := scratchSlots) hj (by unfold scratchSlots; decide)

/-- The memory after storing `v` in slot `k`. -/
def stMem (s : State) (k : Nat) (v : BitVec 64) : Mem := s.mem.writeW (wordAddr (s.gpr .r9) k) v

theorem exec_st {s : State} (h : Room s) {k : Nat} (hk : k < scratchSlots) (r : Reg) :
    exec (st k r) s = some (setMem s (stMem s k (s.gpr r))) := by
  have hw : InRegions s.wr (wordAddr (s.gpr .r9) k) 8 := ⟨scratchR s, h, slot_in_scratch s hk⟩
  have hea : s.ea (slotAt sb k) = wordAddr (s.gpr .r9) k := rfl
  simp only [st, exec, State.store64, hea, hw, ite_true, stMem]
  rfl

theorem slotW_stMem (s : State) {k : Nat} (hk : k < scratchSlots) (v : BitVec 64) {j : Nat}
    (hj : j < scratchSlots) : slotW (setMem s (stMem s k v)) j = if j = k then v else slotW s j := by
  unfold scratchSlots at hk hj
  show (stMem s k v).readW (wordAddr (s.gpr .r9) j) 64 = _
  simp only [stMem]
  split
  · subst j; exact Mem.readW_writeW_self64 _ _ _
  · rename_i hne
    rw [Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) hne) (by decide)]
    rfl

theorem stMem_frame {s : State} {k : Nat} (hk : k < scratchSlots) (v : BitVec 64) :
    Frame [scratchR s] s.mem (stMem s k v) :=
  (Frame.refl _ _).writeW List.mem_cons_self _ (slot_in_scratch s hk)

theorem slotW_setReg (s : State) {r : Reg} (hr : r ≠ .r9) (v : BitVec 64) (j : Nat) :
    slotW (s.setReg r v) j = slotW s j := by
  show s.mem.readW (wordAddr ((s.setReg r v).gpr .r9) j) 64 = s.mem.readW (wordAddr (s.gpr .r9) j) 64
  rw [gpr_setReg_of_ne (s := s) v (Ne.symm hr)]

/-- A block of stores of registers to distinct scratch slots. -/
theorem stores_ok {s : State} (h : Room s) (l : List (Nat × Reg)) (hl : ∀ p ∈ l, p.1 < scratchSlots)
    (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => st p.1 p.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [scratchR s] s.mem s'.mem ∧
      (∀ p ∈ l, slotW s' p.1 = s.gpr p.2) ∧
      (∀ x < scratchSlots, (∀ p ∈ l, p.1 ≠ x) → slotW s' x = slotW s x) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, rfl, Frame.refl _ _, (fun _ h => by cases h),
      fun _ _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_st (r := p.2) h hp
    let s₁ : State := setMem s (stMem s p.1 (s.gpr p.2))
    have h₁ : Room s₁ := h
    have hd' : (l.map (·.1)).Nodup := (List.nodup_cons.mp hd).2
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', g', rd', wr', f', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hd'
    refine ⟨s', ?_, g', rd', wr', (stMem_frame hp _).trans f', fun q hq => ?_,
      fun x hx hne => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ hp (fun r hr he => hn (he ▸ List.mem_map_of_mem hr)), slotW_stMem s hp _ hp]
        simp
      · exact set' q hq
    · rw [keep' x hx (fun q hq => hne q (List.mem_cons_of_mem _ hq)), slotW_stMem s hp _ hx]
      simp [Ne.symm (hne p List.mem_cons_self)]

/-- `setMasks`: constants to distinct scratch slots, through `t0`. -/
theorem masks_ok {s : State} (h : Room s) (l : List (Nat × BitVec 64))
    (hl : ∀ p ∈ l, p.1 < scratchSlots) (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (setMasks l) s = some s' ∧ (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [scratchR s] s.mem s'.mem ∧
      (∀ p ∈ l, slotW s' p.1 = p.2) ∧
      (∀ x < scratchSlots, (∀ p ∈ l, p.1 ≠ x) → slotW s' x = slotW s x) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, (fun _ h => by cases h),
      fun _ _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    let s₀ := s.setReg t0 p.2
    have e₀ : exec (imm t0 p.2) s = some s₀ := rfl
    have r9₀ : s₀.gpr .r9 = s.gpr .r9 := gpr_setReg_of_ne (s := s) _ (by decide)
    have h₀ : Room s₀ := room_congr h r9₀ rfl
    have e := exec_st (r := t0) h₀ hp
    let s₁ : State := setMem s₀ (stMem s₀ p.1 (s₀.gpr t0))
    have h₁ : Room s₁ := h₀
    have hd' : (l.map (·.1)).Nodup := (List.nodup_cons.mp hd).2
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', g', rd', wr', f', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hd'
    have f₀ : Frame [scratchR s] s.mem s₁.mem := by
      have := stMem_frame (s := s₀) hp (s₀.gpr t0)
      simp only [scratchR, r9₀] at this
      exact this
    have f'' : Frame [scratchR s] s₁.mem s'.mem := by
      simpa only [scratchR, s₁, gpr_setMem, r9₀] using f'
    have sl₀ : ∀ j, slotW s₀ j = slotW s j := slotW_setReg s (by decide) _
    refine ⟨s', ?_, fun r hr => ?_, rd', wr', f₀.trans f'', fun q hq => ?_, fun x hx hne => ?_⟩
    · show runBlock isa ([imm t0 p.2, st p.1 t0] ++ setMasks l) s = some s'
      rw [List.cons_append, runBlock_cons, e₀, runStep_some, List.singleton_append, runBlock_cons, e,
        runStep_some]
      exact run'
    · rw [g' r hr]; exact gpr_setReg_of_ne (s := s) _ hr
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ hp (fun r hr he => hn (he ▸ List.mem_map_of_mem hr)), slotW_stMem s₀ hp _ hp]
        simp [s₀, gpr_setReg]
      · exact set' q hq
    · rw [keep' x hx (fun q hq => hne q (List.mem_cons_of_mem _ hq)), slotW_stMem s₀ hp _ hx,
        ite_eq_right_iff.mpr (fun h' => absurd h' (Ne.symm (hne p List.mem_cons_self))), sl₀]

theorem exec_ld {s : State} (h : Room s) {k : Nat} (hk : k < scratchSlots) (r : Reg) :
    exec (movS r k) s = some (s.setReg r (slotW s k)) := by
  have hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r9) k) 8 :=
    ⟨scratchR s, List.mem_append_right _ h, slot_in_scratch s hk⟩
  have hea : s.ea (slotAt sb k) = wordAddr (s.gpr .r9) k := rfl
  simp only [movS, exec, readSrc, State.load64, hea, hr, ite_true, Option.map_some]
  rfl

/-- A block of loads of distinct registers, other than `r9`, from scratch slots. -/
theorem loads_ok {s : State} (h : Room s) (l : List (Reg × Nat))
    (hl : ∀ p ∈ l, p.2 < scratchSlots ∧ p.1 ≠ .r9) (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => movS p.1 p.2) s = some s' ∧ s'.mem = s.mem ∧
      (∀ p ∈ l, s'.gpr p.1 = slotW s p.2) ∧ (∀ r, (∀ p ∈ l, p.1 ≠ r) → s'.gpr r = s.gpr r) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, (fun _ h => by cases h), fun _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_ld h hp.1 p.1
    let s₁ := s.setReg p.1 (slotW s p.2)
    have c₁ : s₁.gpr .r9 = s.gpr .r9 := gpr_setReg_of_ne (s := s) _ (Ne.symm hp.2)
    have h₁ : Room s₁ := room_congr h c₁ rfl
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', m', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (List.nodup_cons.mp hd).2
    have sl₁ : ∀ j, slotW s₁ j = slotW s j := slotW_setReg s hp.2 _
    refine ⟨s', ?_, by rw [m']; rfl, fun q hq => ?_, fun r hr => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ (fun r hr he => hn (by rw [← he]; exact List.mem_map_of_mem hr))]
        simp [s₁, gpr_setReg]
      · rw [set' q hq, sl₁]
    · rw [keep' r (fun q hq => hr q (List.mem_cons_of_mem _ hq))]
      simp only [s₁]
      rw [gpr_setReg_of_ne (s := s) _ (Ne.symm (hr p List.mem_cons_self))]

end VG.Proof.Seed.X86_64
