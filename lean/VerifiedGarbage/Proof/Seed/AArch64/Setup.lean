import VerifiedGarbage.Proof.Seed.AArch64.Batch

/-!
# Storing to and loading from scratch slots

`stores_ok`: stores of registers to distinct slots, writing only the
scratch buffer; `loads_ok`: loads of distinct registers, other than `x5`,
from slots.
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Impl.Aes.AArch64

theorem slot_in_scratch (s : State) {j : Nat} (hj : j < scratchSlots) :
    (scratchR s).Contains (wordAddr (s.gpr .x5) j) (64 / 8) :=
  slot_contains (s.gpr .x5) (n := scratchSlots) hj (by unfold scratchSlots; decide)

theorem slot_off {j : Nat} (hj : j < scratchSlots) : 8 * j % 8 = 0 ∧ 8 * j < 32768 := by
  unfold scratchSlots at hj; omega

/-- The memory after storing `v` in slot `k`. -/
def stMem (s : State) (k : Nat) (v : BitVec 64) : Mem := s.mem.writeW (wordAddr (s.gpr .x5) k) v

theorem exec_st {s : State} (h : Room s) {k : Nat} (hk : k < scratchSlots) (r : Reg) :
    exec (stS k r) s = some (setMem s (stMem s k (s.gpr r))) :=
  exec_str_x (slot_off hk) ⟨scratchR s, h, slot_in_scratch s hk⟩

theorem exec_ld {s : State} (h : Room s) {k : Nat} (hk : k < scratchSlots) (r : Reg) :
    exec (ldS r k) s = some (s.write .x r (slotW s k)) :=
  exec_ldr_x (slot_off hk) ⟨scratchR s, List.mem_append_right _ h, slot_in_scratch s hk⟩

theorem slotW_stMem (s : State) {k : Nat} (hk : k < scratchSlots) (v : BitVec 64) {j : Nat}
    (hj : j < scratchSlots) : slotW (setMem s (stMem s k v)) j = if j = k then v else slotW s j := by
  unfold scratchSlots at hk hj
  show (stMem s k v).readW (wordAddr (s.gpr .x5) j) 64 = _
  simp only [stMem]
  split
  · subst j; exact Mem.readW_writeW_self64 _ _ _
  · rename_i hne
    rw [Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) hne) (by decide)]
    rfl

theorem stMem_frame {s : State} {k : Nat} (hk : k < scratchSlots) (v : BitVec 64) :
    Frame [scratchR s] s.mem (stMem s k v) :=
  (Frame.refl _ _).writeW List.mem_cons_self _ (slot_in_scratch s hk)

theorem slotW_write (s : State) {r : Reg} (hr : r ≠ .x5) (v : BitVec 64) (j : Nat) :
    slotW (s.write .x r v) j = slotW s j := by
  show s.mem.readW (wordAddr ((s.write .x r v).gpr .x5) j) 64 = s.mem.readW (wordAddr (s.gpr .x5) j) 64
  rw [gpr_write_of_ne _ _ _ (Ne.symm hr)]

/-- A block of stores of registers to distinct scratch slots. -/
theorem stores_ok {s : State} (h : Room s) (l : List (Nat × Reg)) (hl : ∀ p ∈ l, p.1 < scratchSlots)
    (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => stS p.1 p.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [scratchR s] s.mem s'.mem ∧
      (∀ p ∈ l, slotW s' p.1 = s.gpr p.2) ∧
      (∀ x < scratchSlots, (∀ p ∈ l, p.1 ≠ x) → slotW s' x = slotW s x) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, rfl, rfl, Frame.refl _ _, (fun _ h => by cases h),
      fun _ _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_st (r := p.2) h hp
    let s₁ : State := setMem s (stMem s p.1 (s.gpr p.2))
    have h₁ : Room s₁ := h
    have hd' : (l.map (·.1)).Nodup := (List.nodup_cons.mp hd).2
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', g', rd', wr', sp', f', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hd'
    refine ⟨s', ?_, g', rd', wr', sp', (stMem_frame hp _).trans f', fun q hq => ?_,
      fun x hx hne => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ hp (fun r hr he => hn (he ▸ List.mem_map_of_mem hr)), slotW_stMem s hp _ hp]
        simp
      · exact set' q hq
    · rw [keep' x hx (fun q hq => hne q (List.mem_cons_of_mem _ hq)), slotW_stMem s hp _ hx]
      simp [Ne.symm (hne p List.mem_cons_self)]

/-- A block of loads of distinct registers, other than `x5`, from scratch slots. -/
theorem loads_ok {s : State} (h : Room s) (l : List (Reg × Nat))
    (hl : ∀ p ∈ l, p.2 < scratchSlots ∧ p.1 ≠ .x5) (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => ldS p.1 p.2) s = some s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ p ∈ l, s'.gpr p.1 = slotW s p.2) ∧ (∀ r, (∀ p ∈ l, p.1 ≠ r) → s'.gpr r = s.gpr r) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, (fun _ h => by cases h), fun _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_ld h hp.1 p.1
    let s₁ := s.write .x p.1 (slotW s p.2)
    have c₁ : s₁.gpr .x5 = s.gpr .x5 := gpr_write_of_ne _ _ _ (Ne.symm hp.2)
    have h₁ : Room s₁ := room_congr h c₁ rfl
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', m', sp', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (List.nodup_cons.mp hd).2
    have sl₁ : ∀ j, slotW s₁ j = slotW s j := slotW_write s hp.2 _
    refine ⟨s', ?_, by rw [m']; rfl, by rw [sp']; rfl, fun q hq => ?_, fun r hr => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ (fun r hr he => hn (by rw [← he]; exact List.mem_map_of_mem hr))]
        simp [s₁, gpr_write]
      · rw [set' q hq, sl₁]
    · rw [keep' r (fun q hq => hr q (List.mem_cons_of_mem _ hq))]
      simp only [s₁]
      rw [gpr_write_of_ne _ _ _ (Ne.symm (hr p List.mem_cons_self))]

end VG.Proof.Seed.AArch64
