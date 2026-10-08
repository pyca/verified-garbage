import VerifiedGarbage.Proof.Camellia.AArch64.Copy

/-!
# Camellia's prologue and epilogue on AArch64

Saving and restoring the callee-saved registers `x19`–`x28` in their slots
(`save_ok`, `restore_ok`, by symbolic execution of the stores and loads),
and setting the masks of the layers (`setSlots_ok`, by evaluation: the
masks are constants of the lane domain).
-/

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 kp movR ldS stS imm)

theorem savedSlot_eq : savedSlot = 368 := rfl

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .x19

theorem savedRegs_eq : savedRegs = (List.range 10).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 10, m.readW (wordAddr b (savedSlot + i)) 64 = s₀.gpr (sreg i)

/-- The saved registers' slots. -/
def savedRegion (b : Addr) : Region := ⟨b + BitVec.ofNat 64 (8 * savedSlot), 80⟩

theorem sreg_ne_sb : ∀ i < 10, sreg i ≠ sb := by decide

theorem sreg_mem (r : Reg) : r ∈ (List.range 10).map sreg ↔ ∃ i < 10, sreg i = r := by
  simp only [List.mem_map, List.mem_range]

theorem save_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [savedRegion b] s.mem s'.mem ∧
      ∀ k, (k < savedSlot ∨ savedSlot + 10 ≤ k) → k < 2 ^ 58 → slotW s' k = slotW s k := by
  let L : List (Nat × Reg) := (List.range 10).map fun i => (savedSlot + i, sreg i)
  have hL : saveRegs = L.map fun x => stS x.1 x.2 := by
    rw [saveRegs, savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 10).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  rw [slots_eq] at hw
  obtain ⟨s', e', g', rd', wr', f', o', v'⟩ := stS_list_ok (savedRegion b) L s (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨by rw [savedSlot_eq]; omega, ⟨_, hw, ?_⟩, ?_⟩
      · rw [hb]; exact VG.Offset.contains_base b (by rw [savedSlot_eq]; omega) (by rw [savedSlot_eq]; omega)
      · rw [hb, savedRegion, wordAddr]
        exact VG.Offset.contains _ (by omega) (by omega) (by rw [savedSlot_eq]; omega))
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, g', rd', wr', f', fun k hk hk' => o' k ?_ hk'⟩
  · have := v' (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
    simp only [slotW, g', hb] at this
    exact this
  · rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; omega

theorem restore_ok {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 10, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := (List.range 10).map fun i => (sreg i, savedSlot + i)
  have hL : restoreRegs = L.map fun x => ldS x.1 x.2 := by
    rw [restoreRegs, savedRegs_eq]
  have hregs : L.map (·.1) = (List.range 10).map sreg := by simp only [L, List.map_map]; rfl
  rw [slots_eq] at hw
  obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldS_list_ok L s
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx; exact sreg_ne_sb i hi)
    (by rw [hregs]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨by rw [savedSlot_eq]; omega, ⟨_, List.mem_append_right _ hw, ?_⟩⟩
      rw [hb]; exact VG.Offset.contains_base b (by rw [savedSlot_eq]; omega) (by rw [savedSlot_eq]; omega))
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, fun r hr => o' r ?_, m', rd', wr'⟩
  · rw [v' (sreg i, savedSlot + i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩), slotW, hb]
    exact hs i hi
  · rw [hregs]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    exact fun i hi h => hr i hi h.symm

/-! ## The masks -/

/-- The masks' slots, below the table. -/
def maskCfg : Cfg := { base := sb, slots := keySlot, ext := sb, exts := 0 }

def maskPost (e : Env (Nat × Nat)) : Bool := layerMasks.all fun kv => e.slot kv.1 == some (kv.2.toNat, 0)

theorem setSlots_check :
    check (lanes 64 1) maskCfg (fun _ => none) (setSlots layerMasks) (linEnvG [] [] []) maskPost = true := by
  decide +kernel

theorem setSlots_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa (setSlots layerMasks) s = some s' ∧ MasksOk s' ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * keySlot⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ setSlots_check
  have hok : Ok maskCfg s :=
    Ok.of_region hw hb.symm (by show 8 * keySlot ≤ 8 * slots; rw [keySlot_eq, slots_eq]; omega)
      (by show 8 * keySlot < 2 ^ 64; rw [keySlot_eq]; decide) rfl
  have hrel : Rel (LaneRel 1 0) maskCfg (fun _ => none) (linEnvG [] [] []) s := by
    refine ⟨fun r a h => ?_, fun k a _ h => ?_, fun _ _ _ h => ?_, fun _ _ h => ?_⟩ <;>
      simp [linEnvG] at h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  have hall : ∀ r, r ≠ t0 → ((setSlots layerMasks).all fun i => dstOf i != some r) = true := by
    intro r hr
    have : ((setSlots layerMasks).all fun i => dstOf i == some t0 || dstOf i == none) = true := by
      decide +kernel
    simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at this ⊢
    intro i hi
    rcases this i hi with h | h <;> simp [h, Ne.symm hr]
  refine ⟨s', hs', fun kv hkv => ?_, fun r hr => p.other r (by simp [hall r hr]), p.rd, p.wr, ?_⟩
  · have h := List.all_eq_true.mp hpost kv hkv
    simp only [beq_iff_eq] at h
    have hr := p.rel.slot kv.1 _ (by simp only [maskCfg]; exact mask_lt hkv) h
    simp only [maskCfg] at hr
    apply BitVec.eq_of_getLsbD_eq
    intro q hq
    show (s'.mem.readW (wordAddr (s'.gpr sb) kv.1) 64).getLsbD q = _
    rw [hr.2 q hq, par_zero, Bool.xor_false]
    rfl
  · have := p.frame
    simpa [slotRegion, maskCfg, hb] using this

end VG.Proof.Camellia.AArch64
