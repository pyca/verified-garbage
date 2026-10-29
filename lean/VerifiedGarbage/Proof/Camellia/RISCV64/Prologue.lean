module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Round
public import VerifiedGarbage.TCB.RISCV64.Target

import VerifiedGarbage.Proof.Camellia.RISCV64.Crypt8
import VerifiedGarbage.Proof.Camellia.RISCV64.Core
import VerifiedGarbage.Proof.Camellia.RISCV64.Fl
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Camellia's prologue and epilogue on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/Prologue.lean`): saving and
restoring the callee-saved registers `s0`–`s11` in their slots (`save_ok`,
`restore_ok`, by symbolic execution of the stores and loads), and setting
the masks (`setSlots_ok`, each built by `movImm64` and stored).
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 kp movR ldS stS)

theorem WP.runBlock_of {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q) :
    ∃ s', runBlock isa is s = some s' ∧ Q s' := by
  induction is generalizing s with
  | nil => exact ⟨s, rfl, WP.block_nil_iff.mp h⟩
  | cons i is ih =>
    obtain ⟨s₁, e₁, h₁⟩ := WP.block_cons_iff.mp h
    obtain ⟨s', e', q⟩ := ih h₁
    exact ⟨s', by
      rw [show runBlock isa (i :: is) s = (isa.exec i s).bind (runBlock isa is) from rfl, e₁,
        Option.bind_some]; exact e', q⟩

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .s0

theorem savedRegs_eq : savedRegs = (List.range 12).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 12, m.readW (wordAddr b (savedSlot + i)) 64 = s₀.gpr (sreg i)

/-- The saved registers' slots. -/
def savedRegion (b : Addr) : Region := ⟨b + BitVec.ofNat 64 (8 * savedSlot), 96⟩

theorem sreg_ne_sb : ∀ i < 12, sreg i ≠ sb := by decide

/-- The callee-saved registers are those `savedRegs` saves. -/
theorem preserved_sreg : ∀ r ∈ preserved, ∃ i < 12, sreg i = r := by decide

theorem save_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hal : b.toNat % 8 = 0) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [savedRegion b] s.mem s'.mem ∧
      ∀ k, (k < savedSlot ∨ savedSlot + 12 ≤ k) → k < 2 ^ 58 → slotW s' k = slotW s k := by
  let L : List (Nat × Reg) := (List.range 12).map fun i => (savedSlot + i, sreg i)
  have hL : saveRegs = L.map fun x => stS x.1 x.2 := by
    rw [saveRegs, savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 12).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  rw [slots_eq] at hw
  obtain ⟨s', e', g', rd', wr', f', o', v'⟩ := stS_list_ok (savedRegion b) L s (by rw [hb]; exact hal)
    (by rw [hslots]; decide)
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
    (hal : b.toNat % 8 = 0) (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 12, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 12, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := (List.range 12).map fun i => (sreg i, savedSlot + i)
  have hL : restoreRegs = L.map fun x => ldS x.1 x.2 := by
    rw [restoreRegs, savedRegs_eq]
  have hregs : L.map (·.1) = (List.range 12).map sreg := by simp only [L, List.map_map]; rfl
  rw [slots_eq] at hw
  obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldS_list_ok L s (by rw [hb]; exact hal)
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

theorem setSlots_cons (k : Nat) (v : BitVec 64) (ms : List (Nat × BitVec 64)) :
    setSlots ((k, v) :: ms) = Impl.Words64.RISCV64.movImm64 t0 t1 v ++ ([stS k t0] ++ setSlots ms) := by
  simp only [setSlots, List.flatMap_cons, List.append_assoc]

/-- Masks to distinct slots below the saved registers. -/
theorem setSlots_gen : ∀ (ms : List (Nat × BitVec 64)) (s : State), (s.gpr sb).toNat % 8 = 0 →
    (ms.map (·.1)).Nodup →
    (∀ kv ∈ ms, kv.1 < savedSlot ∧ InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * kv.1)) 8) →
    ∃ s', runBlock isa (setSlots ms) s = some s' ∧ (∀ kv ∈ ms, slotW s' kv.1 = kv.2) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨s.gpr sb, 8 * savedSlot⟩] s.mem s'.mem ∧
      ∀ k, k ∉ ms.map (·.1) → k < 2 ^ 58 → slotW s' k = slotW s k
  | [], s, _, _, _ => ⟨s, rfl, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl, rfl, rfl,
      Frame.refl _ _, fun _ _ _ => rfl⟩
  | (k, v) :: ms, s, hal, hnd, hin => by
    have hx := hin (k, v) List.mem_cons_self
    have hk : k < savedSlot := hx.1
    rw [savedSlot_eq] at hk
    obtain ⟨s₁, e₁, v₁, g₁, m₁, rd₁, wr₁, -⟩ :=
      WP.runBlock_of (Words64.movImm64_ok (s := s) (d := t0) (tmp := t1) (by decide) v)
    have hb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide) (by decide)
    let s₂ : State := { s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) k) (s₁.gpr t0) }
    have e₂ : runBlock isa [stS k t0] s₁ = some s₂ :=
      stS_ok s₁ t0 (k := k) (by omega) (by rw [hb₁]; exact hal) (by rw [wr₁, hb₁]; exact hx.2)
    rw [List.map_cons, List.nodup_cons] at hnd
    have hb₂ : s₂.gpr sb = s.gpr sb := hb₁
    obtain ⟨s', e', v', g', rd', wr', f', o'⟩ := setSlots_gen ms s₂ (by rw [hb₂]; exact hal) hnd.2
      (fun y hy => by
        have := hin y (List.mem_cons_of_mem _ hy)
        exact ⟨this.1, by show InRegions s₁.wr _ 8; rw [wr₁, hb₁]; exact this.2⟩)
    have hs₂ : ∀ j, j ≠ k → j < 2 ^ 58 → slotW s₂ j = slotW s j := fun j hj hj58 => by
      show (s₁.mem.writeW _ _).readW (wordAddr (s₁.gpr sb) j) 64 = _
      rw [Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) hj) (by decide), m₁, hb₁]
    refine ⟨s', ?_, fun y hy => ?_, fun r h0 h1 => by rw [g' r h0 h1]; exact g₁ r h0 h1,
      rd'.trans rd₁, wr'.trans wr₁, ?_, fun j hj hj58 => ?_⟩
    · rw [setSlots_cons, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some]
      exact e'
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (by omega)]
        show (s₁.mem.writeW _ _).readW _ 64 = _
        rw [Mem.readW_writeW_self64, v₁]
      · exact v' y hy
    · rw [hb₂] at f'
      refine Frame.trans ?_ f'
      rw [show s.mem = s₁.mem from m₁.symm]
      refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
      rw [hb₁, wordAddr]
      exact VG.Offset.contains_base _ (by rw [savedSlot_eq]; omega) (by omega)
    · simp only [List.map_cons, List.mem_cons, not_or] at hj
      rw [o' j hj.2 hj58]; exact hs₂ j hj.1 hj58

theorem setSlots_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hal : b.toNat % 8 = 0) :
    ∃ s', runBlock isa (setSlots allMasks) s = some s' ∧ MasksOk s' ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * savedSlot⟩] s.mem s'.mem := by
  obtain ⟨s', e', v', g', rd', wr', f', -⟩ := setSlots_gen allMasks s (by rw [hb]; exact hal) (by decide)
    (fun kv hkv => by
      have := mask_lt hkv
      refine ⟨this, ⟨_, hw, ?_⟩⟩
      rw [savedSlot_eq] at this
      rw [hb]; exact VG.Offset.contains_base b (by rw [slots_eq]; omega) (by omega))
  rw [hb] at f'
  exact ⟨s', e', v', g', rd', wr', f'⟩

end VG.Proof.Camellia.RISCV64
