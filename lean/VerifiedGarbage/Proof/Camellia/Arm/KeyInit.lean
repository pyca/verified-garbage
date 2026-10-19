module

public import VerifiedGarbage.Proof.Camellia.Arm.Prologue
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Impl.Camellia.Arm.ExpandKey
public import VerifiedGarbage.Proof.Camellia.Arm.Core
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Camellia.Arm.Copy
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Camellia.Arm.KeyPair
import VerifiedGarbage.Proof.Camellia.Planes32

/-!
# Camellia's key schedule on ARMv7: the prologue and the key

`ekPrologue_ok`: the callee-saved registers saved, the schedule's pointer
and the key's length in their slots, and the planes of `Sigma1 … Sigma6`
stored as the table's first six entries (`constStores_ok`), which hold the
constants in every lane (`sigma_rel`). `loadKey_wp`: `KL` and `KR`, from
the key's words, in their slots (`VW`).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS eorR imm32)
open VG.Impl.Camellia (sigmas keyPlane32)
open VG.Proof.Camellia (sigma_rel)
open VG.Proof.Camellia (byteOf getLsbD_byteOf sigE byteOf_wordAt)

/-! ## Constants -/

/-- `movw d, #lo; movt d, #hi`. -/
theorem imm32_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa (imm32 d v) s = some s' ∧ s'.gpr d = v ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₁ := s.setReg d ((v.extractLsb' 0 16).setWidth 32)
  refine ⟨s₁.setReg d (v.extractLsb' 16 16 ++ (s₁.gpr d).extractLsb' 0 16), ?_, ?_,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl, rfl, rfl⟩
  · rw [imm32, runBlock_cons, show exec (.movw d (v.extractLsb' 0 16)) s = some s₁ from rfl, runStep_some,
      runBlock_cons, show exec (.movt d (v.extractLsb' 16 16)) s₁ =
        some (s₁.setReg d (v.extractLsb' 16 16 ++ (s₁.gpr d).extractLsb' 0 16)) from rfl,
      runStep_some, runBlock_nil]
  · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self]; exact movw_movt v

/-- `imm32 t0, v; str t0, [sb, #4 k]` for each `(k, v)` of `L`. -/
theorem constStores_ok {b : BitVec 32} : ∀ (L : List (Nat × BitVec 32)) {s : State}, s.gpr sb = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.flatMap fun (k, v) => imm32 t0 v ++ [stS k t0]) s = some s' ∧
      (∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = x.2) ∧
      (∀ k < slots, k ∉ L.map (·.1) → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | x :: L, s, hb, hw, hnd, hin => by
    have hx := hin x List.mem_cons_self
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := imm32_ok s t0 x.2
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, sp₂, -, f₂⟩ := stSlot_ok s₁ t0 sb (k := x.1)
      (by rw [o₁ _ (by decide), hb]) hx (by rw [wr₁]; exact hw)
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', k', g', rd', wr', sp', f'⟩ := constStores_ok L (s := s₂)
      (by rw [g₂, o₁ _ (by decide), hb]) (by rw [wr₂, wr₁]; exact hw) hnd.2
      fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hfit := hw.fit
    have hslot : ∀ j < slots, s₂.mem.readW (wordAddr b j) 32 = if j = x.1 then x.2 else
        s.mem.readW (wordAddr b j) 32 := fun j hj => by
      rw [m₂, readW_slot_write hfit _ hj hx, v₁, m₁]
    refine ⟨s', ?_, fun y hy => ?_, fun j hj hn => ?_, fun r hr => by rw [g' r hr, g₂, o₁ r hr],
      by rw [rd', rd₂, rd₁], by rw [wr', wr₂, wr₁], by rw [sp', sp₂, sp₁], ?_⟩
    · rw [List.flatMap_cons, runBlock_app, runBlock_app, e₁, Option.bind_some,
        show ([stS x.1 t0] : List Instr) = [.str t0 sb (4 * x.1)] from rfl, e₂, Option.bind_some]
      exact e'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · by_cases hin' : y.1 ∈ L.map (·.1)
        · exact absurd hin' hnd.1
        · rw [k' _ hx hin', hslot _ hx, ite_eq_left rfl]
      · exact v' y hy'
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · rw [← m₁]
      exact (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hx⟩).trans f'

/-- The table's first six entries' words. -/
def sigmaTable : List (Nat × BitVec 32) :=
  (List.range 6).flatMap fun e => (List.range 16).map fun k => (keySlot + 16 * e + k, keyPlane32 (sigE e) (k / 8) (k % 8))

theorem sigmas_zipIdx : sigmas.zipIdx = (List.range 6).map fun e => (sigE e, e) := rfl

theorem sigmas_eq : (sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x) =
    sigmaTable.flatMap fun (k, v) => imm32 t0 v ++ [stS k t0] := by
  rw [sigmas_zipIdx]
  simp only [sigmaTable, List.flatMap_map, List.flatMap_assoc, sigmaOne]

theorem sigmaTable_nodup : (sigmaTable.map (·.1)).Nodup ∧ ∀ x ∈ sigmaTable, x.1 < slots := by
  constructor <;> decide

theorem mem_sigmaTable {e k : Nat} (he : e < 6) (hk : k < 16) :
    (keySlot + 16 * e + k, keyPlane32 (sigE e) (k / 8) (k % 8)) ∈ sigmaTable := by
  simp only [sigmaTable, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨e, he, k, hk, rfl⟩

theorem sigmaTable_slot {x : Nat × BitVec 32} (hx : x ∈ sigmaTable) : keySlot ≤ x.1 ∧ x.1 < keySlot + 96 := by
  simp only [sigmaTable, List.mem_flatMap, List.mem_range, List.mem_map] at hx
  obtain ⟨e, he, k, hk, rfl⟩ := hx
  simp only; omega

/-! ## The prologue -/

theorem ekPrologue_ok {s₀ : State} {b : BitVec 32} (hb : s₀.gpr .r3 = b) (hw : ScrIn s₀.wr b) :
    ∃ s, runBlock isa (saveRegs .r3 ++ [movR sb .r3, stS dSlot .r2, stS nSlot .r1] ++
        (sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x)) s₀ = some s ∧
      s.gpr sb = b ∧ (∀ r, r ≠ sb → r ≠ t0 → s.gpr r = s₀.gpr r) ∧ Saved s₀ b s.mem ∧
      s.mem.readW (wordAddr b dSlot) 32 = s₀.gpr .r2 ∧ s.mem.readW (wordAddr b nSlot) 32 = s₀.gpr .r1 ∧
      (∀ e < 6, ∀ j < 16, entryW s.mem b e j = keyPlane32 (sigE e) (j / 8) (j % 8)) ∧
      Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  have hfit := hw.fit
  obtain ⟨s₁, e₁, sv₁, g₁, rd₁, wr₁, sp₁, f₁, -⟩ := save_ok hw hb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movR_ok s₁ sb .r3
  have b₂ : s₂.gpr sb = b := by rw [r₂, g₁, hb]
  have hw₂ : ScrIn s₂.wr b := by rw [wr₂, wr₁]; exact hw
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, sp₃, -, f₃⟩ := stSlot_ok s₂ .r2 sb (k := dSlot) b₂ (by decide) hw₂
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, f₄⟩ := stSlot_ok s₃ .r1 sb (k := nSlot) (by rw [g₃, b₂]) (by decide)
    (by rw [wr₃]; exact hw₂)
  obtain ⟨hnd, hlt⟩ := sigmaTable_nodup
  obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, sp₅, f₅⟩ := constStores_ok sigmaTable (s := s₄) (by rw [g₄, g₃, b₂])
    (by rw [wr₄, wr₃]; exact hw₂) hnd hlt
  have hout : ∀ k, k < keySlot ∨ keySlot + 96 ≤ k → k ∉ sigmaTable.map (·.1) := fun k hk h => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    have := sigmaTable_slot hx; omega
  have hg : ∀ r, r ≠ sb → r ≠ t0 → s₅.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [g₅ r h2, g₄, g₃, o₂ r h1, g₁]
  have hrun : runBlock isa (saveRegs .r3 ++ [movR sb .r3, stS dSlot .r2, stS nSlot .r1] ++
      (sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x)) s₀ = some s₅ := by
    rw [sigmas_eq, runBlock_app, runBlock_app, e₁, Option.bind_some,
      show ([movR sb .r3, stS dSlot .r2, stS nSlot .r1] : List Instr) =
        [movR sb .r3] ++ ([.str .r2 sb (4 * dSlot)] ++ [.str .r1 sb (4 * nSlot)]) from rfl,
      runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄, Option.bind_some]
    exact e₅
  refine ⟨s₅, hrun, by rw [g₅ _ (by decide), g₄, g₃, b₂], hg, fun i hi => ?_, ?_, ?_, fun e he j hj => ?_, ?_,
    by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁], by rw [sp₅, sp₄, sp₃, sp₂, sp₁]⟩
  · rw [k₅ _ (by rw [savedSlot_eq, slots_eq]; omega) (hout _ (.inr (by rw [savedSlot_eq, keySlot_eq]; omega))),
      m₄, readW_slot_write hfit _ (by rw [savedSlot_eq, slots_eq]; omega) (by decide),
      ite_eq_right (by rw [savedSlot_eq, nSlot_eq]; omega), m₃,
      readW_slot_write hfit _ (by rw [savedSlot_eq, slots_eq]; omega) (by decide),
      ite_eq_right (by rw [savedSlot_eq, dSlot_eq]; omega), m₂]
    exact sv₁ i hi
  · rw [k₅ _ (by decide) (hout _ (.inr (by decide))), m₄, readW_slot_write hfit _ (by decide) (by decide),
      ite_eq_right (by decide), m₃, readW_slot_write hfit _ (by decide) (by decide), ite_eq_left rfl, o₂ _ (by decide),
      g₁]
  · rw [k₅ _ (by decide) (hout _ (.inr (by decide))), m₄, readW_slot_write hfit _ (by decide) (by decide),
      ite_eq_left rfl, g₃, o₂ _ (by decide), g₁]
  · have := v₅ _ (mem_sigmaTable he hj)
    simp only at this
    rw [entryW]; exact this
  · refine f₁.trans ?_
    rw [← m₂]
    refine (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      ((f₄.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans f₅) <;>
      (simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit (by decide))

end VG.Proof.Camellia.Arm
