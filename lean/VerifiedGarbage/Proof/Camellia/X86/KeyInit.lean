module

public import VerifiedGarbage.Proof.Camellia.X86.Prologue
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Impl.Camellia.X86.ExpandKey
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Camellia.Planes32

/-!
# Camellia's key schedule on x86 (32-bit): the prologue

As on ARMv7 (`Proof/Camellia/Arm/KeyInit.lean`): `ekPrologue_ok`, the
callee-saved registers saved, and the planes of `Sigma1 … Sigma6` stored
as the table's first six entries (`constStores_ok`), which hold the
constants in every lane (`sigma_rel`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb tmpRegs slotAt st movI argOp)
open VG.Impl.Camellia (sigmas keyPlane32)
open VG.Proof.Camellia (sigma_rel sigE)

/-- `mov eax, v; mov [edi + 4 k], eax` for each `(k, v)` of `L`. -/
theorem constStores_ok {b : BitVec 32} : ∀ (L : List (Nat × BitVec 32)) {s : State}, s.gpr sb = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.flatMap fun (k, v) => [movI .eax v, st k .eax]) s = some s' ∧
      (∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = x.2) ∧
      (∀ k < slots, k ∉ L.map (·.1) → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | (k, v) :: L, s, hb, hw, hnd, hin => by
    have hx : k < slots := hin (k, v) List.mem_cons_self
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := movI_ok s .eax v
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .eax .edi (b := b) (k := k)
      (by rw [o₁ _ (by decide)]; exact hb) hx (by rw [wr₁]; exact hw)
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := constStores_ok L (s := s₂)
      (by rw [show s₂.gpr sb = s₁.gpr sb from congrFun g₂ sb, o₁ _ (by decide), hb]) (by rw [wr₂, wr₁]; exact hw)
      hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hfit := hw.fit
    have hslot : ∀ j < slots, s₂.mem.readW (wordAddr b j) 32 = if j = k then v else
        s.mem.readW (wordAddr b j) 32 := fun j hj => by
      rw [m₂, readW_slot_write hfit _ hj hx, v₁, m₁]
    refine ⟨s', ?_, fun y hy => ?_, fun j hj hn => ?_, fun r hr => by rw [g' r hr, g₂, o₁ r hr],
      by rw [rd', rd₂, rd₁], by rw [wr', wr₂, wr₁], ?_⟩
    · dsimp only
      rw [List.flatMap_cons]
      dsimp only
      rw [runBlock_app,
        show ([movI .eax v, st k .eax] : List Instr) = [movI .eax v] ++ [.store (slotAt .edi k) .eax] from rfl,
        runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some]
      exact e'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · by_cases hin' : k ∈ L.map (·.1)
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
    sigmaTable.flatMap fun (k, v) => [movI .eax v, st k .eax] := by
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

theorem ekPrologue_ok {s₀ : State} {b : BitVec 32} (hw : ScrIn s₀.wr b)
    (ha : InRegions (s₀.rd ++ s₀.wr) (s₀.ea (argOp 3)) 4) (hb : s₀.mem.readW (s₀.ea (argOp 3)) 32 = b) :
    ∃ s, runBlock isa (saveRegs 3 ++ (sigmas.zipIdx.flatMap fun (x, e) => sigmaOne e x)) s₀ = some s ∧
      s.gpr sb = b ∧ (∀ r, r ≠ .eax → r ≠ .edi → s.gpr r = s₀.gpr r) ∧ Saved s₀ b s.mem ∧
      (∀ e < 6, ∀ j < 16, entryW s.mem b e j = keyPlane32 (sigE e) (j / 8) (j % 8)) ∧
      (∀ k < slots, k < keySlot ∨ keySlot + 96 ≤ k → k < savedSlot →
        s.mem.readW (wordAddr b k) 32 = s₀.mem.readW (wordAddr b k) 32) ∧
      Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hfit := hw.fit
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, k₁⟩ := save_ok hw ha hb
  obtain ⟨hnd, hlt⟩ := sigmaTable_nodup
  obtain ⟨s₂, e₂, v₂, k₂, g₂, rd₂, wr₂, f₂⟩ := constStores_ok sigmaTable (s := s₁) b₁
    (by rw [wr₁]; exact hw) hnd hlt
  have hout : ∀ k, k < keySlot ∨ keySlot + 96 ≤ k → k ∉ sigmaTable.map (·.1) := fun k hk h => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    have := sigmaTable_slot hx; omega
  refine ⟨s₂, by rw [runBlock_app, e₁, Option.bind_some, sigmas_eq]; exact e₂, (g₂ _ (by decide)).trans b₁,
    fun r h1 h2 => by rw [g₂ r h1, g₁ r h1 h2], fun i hi => ?_, fun e he j hj => ?_, fun k hk h1 h2 => ?_,
    f₁.trans f₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [k₂ _ (by rw [savedSlot_eq, slots_eq]; omega) (hout _ (.inr (by rw [savedSlot_eq, keySlot_eq]; omega)))]
    exact sv₁ i hi
  · have := v₂ _ (mem_sigmaTable he hj)
    simp only at this
    rw [entryW]; exact this
  · rw [k₂ k hk (hout k h1), k₁ k h2]

end VG.Proof.Camellia.X86
