module

import VerifiedGarbage.Proof.Camellia.Arm.Crypt8
public import VerifiedGarbage.Proof.Camellia.Arm.KeyLin
public import VerifiedGarbage.Proof.Camellia.Arm.Core
public import VerifiedGarbage.Proof.Camellia.Arm.StoreFrame
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Camellia.Arm.Fl
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.Camellia.Bitsliced

/-!
# Camellia's key schedule on ARMv7: a pair of rounds on one value

`pairPlain_step`: the running value, in the four words at `wSlot` (`VW`:
its bytes, the most significant first, four to a word, little-endian, as
ECB loads a block), in all eight lanes (`bcast_step`), through two rounds
with the next two entries of the table (`round_step`), and lane 0's words
back (`unbcast_step`), is `pair` of it.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Bitslice (lanes)
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp ldS stS)
open VG.Proof.Camellia (pair byteOf)
open VG.Proof.Sm4.Arm (linPostG linG_ok)

/-- The four words at slot `a` hold the value `v`: byte `c` of `v.1 ++ v.2`
(the most significant first) is byte `c % 4` of word `c / 4`. -/
def VW (s : State) (a : Nat) (v : BitVec 64 × BitVec 64) : Prop :=
  ∀ c < 16, ∀ j < 8, (slotW s (a + c / 4)).getLsbD (8 * (c % 4) + j) =
    (byteOf (if c < 8 then v.1 else v.2) (c % 8)).getLsbD j

theorem VW.congr {s s' : State} {a : Nat} {v : BitVec 64 × BitVec 64} (h : VW s a v)
    (hs : ∀ i < 4, slotW s' (a + i) = slotW s (a + i)) : VW s' a v := fun c hc j hj => by
  rw [hs _ (by omega)]; exact h c hc j hj

theorem ok_fromBsCfg {s : State} (hs : Scr s (s.gpr sb)) : Ok fromBsCfg s := ok_fromBs hs

theorem bcast_all : (layerKeep.all fun r => bcast.all fun i => !clobbers i r) = true ∧
    bcast.all (storesIn (4 * d1Slot) (4 * keySlot)) = true := by
  constructor <;> decide +kernel

theorem unbcast_all : (layerKeep.all fun r => unbcast.all fun i => !clobbers i r) = true ∧
    unbcast.all (storesIn (4 * wSlot) (4 * wSlot + 16)) = true := by
  constructor <;> decide +kernel

theorem wSlot_eq : wSlot = 640 := rfl

/-- The value in the planes of both halves, in every lane. -/
theorem bcast_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {v : BitVec 64 × BitVec 64} (hv : VW s wSlot v) :
    ∃ s', runBlock isa bcast s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ Halves s' (fun _ => v) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  have hs := hc.scr hp
  have hfit := hs.fit
  rw [slots_eq] at hfit
  obtain ⟨s', h', -, so', -, rd', wr', -, o', -, -, -⟩ := linG_ok bcast_check (ok_fromBsCfg hs)
    (fun i => slotW s (wSlot + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨w, hw, rfl, rfl⟩ := hji
      exact ⟨by simp only [fromBsCfg, wSlot_eq, tailSlot_eq]; omega, by omega, rfl⟩)
    (fun kv hkv => by simp at hkv) (fun j hj => by simp [fromBsCfg] at hj)
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp bcast_all.1 r (not_layerWrites r hr))
  have hb : s'.gpr sb = s.gpr sb := hkeep _ (by decide)
  obtain ⟨-, f'⟩ := runBlock_storesIn _ bcast_all.2 (by rw [keySlot_eq]; omega) h'
  have hpl : ∀ k < 32, ∀ p < 32, (slotW s' (d1Slot + k)).getLsbD p =
      (slotW s (wSlot + k / 8)).getLsbD (8 * (p / 8) + k % 8) := fun k hk p hp => by
    have := so' (d1Slot + k) (bcastG (k / 8) (k % 8))
      (by simp only [bcastOuts, List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩)
      (by simp only [fromBsCfg, d1Slot_eq, tailSlot_eq]; omega) p hp
    simp only [fromBsCfg] at this
    rw [slotW, hb, this, bcastG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc,
      bitOf_word _ _ _ (by omega)]
  refine ⟨s', h', hc.step rd' wr' (fun r h1 _ => hkeep r h1) ?_, hkeep _ (by decide), ⟨?_, ?_⟩,
    fun k h1 h2 => ?_⟩
  · refine f'.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inl rfl, ?_⟩
    simp only [storeRegion, hc.base]
    exact VG.Offset.sub_base _ (by rw [d1Slot_eq, keySlot_eq] <;> omega)
  · intro b hb c hc j hj
    show (slotW s' (d1Slot + (8 * (c / 4) + j))).getLsbD _ = _
    rw [hpl _ (by omega) _ (by omega), show (8 * (c / 4) + j) / 8 = c / 4 by omega,
      show (8 * (c / 4) + j) % 8 = j by omega, show (8 * (c % 4) + b) / 8 = c % 4 by omega,
      hv c (by omega) j hj, itePos hc, Nat.mod_eq_of_lt hc]
  · intro b hb c hc j hj
    show (slotW s' (d2Slot + (8 * (c / 4) + j))).getLsbD _ = _
    rw [show d2Slot + (8 * (c / 4) + j) = d1Slot + (16 + 8 * (c / 4) + j) by rw [d1Slot_eq, d2Slot_eq]; omega,
      hpl _ (by omega) _ (by omega), show (16 + 8 * (c / 4) + j) / 8 = (8 + c) / 4 by omega,
      show (16 + 8 * (c / 4) + j) % 8 = j by omega, show (8 * (c % 4) + b) / 8 = (8 + c) % 4 by omega,
      hv (8 + c) (by omega) j hj, iteNeg (show ¬ 8 + c < 8 by omega), show (8 + c) % 8 = c by omega]
  · simp only [slotW, hb]
    refine f'.readW (r := ⟨wordAddr (s.gpr sb) k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [wordAddr, VG.Arm.addr_add (by rw [slots_eq] at h2; omega)]
    exact VG.Offset.disjoint _ (by rw [d1Slot_eq, keySlot_eq] at *; omega) (by rw [slots_eq] at h2; omega)
      (by rw [d1Slot_eq, keySlot_eq]; omega)

/-- Lane 0's words back from the planes of the halves. -/
theorem unbcast_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa unbcast s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ VW s' wSlot (S 0) ∧
      (∀ k, k < slots → k < wSlot ∨ wSlot + 4 ≤ k → slotW s' k = slotW s k) := by
  have hs := hc.scr hp
  have hfit := hs.fit
  rw [slots_eq] at hfit
  obtain ⟨s', h', -, so', -, rd', wr', -, o', -, -, -⟩ := linG_ok unbcast_check (ok_fromBsCfg hs)
    (fun i => slotW s (d1Slot + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [fromBsCfg, d1Slot_eq, tailSlot_eq]; omega, by omega, rfl⟩)
    (fun kv hkv => by simp at hkv) (fun j hj => by simp [fromBsCfg] at hj)
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp unbcast_all.1 r (not_layerWrites r hr))
  have hb : s'.gpr sb = s.gpr sb := hkeep _ (by decide)
  obtain ⟨-, f'⟩ := runBlock_storesIn _ unbcast_all.2 (by rw [wSlot_eq]; omega) h'
  have hw : ∀ w < 4, ∀ t < 32, (slotW s' (wSlot + w)).getLsbD t =
      (slotW s (d1Slot + (8 * w + t % 8))).getLsbD (8 * (t / 8)) := fun w hw t ht => by
    have := so' (wSlot + w) (unbcastG w)
      (by simp only [unbcastOuts, List.mem_map, List.mem_range]; exact ⟨w, hw, rfl⟩)
      (by simp only [fromBsCfg, wSlot_eq, tailSlot_eq]; omega) t ht
    simp only [fromBsCfg] at this
    rw [slotW, hb, this, unbcastG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ (by omega)]
  obtain ⟨h1, h2⟩ := hS
  refine ⟨s', h', hc.step rd' wr' (fun r h1 _ => hkeep r h1) ?_, hkeep _ (by decide), fun c hc' j hj => ?_,
    fun k h1 h2 => ?_⟩
  · refine f'.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, by simp only [ctxRegions, List.mem_cons]; exact .inr (.inr (.inl rfl)), ?_⟩
    simp only [storeRegion]
    rw [← hc.base, VG.Arm.addr_add (by rw [tailSlot_eq]; omega)]
    exact VG.Offset.sub _ (by rw [wSlot_eq, tailSlot_eq]; omega) (by rw [wSlot_eq, tailSlot_eq]; omega)
  · rw [hw _ (by omega) _ (by omega), show (8 * (c % 4) + j) % 8 = j by omega,
      show (8 * (c % 4) + j) / 8 = c % 4 by omega]
    by_cases h8 : c < 8
    · have := h1 0 (by omega) c h8 j hj
      simp only [half] at this
      rw [itePos h8, Nat.mod_eq_of_lt h8, ← this, Nat.add_zero]
    · have := h2 0 (by omega) (c - 8) (by omega) j hj
      simp only [half] at this
      rw [iteNeg h8, show c % 8 = c - 8 by omega, ← this, Nat.add_zero,
        show d1Slot + (8 * (c / 4) + j) = d2Slot + (8 * ((c - 8) / 4) + j) by rw [d1Slot_eq, d2Slot_eq]; omega,
        show c % 4 = (c - 8) % 4 by omega]
  · simp only [slotW, hb]
    refine f'.readW (r := ⟨wordAddr (s.gpr sb) k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [wordAddr, VG.Arm.addr_add (by rw [slots_eq] at h1; omega)]
    exact VG.Offset.disjoint _ (by rw [wSlot_eq] at *; omega) (by rw [slots_eq] at h1; omega)
      (by rw [wSlot_eq]; omega)

/-- Two rounds on the running value, with entries `m` and `m + 1`. -/
theorem pairPlain_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {v : BitVec 64 × BitVec 64} (hv : VW s wSlot v) :
    ∃ s', runBlock isa pairPlain s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      VW s' wSlot (pair (E m) (E (m + 1)) v) ∧
      (∀ k, keySlot ≤ k → k < slots → k < wSlot ∨ wSlot + 4 ≤ k → slotW s' k = slotW s k) := by
  obtain ⟨s₁, e₁, c₁, k₁, ⟨h1, h2⟩, o₁⟩ := bcast_step hp hc hv
  have hk₁ : AtEntry s₁ (s₀.gpr sb) m := by rw [AtEntry, k₁]; exact hk
  obtain ⟨s₂, e₂, c₂, k₂, d₂, a₂, o₂⟩ := round_step hp c₁ (off := 0) (src := d1Slot) (dst := d2Slot)
    preL0_check mid0_check post2_check (.inl ⟨rfl, rfl, rfl⟩) hk₁ (by omega) hm34 h1 h2
  have hk₂ : AtEntry s₂ (s₀.gpr sb) m := by rw [AtEntry, k₂]; exact hk₁
  have h1' : W32.HalfRel (half s₂ d1Slot) (fun _ => v.1) := h1.congr fun i hi => a₂ i hi
  obtain ⟨s₃, e₃, c₃, k₃, d₃, a₃, o₃⟩ := round_step hp c₂ (off := 16) (src := d2Slot) (dst := d1Slot)
    preL16_check mid16_check post1_check (.inr ⟨rfl, rfl, rfl⟩) hk₂ (by omega) hm34 d₂ h1'
  have d₂' : W32.HalfRel (half s₃ d2Slot) (fun _ => v.2 ^^^ Spec.Camellia.f v.1 (E (m + 0 / 16))) :=
    d₂.congr fun i hi => a₃ i hi
  obtain ⟨s₄, e₄, c₄, k₄, w₄, o₄⟩ := unbcast_step hp c₃ (S := fun _ => pair (E m) (E (m + 1)) v) ⟨d₃, d₂'⟩
  let s₅ := s₄.setReg kp (s₄.gpr kp + BitVec.ofNat 32 128)
  refine ⟨s₅, ?_, c₄.step rfl rfl (fun r _ h2 => RegUpd.gpr_setReg_of_ne _ _ h2) (Frame.refl _ _), ?_,
    w₄.congr fun i _ => slotW_setReg _ _ (by decide) _, fun k h1 h2 h3 => ?_⟩
  · rw [pairPlain_eq, runBlock_app, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some]
    exact addKp_ok _ _ encodable_128
  · exact hk.add (n := 2) (by rw [RegUpd.gpr_setReg_self, k₄, k₃, k₂, k₁])
  · rw [slotW_setReg _ _ (by decide), o₄ k h2 h3, o₃ k h1 h2, o₂ k h1 h2, o₁ k h1 h2]

end VG.Proof.Camellia.Arm
