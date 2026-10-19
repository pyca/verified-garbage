module

import VerifiedGarbage.Proof.Camellia.X86.Crypt8
public import VerifiedGarbage.Proof.Camellia.X86.KeyLin
public import VerifiedGarbage.Proof.Camellia.X86.Core
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Camellia.X86.Fl

/-!
# Camellia's key schedule on x86 (32-bit): a pair of rounds on one value

As on ARMv7 (`Proof/Camellia/Arm/KeyPair.lean`): `pairPlain_step`, the
running value, in the four words at `wSlot` (`VW`: its bytes, the most
significant first, four to a word, little-endian, as ECB loads a block),
in all eight lanes (`bcast_step`), through two rounds with the next two
entries of the table (`round_step`), and lane 0's words back
(`unbcast_step`), is `pair` of it. The other values in the tail buffer are
kept.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Bitslice (lanes bitOf xorBits bitOf_word xorBits_cons xorBits_nil)
open VG.Impl.Aes.X86 (sb tmpRegs addI)
open VG.Proof.Camellia (pair byteOf)

/-- The four words at slot `a` hold the value `v`: byte `c` of `v.1 ++ v.2`
(the most significant first) is byte `c % 4` of word `c / 4`. -/
def VW (s : State) (a : Nat) (v : BitVec 64 × BitVec 64) : Prop :=
  ∀ c < 16, ∀ j < 8, (slotW s (a + c / 4)).getLsbD (8 * (c % 4) + j) =
    (byteOf (if c < 8 then v.1 else v.2) (c % 8)).getLsbD j

theorem VW.congr {s s' : State} {a : Nat} {v : BitVec 64 × BitVec 64} (h : VW s a v)
    (hs : ∀ i < 4, slotW s' (a + i) = slotW s (a + i)) : VW s' a v := fun c hc j hj => by
  rw [hs _ (by omega)]; exact h c hc j hj

theorem bcast_all : ([Reg.esp, .esi, .edi].all fun r => bcast.all fun i => i.dst != some r) = true := by
  decide +kernel

theorem unbcast_all : ([Reg.esp, .esi, .edi].all fun r => unbcast.all fun i => i.dst != some r) = true := by
  decide +kernel

theorem wSlot_eq : wSlot = 80 := rfl

/-- The value in the planes of both halves, in every lane. -/
theorem bcast_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {v : BitVec 64 × BitVec 64} (hv : VW s wSlot v) :
    ∃ s', runBlock isa bcast s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ Halves s' (fun _ => v) ∧
      (∀ k, tailSlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  have hs := hc.scr hp
  obtain ⟨s', h', so', rd', wr', o', f'⟩ := linear_ok bcast_check (ok_bs hs) (fun i => slotW s (tailSlot + i))
    (fun j i hji hj => by
      simp only [tailIns', List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by omega, by rw [Nat.zero_add]; rfl⟩)
    (fun j hj => by simp [bsCfg] at hj)
  have hkeep : ∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r := fun r hr => o' r (keep_of_all bcast_all hr)
  have hb : s'.gpr sb = s.gpr sb := hkeep _ (by decide)
  have hpl : ∀ k < 32, ∀ p < 32, (slotW s' (d1Slot + k)).getLsbD p =
      (slotW s (wSlot + k / 8)).getLsbD (8 * (p / 8) + k % 8) := fun k hk p hp => by
    have := so' (d1Slot + k) (bcastG (k / 8) (k % 8))
      (List.mem_append_left _ (by simp only [List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩)) p hp
    simp only [bsCfg] at this
    rw [slotW, hb, this, bcastG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc,
      bitOf_word _ _ _ (by omega), show tailSlot + (8 + k / 8) = wSlot + k / 8 by rw [wSlot]; omega]
  refine ⟨s', h', hc.stepB rd' wr' (fun r h1 _ => hkeep r h1) f', hkeep _ (by decide), ⟨?_, ?_⟩,
    fun k h1 h2 => ?_⟩
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
  · by_cases hk : k < keySlot
    · have hk' : k - tailSlot < 32 := by rw [tailSlot_eq, keySlot_eq] at *; omega
      have := so' (tailSlot + (k - tailSlot)) _ (List.mem_append_right _ (List.mem_map.mpr
        ⟨k - tailSlot, List.mem_range.mpr hk', rfl⟩))
      rw [Nat.add_sub_cancel' h1] at this
      rw [slotW, hb]
      exact keep_word (W := fun i => slotW s (tailSlot + i)) (i := k - tailSlot)
        (by show slotW s (tailSlot + (k - tailSlot)) = _; rw [Nat.add_sub_cancel' h1]) this
    · exact slot_above_bs hs.fit hb f' (by omega) h2

/-- Lane 0's words back from the planes of the halves. -/
theorem unbcast_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa unbcast s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧ VW s' wSlot (S 0) ∧
      (∀ k, tailSlot ≤ k → k < slots → k < wSlot ∨ wSlot + 4 ≤ k → slotW s' k = slotW s k) := by
  have hs := hc.scr hp
  let W : Nat → BitVec 32 := fun i => if i < 32 then slotW s (d1Slot + i) else slotW s (tailSlot + (i - 32))
  obtain ⟨s', h', so', rd', wr', o', f'⟩ := linear_ok unbcast_check (ok_bs hs) W
    (fun j i hji hj => by
      simp only [halvesIns, tailIns', List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      rcases hji with ⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩
      · exact ⟨by omega, by simp [W, hk]; rfl⟩
      · exact ⟨by omega, by simp [W, show ¬ 32 + k < 32 by omega]; rfl⟩)
    (fun j hj => by simp [bsCfg] at hj)
  have hkeep : ∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r := fun r hr => o' r (keep_of_all unbcast_all hr)
  have hb : s'.gpr sb = s.gpr sb := hkeep _ (by decide)
  have hw : ∀ w < 4, ∀ t < 32, (slotW s' (wSlot + w)).getLsbD t =
      (slotW s (d1Slot + (8 * w + t % 8))).getLsbD (8 * (t / 8)) := fun w hw t ht => by
    have := so' (wSlot + w) (unbcastG w)
      (List.mem_append_left _ (by simp only [List.mem_map, List.mem_range]; exact ⟨w, hw, rfl⟩)) t ht
    simp only [bsCfg] at this
    rw [slotW, hb, this, unbcastG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ (by omega)]
    simp only [W, show 8 * w + t % 8 < 32 by omega, ↓reduceIte]
  obtain ⟨h1, h2⟩ := hS
  refine ⟨s', h', hc.stepB rd' wr' (fun r h1 _ => hkeep r h1) f', hkeep _ (by decide), fun c hc' j hj => ?_,
    fun k k1 k2 k3 => ?_⟩
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
  · by_cases hk : k < keySlot
    · have hk' : k - tailSlot < 32 := by rw [tailSlot_eq, keySlot_eq] at *; omega
      have hf : (!(8 ≤ k - tailSlot && k - tailSlot < 12)) = true := by
        rw [wSlot_eq] at k3; rw [tailSlot_eq] at k1 ⊢
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      have := so' (tailSlot + (k - tailSlot)) _ (List.mem_append_right _ (List.mem_map.mpr
        ⟨k - tailSlot, List.mem_filter.mpr ⟨List.mem_range.mpr hk', hf⟩, rfl⟩))
      rw [Nat.add_sub_cancel' k1] at this
      rw [slotW, hb]
      refine keep_word (W := W) (i := 32 + (k - tailSlot)) ?_ this
      simp only [W, show ¬ 32 + (k - tailSlot) < 32 by omega, ↓reduceIte, show 32 + (k - tailSlot) - 32 = k - tailSlot by omega,
        Nat.add_sub_cancel' k1]
    · exact slot_above_bs hs.fit hb f' (by omega) k2

/-- Two rounds on the running value, with entries `m` and `m + 1`. -/
theorem pairPlain_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {v : BitVec 64 × BitVec 64} (hv : VW s wSlot v) :
    ∃ s', runBlock isa pairPlain s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      VW s' wSlot (pair (E m) (E (m + 1)) v) ∧
      (∀ k, tailSlot ≤ k → k < slots → k < wSlot ∨ wSlot + 4 ≤ k → slotW s' k = slotW s k) := by
  obtain ⟨s₁, e₁, c₁, k₁, ⟨h1, h2⟩, o₁⟩ := bcast_step hp hc hv
  have hk₁ : AtEntry s₁ (s₀.gpr sb) m := by rw [AtEntry, k₁]; exact hk
  obtain ⟨s₂, e₂, c₂, k₂, d₂, a₂, o₂⟩ := round_step hp c₁ (off := 0) (src := d1Slot) (dst := d2Slot)
    preL0_check mid0_check post2_check (by decide +kernel) (.inl ⟨rfl, rfl, rfl⟩) hk₁ (by omega) hm34 h1 h2
  have hk₂ : AtEntry s₂ (s₀.gpr sb) m := by rw [AtEntry, k₂]; exact hk₁
  have h1' : W32.HalfRel (half s₂ d1Slot) (fun _ => v.1) := h1.congr fun i hi => a₂ i hi
  obtain ⟨s₃, e₃, c₃, k₃, d₃, a₃, o₃⟩ := round_step hp c₂ (off := 16) (src := d2Slot) (dst := d1Slot)
    preL16_check mid16_check post1_check (by decide +kernel) (.inr ⟨rfl, rfl, rfl⟩) hk₂ (by omega) hm34 d₂ h1'
  have d₂' : W32.HalfRel (half s₃ d2Slot) (fun _ => v.2 ^^^ Spec.Camellia.f v.1 (E (m + 0 / 16))) :=
    d₂.congr fun i hi => a₃ i hi
  obtain ⟨s₄, e₄, c₄, k₄, w₄, o₄⟩ := unbcast_step hp c₃ (S := fun _ => pair (E m) (E (m + 1)) v) ⟨d₃, d₂'⟩
  obtain ⟨s₅, e₅, kp₅, -, g₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ kp 128
  have hs₅ : ∀ k, slotW s₅ k = slotW s₄ k := fun k => by simp only [slotW, m₅, g₅ sb (by decide)]
  refine ⟨s₅, ?_, c₄.regs (fun r h _ => g₅ r h) m₅ rd₅ wr₅, ?_, w₄.congr fun i _ => hs₅ _, fun k h1 h2 h3 => ?_⟩
  · rw [pairPlain, runBlock_app, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅]
  · exact hk.add (n := 2) (by rw [kp₅, k₄, k₃, k₂, k₁]; rfl)
  · rw [hs₅, o₄ k h1 h2 h3, o₃ k h1 h2, o₂ k h1 h2, o₁ k h1 h2]

end VG.Proof.Camellia.X86
