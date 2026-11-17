module

public import VerifiedGarbage.Impl.Camellia.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Camellia.RISCV64.Core
public import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Camellia.RISCV64.Group
import VerifiedGarbage.Proof.Camellia.RISCV64.Prologue
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.RISCV64.KeyChecks
public import VerifiedGarbage.Proof.Camellia.RISCV64.Linear

/-! ### `Camellia.RISCV64.KeyPair`, which this module and modules that import it used -/

section

/-! ### `Camellia.RISCV64.KeyChecks2`, which only this module used -/

section

/-!
# The key schedule's evaluated facts on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyPair.lean`): `spread d`, which
bitslices the word at `[a0 + d]` into all eight lanes as `toBs` bitslices
eight words, keeping the masks and both halves' slots (`spread0_check`,
`spread8_check`). The constants' planes (`sigmaOne`) are stored by
`sigmaOne_ok` (`Proof/Camellia/RISCV64/KeySetup.lean`), as the lane domain
does not follow `movImm64`.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 kp movR)
open VG.Proof.Camellia (HalfRel pos)

/-- The masks' slots below the saved registers; the running value's two words at `a0`. -/
def kaCfg : Cfg := { base := sb, slots := savedSlot, ext := .a0, exts := 2 }

/-- The halves' slots are input words 2–17, after the running value's two at `a0`. -/
def kaIns : List (Nat × Nat) := (List.range 16).map fun j => (d1Slot + j, 2 + j)

def kaEnv : Env (Nat × Nat) := linEnvG [] kaIns allMasks

/-- Plane `j` of word `d / 8` at `a0`: bit `8 c + b` is bit `j` of its byte `pos c`. -/
def spreadBsG (d j p : Nat) : List Nat := [64 * (d / 8) + 8 * pos (p / 8) + j]

/-- `spread d`: the running value's word at `[a0 + d]` in all lanes,
keeping the masks and both halves' slots. -/
theorem spread0_check :
    check (lanes 64 11) kaCfg (linExt 0) (spread 0) kaEnv
      (linPostG 11 (qOuts (spreadBsG 0)) [] (maskSlots ++ kaIns.map (·.1)) kaEnv) = true := by
  decide +kernel

theorem spread8_check :
    check (lanes 64 11) kaCfg (linExt 0) (spread 8) kaEnv
      (linPostG 11 (qOuts (spreadBsG 8)) [] (maskSlots ++ kaIns.map (·.1)) kaEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.RISCV64

end

end


/-!
# A pair of rounds of the key schedule on RISCV64

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyPair.lean`): `pairPlain_ok`: with the running value's halves as words at
`r3` (`wSlot`) and `kp` at entry `m` of a table of the subkeys `E`,
`pairPlain` leaves `pair (E m) (E (m + 1))` of them there, and `kp` at entry
`m + 2`. The rounds are ECB's (`round_step`), on eight copies of the value.
The value's slots are in the tail buffer, which `Ctx` lets ECB write, so
each step also states that it keeps the slots from the saved registers on.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 kp movR ldS stS)
open VG.Proof.Aes.RISCV64 (sboxWrites not_sboxWrites restRegs)
open VG.Proof.Camellia (HalfRel WordRel pair)

theorem wSlot_eq : wSlot = 100 := rfl

/-- `spread d`: the half at `[r3 + d]`, a word of `wSlot`, in every lane. -/
theorem spread_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {d : Nat} (hd : d = 0 ∨ d = 8) (hr3 : s.gpr .a0 = s₀.gpr sb + BitVec.ofNat 64 (8 * wSlot))
    {H : BitVec 64} (hw : WordOf (slotW s (wSlot + d / 8)) H) :
    ∃ s', runBlock isa (spread d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .a0 = s.gpr .a0 ∧ HalfRel (Qs s') (fun _ => H) ∧
      (∀ j < 16, slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧
      (∀ k, savedSlot ≤ k → k < 2 ^ 58 → slotW s' k = slotW s k) := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  have hb := hc.base
  obtain hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr := by rw [hc.wr, hb]; exact hp.scr
  obtain hrw : ∀ k, wordAddr (s.gpr .a0) k = wordAddr (s.gpr sb) (wSlot + k) := fun k => by
    rw [hr3, hb, wordAddr, wordAddr, addr_add, Nat.mul_add]
  obtain hok : Ok kaCfg s :=
    { slotIn := fun k hk => ⟨_, hscr, by
        simp only [kaCfg, savedSlot_eq] at hk ⊢
        exact VG.Offset.contains_base _ (by rw [slots_eq]; omega_arith) (by omega_arith)⟩
      extIn := fun k hk => ⟨_, List.mem_append_right _ hscr, by
        simp only [kaCfg] at hk ⊢
        rw [hrw]; exact VG.Offset.contains_base _ (by rw [slots_eq, wSlot_eq]; omega_arith) (by rw [wSlot_eq]; omega_arith)⟩
      baseAl := fun _ => by simp only [kaCfg]; rw [hb]; exact hp.al
      extAl := fun _ => by simp only [kaCfg]; rw [hr3]; exact Spill.al8 hp.al (by rw [wSlot_eq])
      slots := by simp [kaCfg, savedSlot_eq]
      sep := fun k hk j hj => by
        simp only [kaCfg, savedSlot_eq] at hk hj ⊢
        rw [hrw]; exact slot_sep _ (by omega_arith) (by rw [wSlot_eq]; omega_arith) (by rw [wSlot_eq]; omega_arith) }
  obtain hchk : check (lanes 64 11) kaCfg (linExt 0) (spread d) kaEnv
      (linPostG 11 (qOuts (spreadBsG d)) [] (maskSlots ++ kaIns.map (·.1)) kaEnv) = true := by
    rcases hd with rfl | rfl
    · exact spread0_check
    · exact spread8_check
  unfold kaEnv at hchk
  let W : Nat → BitVec 64 := fun k =>
    if k < 2 then s.mem.readW (wordAddr (s.gpr .a0) k) 64 else slotW s (d1Slot + (k - 2))
  obtain ⟨s', h', ho, -, hkp, rd', wr', -, o', f', hb', -⟩ := linG_ok hchk hok W
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [kaIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨j, hj, rfl, rfl⟩ := hji
      refine ⟨by simp only [kaCfg, d1Slot, savedSlot]; omega_arith, by omega_arith, ?_⟩
      simp only [W, show ¬ 2 + j < 2 by omega_arith, ↓reduceIte, show 2 + j - 2 = j by omega_arith]; rfl)
    (fun kv hkv => ⟨by simp only [kaCfg]; exact mask_lt hkv, by simp only [kaCfg]; exact hc.masks kv hkv⟩)
    (fun j hj => ⟨by simp only [kaCfg] at hj; omega_arith, by
      simp only [kaCfg] at hj ⊢; simp only [W, Nat.zero_add, hj, ↓reduceIte]⟩)
  simp only [kaCfg] at hb' hkp f'
  obtain hall : ∀ r, r ∉ sboxWrites → ((spread d).all fun i => dst i != some r) = true := fun r hr => by
    obtain h := not_sboxWrites r hr
    have : (restRegs.all fun r => (spread d).all fun i => dst i != some r) = true := by
      rcases hd with rfl | rfl <;> decide +kernel
    exact List.all_eq_true.mp this r h
  obtain hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr => o' r (hall r hr)
  obtain f'' : Frame [⟨s₀.gpr sb, 8 * savedSlot⟩] s.mem s'.mem := by
    refine f'.mono fun r hr => ?_
    simp only [slotRegion, List.mem_singleton] at hr; subst hr; simp [hb]
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) f'' (fun kv hkv => ?_), hkeep _ (by decide),
    hkeep _ (by decide), ?_, fun j hj => ?_, fun k hk hk' => slotW_above hc (hkeep _ (by decide)) f'' hk hk'⟩
  · show s'.mem.readW (wordAddr (s'.gpr sb) kv.1) 64 = kv.2
    rw [hb', hkp kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (mask_lt hkv)]
    exact hc.masks kv hkv
  · refine Camellia.half_of_words (W := fun _ => slotW s (wSlot + d / 8)) (fun j hj p hp => ?_)
      (wordOf_iff_rel.mp hw)
    have := Camellia.pos_lt (show p / 8 < 8 by omega_arith)
    rw [Qs, ho (q j) (spreadBsG d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      p hp, spreadBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ (by omega_arith)]
    simp only [W, show d / 8 < 2 by omega_arith, ↓reduceIte, hrw]
  · show s'.mem.readW (wordAddr (s'.gpr sb) _) 64 = _
    rw [hb']
    exact hkp _ (List.mem_append_right _ (by
      simp only [kaIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp only [d1Slot, savedSlot]; omega_arith)

/-! ## Slots of the key schedule -/

/-- `KeyCtx` moves to a state with the same base, regions, masks and table. -/
theorem KeyCtx.transfer {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E)
    (hsb : s.gpr sb = s₀.gpr sb) (hwr : s.wr = s₀.wr) (hm : MasksOk s)
    (he : ∀ i < nk, ∀ j < 8, entryW s.mem (s₀.gpr sb) i j = entryW s₀.mem (s₀.gpr sb) i j) :
    KeyCtx s nk E where
  scr := by rw [hwr, hsb]; exact hp.scr
  al := by rw [hsb]; exact hp.al
  fit := by rw [hsb]; exact hp.fit
  nk34 := hp.nk34
  masks := hm
  keys i hi := by rw [hsb]; exact (hp.keys i hi).congr fun j hj => he i hi j hj

theorem readW_slot_write {m : Mem} {b : Addr} {j k : Nat} (v : BitVec 64) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 64 = if j = k then v else m.readW (wordAddr b j) 64 := by
  rw [slots_eq] at hj hk
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_arith) (by omega_arith) h) (by decide)

/-- A store below the table keeps its entries. -/
theorem entryW_write {m : Mem} {b : Addr} {k : Nat} (v : BitVec 64) (hk2 : k < keySlot)
    {i j : Nat} (hi : i < 34) (hj : j < 8) :
    entryW (m.writeW (wordAddr b k) v) b i j = entryW m b i j := by
  obtain he : ∀ m : Mem, entryW m b i j = m.readW (wordAddr b (keySlot + 8 * i + j)) 64 := fun m => by
    rw [entryW, wordAddr, show 8 * keySlot + 64 * i + 8 * j = 8 * (keySlot + 8 * i + j) by omega_arith]
  rw [he, he, readW_slot_write v (by rw [slots_eq, keySlot_eq]; omega_arith)
      (by rw [keySlot_eq] at hk2; rw [slots_eq]; omega_arith),
    ite_eq_right (show ¬ keySlot + 8 * i + j = k by omega_arith)]

/-- The slots after a store to slot `k`. -/
theorem slotW_store {s s' : State} {k : Nat} {v : BitVec 64}
    (hm : s'.mem = s.mem.writeW (wordAddr (s.gpr sb) k) v) (hg : s'.gpr = s.gpr) {j : Nat} (hj : j < slots)
    (hk : k < slots) : slotW s' j = if j = k then v else slotW s j := by
  simp only [slotW, hm, hg]; exact readW_slot_write v hj hk

/-- A store to the tail buffer keeps the masks and `KeyCtx`. -/
theorem KeyCtx.store {s₀ s s' : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {k : Nat} {v : BitVec 64} (hm : s'.mem = s.mem.writeW (wordAddr (s.gpr sb) k) v) (hg : s'.gpr = s.gpr)
    (hwr : s'.wr = s.wr) (hk : tailSlot ≤ k) (hk2 : k < keySlot) : KeyCtx s' nk E := by
  have h34 := hp.nk34
  refine (hp.transfer (s := s) hc.base hc.wr hc.masks
    (fun i hi j hj => hc.entry hp (by omega_arith) hj)).transfer (by rw [hg]) hwr (fun kv hkv => ?_)
    (fun i hi j hj => by rw [hm]; exact entryW_write v hk2 (by omega_arith) hj)
  have := mask_lt hkv
  rw [slotW_store hm hg (by rw [slots_eq]; rw [savedSlot_eq] at this; omega_arith)
      (by rw [keySlot_eq] at hk2; rw [slots_eq]; omega_arith),
    ite_eq_right (show ¬ kv.1 = k by rw [tailSlot_eq] at hk; rw [savedSlot_eq] at this; omega_arith)]
  exact hc.masks kv hkv

/-- `sd q0, 8 k(sb)`, under `Ctx`, to a slot of the tail buffer. -/
theorem stQ_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {k : Nat} (hk : tailSlot ≤ k) (hk2 : k < keySlot) :
    ∃ s', runBlock isa [stS k (q 0)] s = some s' ∧
      s'.mem = s.mem.writeW (wordAddr (s.gpr sb) k) (s.gpr (q 0)) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ KeyCtx s' nk E :=
  ⟨_, stS_ok s (q 0) (by rw [keySlot_eq] at hk2; omega_arith) (by rw [hc.base]; exact hp.al)
      (hc.inWr hp (by rw [keySlot_eq] at hk2; rw [slots_eq]; omega_arith)), rfl, rfl, rfl, rfl,
    hp.store hc rfl rfl rfl hk hk2⟩

/-! ## A pair of rounds -/

theorem pairPlain_ok {s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s nk E)
    {m : Nat} (hk : AtEntry s (s.gpr sb) m) (hm : m + 1 < nk)
    (hr3 : s.gpr .a0 = s.gpr sb + BitVec.ofNat 64 (8 * wSlot))
    {H1 H2 : BitVec 64} (hw1 : WordOf (slotW s wSlot) H1) (hw2 : WordOf (slotW s (wSlot + 1)) H2) :
    ∃ s', runBlock isa pairPlain s = some s' ∧ KeyCtx s' nk E ∧ AtEntry s' (s.gpr sb) (m + 2) ∧
      (∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a0 → s'.gpr r = s.gpr r) ∧ s'.gpr .a0 = s.gpr .a0 ∧
      WordOf (slotW s' wSlot) (pair (E m) (E (m + 1)) (H1, H2)).1 ∧
      WordOf (slotW s' (wSlot + 1)) (pair (E m) (E (m + 1)) (H1, H2)).2 ∧
      (∀ k, savedSlot ≤ k → k < slots → k ≠ wSlot → k ≠ wSlot + 1 → slotW s' k = slotW s k) ∧
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hm34 : m + 2 ≤ 34 := by have := hp.nk34; omega_arith
  have hfit := hp.fit
  rw [slots_eq] at hfit
  obtain h58 : ∀ k, k < slots → k < 2 ^ 58 := fun k hk => by rw [slots_eq] at hk; omega_arith
  -- The value, bitsliced: `D2` from the second word, `D1` from the first.
  obtain ⟨s₁, e₁, c₁, kp₁, x₁, q₁, -, a₁⟩ := spread_step hp (Ctx.refl hp.masks) (d := 8) (Or.inr rfl) hr3 hw2
  obtain hk₁ : AtEntry s₁ (s.gpr sb) m := by rw [AtEntry, kp₁]; exact hk
  obtain ⟨s₂, e₂, c₂, kp₂, x₂, -, h₂, -, a₂⟩ := storeHalf_step hp c₁ (Or.inr rfl) storeHalf2_check hk₁ hm34
  obtain hk₂ : AtEntry s₂ (s.gpr sb) m := by rw [AtEntry, kp₂]; exact hk₁
  obtain hD2 : HalfRel (fun j => slotW s₂ (d2Slot + j)) (fun _ => H2) := q₁.congr fun j hj => h₂ j hj
  obtain ⟨s₃, e₃, c₃, kp₃, x₃, q₃, o₃, a₃⟩ := spread_step hp c₂ (d := 0) (Or.inl rfl)
    (by rw [x₂, x₁, hr3]) (hw1.congr (by rw [a₂ _ (by decide) (by decide), a₁ _ (by decide) (by decide)]; rfl))
  obtain hk₃ : AtEntry s₃ (s.gpr sb) m := by rw [AtEntry, kp₃]; exact hk₂
  obtain ⟨s₄, e₄, c₄, kp₄, x₄, q₄, h₄, o₄, a₄⟩ := storeHalf_step hp c₃ (Or.inl rfl) storeHalf1_check hk₃ hm34
  obtain hk₄ : AtEntry s₄ (s.gpr sb) m := by rw [AtEntry, kp₄]; exact hk₃
  obtain hd2 : ∀ j < 8, slotW s₄ (d2Slot + j) = slotW s₂ (d2Slot + j) := fun j hj => by
    obtain a := o₄ (8 + j) (by omega_arith) (Or.inr (by simp only [d1Slot]; omega_arith))
    obtain b := o₃ (8 + j) (by omega_arith)
    rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega_arith] at a b
    rw [a, b]
  -- The two rounds.
  obtain ⟨s₅, e₅, c₅, k₅, r₅, q₅, d₅, o₅, a₅⟩ := round_step hp c₄ (off := 0) (d := d2Slot) keyIn0_check
    feistel2_check (by decide) (by decide) hk₄ (by omega_arith) hm34 (q₃.congr q₄) (hD2.congr hd2)
  obtain h1' : HalfRel (fun j => slotW s₅ (d1Slot + j)) (fun _ => H1) :=
    (q₃.congr fun j hj => h₄ j hj).congr fun j hj => o₅ j (by omega_arith) (Or.inl (by simp [d1Slot, d2Slot]; omega_arith))
  obtain ⟨s₆, e₆, c₆, k₆, r₆, q₆, d₆, o₆, a₆⟩ := round_step hp c₅ (off := 8) (d := d1Slot) keyIn8_check
    feistel1_check (by decide) (by decide) (by rw [AtEntry, k₅]; exact hk₄) (by omega_arith) hm34 q₅ h1'
  obtain hk₆ : AtEntry s₆ (s.gpr sb) m := by rw [AtEntry, k₆, k₅]; exact hk₄
  obtain d₅' : HalfRel (fun j => slotW s₆ (d2Slot + j)) (fun _ => (pair (E m) (E (m + 1)) (H1, H2)).2) :=
    d₅.congr fun j hj => by
      have := o₆ (8 + j) (by omega_arith) (Or.inr (by simp only [d1Slot]; omega_arith))
      rw [show d1Slot + (8 + j) = d2Slot + j by simp [d1Slot, d2Slot]; omega_arith] at this
      exact this
  -- The first word.
  obtain ⟨s₇, e₇, c₇, kp₇, x₇, q₇, d₇, -, a₇⟩ := lin_step hp c₆ hk₆ hm34 fromBs_check (by decide +kernel)
  obtain hW1 : WordRel (Qs s₇) (fun _ => (pair (E m) (E (m + 1)) (H1, H2)).1) := fromBs_rel q₇ q₆
  obtain ⟨s₈, e₈, m₈, g₈, rd₈, wr₈, hp₈⟩ := stQ_step hp c₇ (k := wSlot) (by decide) (by decide)
  obtain hb₈ : s₈.gpr sb = s.gpr sb := by rw [g₈, c₇.base]
  -- The second word.
  obtain hk₈ : AtEntry s₈ (s₈.gpr sb) m := by rw [AtEntry, hb₈, g₈, kp₇]; exact hk₆
  obtain ⟨s₉, e₉, c₉, kp₉, x₉, q₉, -, a₉⟩ := loadHalf_step hp₈ (Ctx.refl hp₈.masks) (Or.inr rfl)
    loadHalf2_check hk₈ hm34
  obtain hD2' : HalfRel (Qs s₉) (fun _ => (pair (E m) (E (m + 1)) (H1, H2)).2) := d₅'.congr fun j hj => by
    have := d₇ (8 + j) (by omega_arith)
    rw [show d1Slot + (8 + j) = d2Slot + j by simp [d1Slot, d2Slot]; omega_arith] at this
    rw [q₉ j hj, slotW_store m₈ g₈ (by simp only [d2Slot, slots_eq]; omega_arith) (by decide),
      ite_eq_right (show ¬ d2Slot + j = wSlot by simp only [d2Slot, wSlot_eq]; omega_arith), this]
  obtain hk₉ : AtEntry s₉ (s₈.gpr sb) m := by rw [AtEntry, kp₉]; exact hk₈
  obtain ⟨s₁₀, e₁₀, c₁₀, kp₁₀, x₁₀, q₁₀, -, -, a₁₀⟩ := lin_step hp₈ c₉ hk₉ hm34 fromBs_check (by decide +kernel)
  obtain hW2 : WordRel (Qs s₁₀) (fun _ => (pair (E m) (E (m + 1)) (H1, H2)).2) := fromBs_rel q₁₀ hD2'
  obtain ⟨s₁₁, e₁₁, m₁₁, g₁₁, rd₁₁, wr₁₁, hp₁₁⟩ := stQ_step hp₈ c₁₀ (k := wSlot + 1) (by decide) (by decide)
  obtain ⟨s₁₂, e₁₂, kp₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂⟩ := addKp_ok s₁₁ 128 (by decide)
  obtain hsl : ∀ k, slotW s₁₂ k = slotW s₁₁ k := fun k => by
    simp only [slotW, m₁₂, o₁₂ sb (by decide)]
  -- The slots from the saved registers on.
  obtain hab : ∀ k, savedSlot ≤ k → k < slots → k ≠ wSlot → slotW s₈ k = slotW s k := fun k h1 h2 h3 => by
    rw [slotW_store m₈ g₈ h2 (by decide), ite_eq_right h3, a₇ k h1 (h58 k h2), a₆ k h1 (h58 k h2),
      a₅ k h1 (h58 k h2), a₄ k h1 (h58 k h2), a₃ k h1 (h58 k h2), a₂ k h1 (h58 k h2), a₁ k h1 (h58 k h2)]
  obtain hhi : ∀ k, savedSlot ≤ k → k < slots → k ≠ wSlot + 1 → slotW s₁₂ k = slotW s₈ k := fun k h1 h2 h3 => by
    rw [hsl k, slotW_store m₁₁ g₁₁ h2 (by decide), ite_eq_right h3, a₁₀ k h1 (h58 k h2), a₉ k h1 (h58 k h2)]
  refine ⟨s₁₂, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, fun k h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · unfold pairPlain
    rw [show ([stS (wSlot + 1) (q 0), .addi kp kp 128] : List Instr) =
        [stS (wSlot + 1) (q 0)] ++ [.addi kp kp 128] from rfl]
    simp only [List.append_assoc]
    rw [runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some,
      runBlock_append', e₅, Option.bind_some, runBlock_append', e₆, Option.bind_some,
      runBlock_append', e₇, Option.bind_some, runBlock_append', e₈, Option.bind_some,
      runBlock_append', e₉, Option.bind_some, runBlock_append', e₁₀, Option.bind_some,
      runBlock_append', e₁₁, Option.bind_some, e₁₂]
  · refine hp₁₁.transfer (o₁₂ sb (by decide)) wr₁₂ (fun kv hkv => ?_) (fun i hi j hj => by rw [m₁₂])
    show s₁₂.mem.readW (wordAddr (s₁₂.gpr sb) kv.1) 64 = kv.2
    rw [m₁₂, o₁₂ sb (by decide)]; exact hp₁₁.masks kv hkv
  · rw [AtEntry, kp₁₂, g₁₁, kp₁₀, kp₉, g₈, kp₇, k₆, k₅, show s₄.gpr kp = _ from hk₄, addr_add,
      show 8 * keySlot + 64 * m + 128 = 8 * keySlot + 64 * (m + 2) by omega_arith]
  · rw [o₁₂ r h2, g₁₁, c₁₀.keep r h1 h2 h3, g₈, c₇.keep r h1 h2 h3]
  · rw [o₁₂ _ (by decide), g₁₁, x₁₀, x₉, g₈, x₇, r₆, r₅, x₄, x₃, x₂, x₁]
  · rw [hhi _ (by decide) (by decide) (by decide), slotW_store m₈ g₈ (by decide) (by decide), ite_eq_left rfl]
    exact fun i hi j hj => hW1 0 (by decide) i hi j hj
  · rw [hsl, slotW_store m₁₁ g₁₁ (by decide) (by decide), ite_eq_left rfl]
    exact fun i hi j hj => hW2 0 (by decide) i hi j hj
  · rw [hhi k h1 h2 h4, hab k h1 h2 h3]
  · have hsub : ∀ {t : State}, t.gpr sb = s.gpr sb →
        ∀ r ∈ ctxRegions (t.gpr sb), ∃ r' ∈ [(⟨s.gpr sb, 8 * slots⟩ : Region)], Region.Sub r r' := by
      intro t hb r hr
      simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rcases hr with rfl | rfl
      · rw [hb]; exact Region.sub_prefix (by decide)
      · rw [hb]; exact VG.Offset.sub_base _ (by decide)
    obtain hst : ∀ {t : State} (k : Nat), k < slots → t.gpr sb = s.gpr sb →
        (⟨s.gpr sb, 8 * slots⟩ : Region).Contains (wordAddr (t.gpr sb) k) (64 / 8) := fun k hk hb => by
      rw [hb, wordAddr]; rw [slots_eq] at hk
      exact VG.Offset.contains_base _ (by rw [slots_eq]; omega_arith) (by omega_arith)
    obtain f₈ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₈.mem := by
      rw [m₈]; exact (c₇.frame.sub (hsub rfl)).writeW (List.mem_singleton_self _) _
        (hst _ (by decide) c₇.base)
    rw [m₁₂, m₁₁]
    exact (f₈.trans (c₁₀.frame.sub (hsub hb₈))).writeW (List.mem_singleton_self _) _
      (hst _ (by decide) (c₁₀.base.trans hb₈))
  · rw [rd₁₂, rd₁₁, c₁₀.rd, rd₈, c₇.rd]
  · rw [wr₁₂, wr₁₁, c₁₀.wr, wr₈, c₇.wr]

end VG.Proof.Camellia.RISCV64

end

end

/-!
# `KA` and `KB` on RISCV64

As on PPC64LE (`Proof/Camellia/PPC64LE/KaKb.lean`): `kaKb_wp`: from the halves of `KL` and `KR` as words in their
slots, the loop of three pairs of rounds (`pairPlain_ok`), with the XORs and
copies between them on the plain words (`xorWords_ok`, `copyWords_ok`),
leaves the halves of `KA` and `KB` in theirs (`Spec.Camellia.kakb`, by
`kakb_halves`).
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 kp movR ldS stS xorR shrI)
open VG.Proof.Aes.RISCV64 (sboxWrites)
open VG.Proof.Camellia (HalfRel WordRel pair hiW loW)

/-! ## Moving words between slots -/

theorem slotW_eq_of {s s' : State} (hm : s'.mem = s.mem) (hb : s'.gpr sb = s.gpr sb) (k : Nat) :
    slotW s' k = slotW s k := by
  simp only [slotW, hm, hb]

theorem scr_in {s : State} {b : Addr} (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < slots) :
    InRegions s.wr (b + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨_, hscr, by rw [slots_eq] at hk; exact VG.Offset.contains_base _ (by rw [slots_eq]; omega_arith) (by omega_arith)⟩

theorem frame_slot {m : Mem} {b : Addr} {k : Nat} (v : BitVec 64) (hk : k < slots) :
    Frame [⟨b, 8 * slots⟩] m (m.writeW (wordAddr b k) v) :=
  frame_writeW v (by rw [wordAddr]; rw [slots_eq] at hk; exact VG.Offset.sub_base _ (by rw [slots_eq]; omega_arith))

/-- `ldr d, [sb, #8 k]`. -/
theorem ldS_ok {s : State} {b : Addr} {k : Nat} (d : Reg) (hb : s.gpr sb = b) (hal : b.toNat % 8 = 0)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < keySlot) :
    ∃ s', runBlock isa [ldS d k] s = some s' ∧ s'.gpr d = slotW s k ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have := scr_in hscr (show k < slots by rw [keySlot_eq] at hk; rw [slots_eq]; omega_arith)
  rw [← hb] at this
  exact ldMask_ok (by rw [keySlot_eq] at hk; omega_arith) (by rw [hb]; exact hal) (inRd this) rfl

/-- `str r, [sb, #8 k]`. -/
theorem stS_slot {s : State} {b : Addr} {k : Nat} (r : Reg) (hb : s.gpr sb = b) (hal : b.toNat % 8 = 0)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < keySlot) :
    ∃ s', runBlock isa [stS k r] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have := scr_in hscr (show k < slots by rw [keySlot_eq] at hk; rw [slots_eq]; omega_arith)
  rw [← hb] at this
  exact ⟨_, stS_ok s r (by rw [keySlot_eq] at hk; omega_arith) (by rw [hb]; exact hal) this, by rw [hb], rfl, rfl,
    rfl⟩

theorem eor_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [xorR d n m] s = some s' ∧ s'.gpr d = s.gpr n ^^^ s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (s.gpr n ^^^ s.gpr m), by
    simp only [xorR, runBlock_cons, runStep_some, runBlock_nil, exec_logic],
    RegUpd.gpr_write_self _ _ _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- `copyWords w x`: the two words at slot `x` to slot `w`. -/
theorem copyWords_ok {s : State} {b : Addr} {w x : Nat} (hb : s.gpr sb = b) (hal : b.toNat % 8 = 0)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hwk : w + 1 < keySlot) (hxk : x + 1 < keySlot) (hxw : x + 1 ≠ w) :
    ∃ s', runBlock isa (copyWords w x) s = some s' ∧
      (∀ k < slots, slotW s' k = if k = w then slotW s x else if k = w + 1 then slotW s (x + 1) else slotW s k) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hw : w + 1 < slots := by rw [keySlot_eq] at hwk; rw [slots_eq]; omega_arith
  obtain hx : x + 1 < slots := by rw [keySlot_eq] at hxk; rw [slots_eq]; omega_arith
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := ldS_ok (k := x) t0 hb hal hscr (by omega_arith)
  obtain hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stS_slot (k := w) t0 hb₁ hal (by rw [wr₁]; exact hscr) (by omega_arith)
  obtain hb₂ : s₂.gpr sb = b := by rw [g₂, hb₁]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := ldS_ok (k := x + 1) t0 hb₂ hal (by rw [wr₂, wr₁]; exact hscr) hxk
  obtain hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), hb₂]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stS_slot (k := w + 1) t0 hb₃ hal (by rw [wr₃, wr₂, wr₁]; exact hscr) hwk
  obtain h₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ (hb₁.trans hb.symm)
  obtain h₂ : ∀ k < slots, slotW s₂ k = if k = w then slotW s x else slotW s k := fun k hk => by
    rw [slotW_store (by rw [m₂, hb₁]) g₂ hk (by omega_arith), a₁, h₁]
  obtain h₃ : ∀ k, slotW s₃ k = slotW s₂ k := slotW_eq_of m₃ (hb₃.trans hb₂.symm)
  refine ⟨s₄, ?_, fun k hk => ?_, fun r hr => ?_, ?_, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show copyWords w x = [ldS t0 x] ++ ([stS w t0] ++ ([ldS t0 (x + 1)] ++ [stS (w + 1) t0]))
      from rfl, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, e₄]
  · rw [slotW_store (by rw [m₄, hb₃]) g₄ hk hw, a₃, h₂ (x + 1) hx, ite_eq_right hxw, h₃, h₂ k hk]
    exact ite_swap2 _ _ _
  · rw [g₄, o₃ r hr, g₂, o₁ r hr]
  · rw [m₄, m₃, m₂, m₁]
    exact (frame_slot _ (by omega_arith)).trans (frame_slot _ hw)

/-- `xorWords w x`: the two words at slot `x` XORed into those at slot `w`. -/
theorem xorWords_ok {s : State} {b : Addr} {w x : Nat} (hb : s.gpr sb = b) (hal : b.toNat % 8 = 0)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hwk : w + 1 < keySlot) (hxk : x + 1 < keySlot) (hxw : x + 1 ≠ w) :
    ∃ s', runBlock isa (xorWords w x) s = some s' ∧
      (∀ k < slots, slotW s' k = if k = w then slotW s x ^^^ slotW s w
        else if k = w + 1 then slotW s (x + 1) ^^^ slotW s (w + 1) else slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hw : w + 1 < slots := by rw [keySlot_eq] at hwk; rw [slots_eq]; omega_arith
  obtain hx : x + 1 < slots := by rw [keySlot_eq] at hxk; rw [slots_eq]; omega_arith
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := ldS_ok (k := x) t0 hb hal hscr (by omega_arith)
  obtain hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := ldS_ok (k := w) t1 hb₁ hal (by rw [wr₁]; exact hscr) (by omega_arith)
  obtain hb₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide), hb₁]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := eor_ok s₂ t0 t0 t1
  obtain hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), hb₂]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stS_slot (k := w) t0 hb₃ hal (by rw [wr₃, wr₂, wr₁]; exact hscr) (by omega_arith)
  obtain hb₄ : s₄.gpr sb = b := by rw [g₄, hb₃]
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅⟩ := ldS_ok (k := x + 1) t0 hb₄ hal
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact hscr) hxk
  obtain hb₅ : s₅.gpr sb = b := by rw [o₅ _ (by decide), hb₄]
  obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆⟩ := ldS_ok (k := w + 1) t1 hb₅ hal
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact hscr) hwk
  obtain hb₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), hb₅]
  obtain ⟨s₇, e₇, a₇, o₇, m₇, rd₇, wr₇⟩ := eor_ok s₆ t0 t0 t1
  obtain hb₇ : s₇.gpr sb = b := by rw [o₇ _ (by decide), hb₆]
  obtain ⟨s₈, e₈, m₈, g₈, rd₈, wr₈⟩ := stS_slot (k := w + 1) t0 hb₇ hal
    (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hscr) hwk
  obtain h₃ : ∀ k, slotW s₃ k = slotW s k := fun k => by
    rw [slotW_eq_of m₃ (hb₃.trans hb₂.symm), slotW_eq_of m₂ (hb₂.trans hb₁.symm),
      slotW_eq_of m₁ (hb₁.trans hb.symm)]
  obtain v₃ : s₃.gpr t0 = slotW s x ^^^ slotW s w := by
    rw [a₃, o₂ _ (by decide), a₁, a₂, slotW_eq_of m₁ (hb₁.trans hb.symm)]
  obtain h₄ : ∀ k < slots, slotW s₄ k = if k = w then slotW s x ^^^ slotW s w else slotW s k := fun k hk => by
    rw [slotW_store (by rw [m₄, hb₃]) g₄ hk (by omega_arith), v₃, h₃]
  obtain h₆ : ∀ k, slotW s₆ k = slotW s₄ k := fun k => by
    rw [slotW_eq_of m₆ (hb₆.trans hb₅.symm), slotW_eq_of m₅ (hb₅.trans hb₄.symm)]
  obtain v₇ : s₇.gpr t0 = slotW s₄ (x + 1) ^^^ slotW s₄ (w + 1) := by
    rw [a₇, o₆ _ (by decide), a₅, a₆, slotW_eq_of m₅ (hb₅.trans hb₄.symm)]
  refine ⟨s₈, ?_, fun k hk => ?_, fun r h0 h1 => ?_, ?_, by rw [rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show xorWords w x = [ldS t0 x] ++ ([ldS t1 w] ++ ([xorR t0 t0 t1] ++ ([stS w t0] ++
      ([ldS t0 (x + 1)] ++ ([ldS t1 (w + 1)] ++ ([xorR t0 t0 t1] ++ [stS (w + 1) t0])))))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some,
      runBlock_append', e₅, Option.bind_some, runBlock_append', e₆, Option.bind_some,
      runBlock_append', e₇, Option.bind_some, e₈]
  · rw [slotW_store (by rw [m₈, hb₇]) g₈ hk hw, v₇, slotW_eq_of m₇ (hb₇.trans hb₆.symm), h₆,
      h₄ (x + 1) hx, ite_eq_right hxw, h₄ (w + 1) hw, ite_eq_right (show ¬ w + 1 = w by omega_arith), h₄ k hk]
    exact ite_swap2 _ _ _
  · rw [g₈, o₇ r h0, o₆ r h1, o₅ r h0, g₄, o₃ r h0, o₂ r h1, o₁ r h0]
  · rw [m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
    exact (frame_slot _ (by omega_arith)).trans (frame_slot _ hw)

/-! ## The values -/


/-- The words at slots `k` and `k + 1` hold the halves `v`. -/
def WordsAt (s : State) (k : Nat) (v : BitVec 64 × BitVec 64) : Prop :=
  WordOf (slotW s k) v.1 ∧ WordOf (slotW s (k + 1)) v.2

theorem WordsAt.congr {s s' : State} {k : Nat} {v : BitVec 64 × BitVec 64} (h : WordsAt s k v)
    (h0 : slotW s' k = slotW s k) (h1 : slotW s' (k + 1) = slotW s (k + 1)) : WordsAt s' k v :=
  ⟨h.1.congr h0, h.2.congr h1⟩

theorem kaKb_slots : klSlot = 96 ∧ krSlot = 98 ∧ wSlot = 100 ∧ kaSlot = 102 ∧ kbSlot = 104 ∧
    savedSlot = 80 ∧ keySlot = 128 ∧ slots = 400 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `KeyCtx` moves to a state with the same base, regions, and slots below
the saved registers and from the table on. -/
theorem KeyCtx.of_slots {s s' : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s nk E)
    (hb : s'.gpr sb = s.gpr sb) (hwr : s'.wr = s.wr)
    (hs : ∀ k < slots, (k < savedSlot ∨ keySlot ≤ k) → slotW s' k = slotW s k) : KeyCtx s' nk E := by
  have h34 := hp.nk34
  refine hp.transfer hb hwr (fun kv hkv => ?_) (fun i hi j hj => ?_)
  · have := mask_lt hkv
    rw [hs _ (by rw [slots_eq]; rw [savedSlot_eq] at this; omega_arith) (Or.inl this)]; exact hp.masks kv hkv
  · have := hs (keySlot + 8 * i + j) (by rw [slots_eq, keySlot_eq]; omega_arith) (Or.inr (by omega_arith))
    simp only [slotW, hb, wordAddr] at this
    simp only [entryW]
    rw [show 8 * keySlot + 64 * i + 8 * j = 8 * (keySlot + 8 * i + j) by omega_arith]
    exact this

/-! ## The moves between the pairs -/

/-- What the moves keep: the slots but the running value's, `KA`'s and `KB`'s, and the registers but `t0`, `t1`. -/
structure MoveOk (s s' : State) : Prop where
  keep : ∀ k < slots, (k < wSlot ∨ kbSlot + 2 ≤ k) → slotW s' k = slotW s k
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem MoveOk.trans {s₁ s₂ s₃ : State} (h₁ : MoveOk s₁ s₂) (h₂ : MoveOk s₂ s₃) : MoveOk s₁ s₃ where
  keep k hk h := (h₂.keep k hk h).trans (h₁.keep k hk h)
  regs r h0 h1 := (h₂.regs r h0 h1).trans (h₁.regs r h0 h1)
  frame := by have := h₂.frame; rw [h₁.regs sb (by decide) (by decide)] at this; exact h₁.frame.trans this
  rd := h₂.rd.trans h₁.rd
  wr := h₂.wr.trans h₁.wr

/-- `copyWords w x`, for `w` the running value's, `KA`'s or `KB`'s slot. -/
theorem copyW_ok {s : State} {w x : Nat} (hal : (s.gpr sb).toNat % 8 = 0)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hw1 : wSlot ≤ w) (hw2 : w ≤ kbSlot) (hx : x + 1 < keySlot) (hxw : x + 1 ≠ w)
    {v : BitVec 64 × BitVec 64} (hv : WordsAt s x v) :
    ∃ s', runBlock isa (copyWords w x) s = some s' ∧ MoveOk s s' ∧ WordsAt s' w v ∧
      (∀ k < slots, k ≠ w → k ≠ w + 1 → slotW s' k = slotW s k) := by
  obtain ⟨k₁s, k₂s, k₃s, k₄s, k₅s, k₆s, k₇s, k₈s⟩ := kaKb_slots
  obtain ⟨s', e, hs, g, f, rd, wr⟩ := copyWords_ok rfl hal hscr (by omega_arith) hx hxw
  obtain hk : ∀ k < slots, k ≠ w → k ≠ w + 1 → slotW s' k = slotW s k := fun k hk h1 h2 => by
    rw [hs k hk, ite_eq_right h1, ite_eq_right h2]
  refine ⟨s', e, ⟨fun k hkk h => hk k hkk (by omega_arith) (by omega_arith), fun r h0 _ => g r h0, f, rd, wr⟩, ⟨?_, ?_⟩, hk⟩
  · rw [hs w (by omega_arith), ite_eq_left rfl]; exact hv.1
  · rw [hs (w + 1) (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left rfl]; exact hv.2

/-- `xorWords w x`, for `w` the running value's slot. -/
theorem xorW_ok {s : State} {x : Nat} (hal : (s.gpr sb).toNat % 8 = 0)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hx : x + 1 < keySlot) (hxw : x + 1 ≠ wSlot)
    {u v : BitVec 64 × BitVec 64} (hu : WordsAt s wSlot u) (hv : WordsAt s x v) :
    ∃ s', runBlock isa (xorWords wSlot x) s = some s' ∧ MoveOk s s' ∧
      WordsAt s' wSlot (u.1 ^^^ v.1, u.2 ^^^ v.2) ∧
      (∀ k < slots, k ≠ wSlot → k ≠ wSlot + 1 → slotW s' k = slotW s k) := by
  obtain ⟨k₁s, k₂s, k₃s, k₄s, k₅s, k₆s, k₇s, k₈s⟩ := kaKb_slots
  obtain ⟨s', e, hs, g, f, rd, wr⟩ := xorWords_ok rfl hal hscr (by omega_arith) hx hxw
  obtain hk : ∀ k < slots, k ≠ wSlot → k ≠ wSlot + 1 → slotW s' k = slotW s k := fun k hk h1 h2 => by
    rw [hs k hk, ite_eq_right h1, ite_eq_right h2]
  refine ⟨s', e, ⟨fun k hkk h => hk k hkk (by omega_arith) (by omega_arith), g, f, rd, wr⟩, ⟨?_, ?_⟩, hk⟩
  · rw [hs wSlot (by omega_arith), ite_eq_left rfl, BitVec.xor_comm]; exact hu.1.xor hv.1
  · rw [hs (wSlot + 1) (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left rfl, BitVec.xor_comm]
    exact hu.2.xor hv.2

/-! ## The loop -/

/-- What `kaKb` needs: the table of `Sigma1 … Sigma6`, `kp` at its start, and `KL` and `KR` in their slots. -/
structure KaPre (s₀ : State) (KL KR : BitVec 64 × BitVec 64) : Prop where
  ctx : KeyCtx s₀ 6 sigE
  kp : AtEntry s₀ (s₀.gpr sb) 0
  kl : WordsAt s₀ klSlot KL
  kr : WordsAt s₀ krSlot KR

/-- The loop's state: `kp` at entry `m`, `i` pairs done (`KA` after two,
`KB` after three), `c` in `r7`, the running value `W`. -/
structure KaInv (s₀ : State) (KL KR : BitVec 64 × BitVec 64) (m i c : Nat) (W : BitVec 64 × BitVec 64)
    (s : State) : Prop where
  ctx : KeyCtx s 6 sigE
  base : s.gpr sb = s₀.gpr sb
  ent : AtEntry s (s₀.gpr sb) m
  a0 : s.gpr .a0 = s₀.gpr sb + BitVec.ofNat 64 (8 * wSlot)
  cnt : s.gpr .a4 = BitVec.ofNat 64 c
  w : WordsAt s wSlot W
  ka : 2 ≤ i → WordsAt s kaSlot (kaD2 KL KR)
  kb : 3 ≤ i → WordsAt s kbSlot (kaD3 KL KR)
  keep : ∀ k, savedSlot ≤ k → k < slots → (k < wSlot ∨ kbSlot + 2 ≤ k) → slotW s k = slotW s₀ k
  regs : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a0 → r ≠ .a4 → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 8 * slots⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem KaInv.kl {s₀ s : State} {KL KR : BitVec 64 × BitVec 64} {m i c : Nat} {W : BitVec 64 × BitVec 64}
    (hp : KaPre s₀ KL KR) (h : KaInv s₀ KL KR m i c W s) : WordsAt s klSlot KL := by
  obtain ⟨k₁s, k₂s, k₃s, k₄s, k₅s, k₆s, k₇s, k₈s⟩ := kaKb_slots
  exact hp.kl.congr (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)) (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith))

theorem KaInv.kr {s₀ s : State} {KL KR : BitVec 64 × BitVec 64} {m i c : Nat} {W : BitVec 64 × BitVec 64}
    (hp : KaPre s₀ KL KR) (h : KaInv s₀ KL KR m i c W s) : WordsAt s krSlot KR := by
  obtain ⟨k₁s, k₂s, k₃s, k₄s, k₅s, k₆s, k₇s, k₈s⟩ := kaKb_slots
  exact hp.kr.congr (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)) (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith))

theorem t_layer : t0 ∈ sboxWrites ∧ t1 ∈ sboxWrites := by decide

theorem KaInv.move {s₀ s s' : State} {KL KR : BitVec 64 × BitVec 64} {m i i' c : Nat}
    {W W' : BitVec 64 × BitVec 64} (h : KaInv s₀ KL KR m i c W s) (hm : MoveOk s s')
    (hw : WordsAt s' wSlot W') (hka : 2 ≤ i' → WordsAt s' kaSlot (kaD2 KL KR))
    (hkb : 3 ≤ i' → WordsAt s' kbSlot (kaD3 KL KR)) : KaInv s₀ KL KR m i' c W' s' := by
  obtain ⟨k₁s, k₂s, k₃s, k₄s, k₅s, k₆s, k₇s, k₈s⟩ := kaKb_slots
  obtain hg : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    hm.regs r (fun e => hr (e ▸ t_layer.1)) (fun e => hr (e ▸ t_layer.2))
  refine ⟨h.ctx.of_slots (hg _ (by decide)) hm.wr
      (fun k hk h' => hm.keep k hk (by omega_arith)), (hg _ (by decide)).trans h.base,
    by rw [AtEntry, hg _ (by decide)]; exact h.ent,
    (hg _ (by decide)).trans h.a0, (hg _ (by decide)).trans h.cnt, hw, hka, hkb,
    fun k h1 h2 h3 => (hm.keep k h2 h3).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => (hg r h1).trans (h.regs r h1 h2 h3 h4),
    h.frame.trans ?_, hm.rd.trans h.rd, hm.wr.trans h.wr⟩
  have := hm.frame
  rw [h.base] at this
  exact this

/-- A step that writes only `r` (not `sb`, `kp` or `r3`). -/
theorem KaInv.regs1 {s₀ s s' : State} {KL KR : BitVec 64 × BitVec 64} {m i c c' : Nat}
    {W : BitVec 64 × BitVec 64} (h : KaInv s₀ KL KR m i c W s) {r₀ : Reg} (hr₀ : r₀ ∈ [t1, Reg.a4])
    (hg : ∀ r, r ≠ r₀ → s'.gpr r = s.gpr r)
    (hmem : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hc : s'.gpr .a4 = BitVec.ofNat 64 c') : KaInv s₀ KL KR m i c' W s' := by
  obtain hn : sb ≠ r₀ ∧ kp ≠ r₀ ∧ Reg.a0 ≠ r₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr₀; rcases hr₀ with rfl | rfl <;> decide
  obtain hs : ∀ k, slotW s' k = slotW s k := slotW_eq_of hmem (hg _ hn.1)
  refine ⟨h.ctx.of_slots (hg _ hn.1) hwr (fun k _ _ => hs k),
    (hg _ hn.1).trans h.base, by rw [AtEntry, hg _ hn.2.1]; exact h.ent, (hg _ hn.2.2).trans h.a0, hc,
    h.w.congr (hs _) (hs _), fun hi => (h.ka hi).congr (hs _) (hs _), fun hi => (h.kb hi).congr (hs _) (hs _),
    fun k h1 h2 h3 => (hs k).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => ?_, by rw [hmem]; exact h.frame,
    hrd.trans h.rd, hwr.trans h.wr⟩
  have : r ≠ r₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr₀
    rcases hr₀ with rfl | rfl
    · exact fun e => h1 (e ▸ t_layer.2)
    · exact h4
  exact (hg r this).trans (h.regs r h1 h2 h3 h4)

/-- A pair of rounds. -/
theorem KaInv.pair_ok {s₀ s : State} {KL KR : BitVec 64 × BitVec 64} {i c : Nat} {W : BitVec 64 × BitVec 64}
    (h : KaInv s₀ KL KR (2 * i) i c W s) (hi : i < 3) :
    ∃ s', runBlock isa pairPlain s = some s' ∧
      KaInv s₀ KL KR (2 * i + 2) i c (pair (sigE (2 * i)) (sigE (2 * i + 1)) W) s' := by
  obtain ⟨k₁s, k₂s, k₃s, k₄s, k₅s, k₆s, k₇s, k₈s⟩ := kaKb_slots
  obtain ⟨s', e, ctx', kp', regs', a0', w1, w2, keep', frame', rd', wr'⟩ :=
    pairPlain_ok h.ctx (by rw [h.base]; exact h.ent) (by omega_arith) (by rw [h.a0, h.base]) h.w.1 h.w.2
  have hr : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a0 → s'.gpr r = s.gpr r := regs'
  obtain hk : ∀ k, savedSlot ≤ k → k < slots → (k < wSlot ∨ kbSlot + 2 ≤ k ∨ k = kaSlot ∨ k = kaSlot + 1 ∨
      k = kbSlot ∨ k = kbSlot + 1) → slotW s' k = slotW s k := fun k h1 h2 h3 =>
    keep' k h1 h2 (by omega_arith) (by omega_arith)
  refine ⟨s', e, ⟨ctx', (hr _ (by decide) (by decide) (by decide)).trans h.base,
    by rw [h.base] at kp'; exact kp',
    a0'.trans h.a0, (hr _ (by decide) (by decide) (by decide)).trans h.cnt, ⟨w1, w2⟩,
    fun hi => (h.ka hi).congr (hk _ (by omega_arith) (by omega_arith) (by omega_arith)) (hk _ (by omega_arith) (by omega_arith) (by omega_arith)),
    fun hi => (h.kb hi).congr (hk _ (by omega_arith) (by omega_arith) (by omega_arith)) (hk _ (by omega_arith) (by omega_arith) (by omega_arith)),
    fun k h1 h2 h3 => (hk k h1 h2 (by omega_arith)).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => (hr r h1 h2 h3).trans (h.regs r h1 h2 h3 h4),
    h.frame.trans (by rw [h.base] at frame'; exact frame'), rd'.trans h.rd, wr'.trans h.wr⟩⟩

/-- `KL ^ KR` to the running value's slots, `r7 := 3`, `r3` at them. -/
theorem kaPrefix_ok {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KaPre s₀ KL KR) :
    ∃ s', runBlock isa (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++ ([.li .a4 3,
      .addi .a0 sb ((8 * wSlot : Nat) : Int)] : List Instr)) s₀ = some s' ∧
      KaInv s₀ KL KR 0 0 3 (kaW KL KR 0) s' := by
  obtain ⟨k₁s, k₂s, k₃s, k₄s, k₅s, k₆s, k₇s, k₈s⟩ := kaKb_slots
  obtain ⟨s₁, e₁, mv₁, w₁, -⟩ := copyW_ok (w := wSlot) (x := klSlot) hp.ctx.al hp.ctx.scr (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) hp.kl
  obtain hscr₁ : (⟨s₁.gpr sb, 8 * slots⟩ : Region) ∈ s₁.wr := by
    rw [mv₁.regs _ (by decide) (by decide), mv₁.wr]; exact hp.ctx.scr
  obtain ⟨s₂, e₂, mv₂, w₂, -⟩ := xorW_ok (by rw [mv₁.regs _ (by decide) (by decide)]; exact hp.ctx.al) hscr₁
    (by omega_arith) (by omega_arith) w₁
    (hp.kr.congr (mv₁.keep _ (by omega_arith) (Or.inl (by omega_arith))) (mv₁.keep _ (by omega_arith) (Or.inl (by omega_arith))))
  obtain mv := mv₁.trans mv₂
  obtain ⟨s₃, e₃, c₃, o₃, m₃, rd₃, wr₃⟩ := liN_ok s₂ .a4 3 (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addIc_ok s₃ .a0 sb (8 * wSlot) (by decide)
  obtain hg : ∀ r, r ≠ .a4 → r ≠ .a0 → s₅.gpr r = s₂.gpr r := fun r h1 h2 => by rw [o₅ r h2, o₃ r h1]
  obtain hb : s₅.gpr sb = s₀.gpr sb := by rw [hg _ (by decide) (by decide), mv.regs _ (by decide) (by decide)]
  obtain hs : ∀ k, slotW s₅ k = slotW s₂ k := slotW_eq_of (by rw [m₅, m₃]) (hg _ (by decide) (by decide))
  refine ⟨s₅, ?_, ⟨hp.ctx.of_slots hb (by rw [wr₅, wr₃, mv.wr])
      (fun k hk h' => by rw [hs, mv.keep k hk (by omega_arith)]), hb, ?_, ?_,
    (o₅ _ (by decide)).trans c₃, w₂.congr (hs _) (hs _),
    fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun k _ h2 h3 => by rw [hs, mv.keep k h2 h3],
    fun r h1 _ h3 h4 => by
      rw [hg r h4 h3, mv.regs r (fun e => h1 (e ▸ t_layer.1)) (fun e => h1 (e ▸ t_layer.2))], ?_,
    by rw [rd₅, rd₃, mv.rd], by rw [wr₅, wr₃, mv.wr]⟩⟩
  · rw [runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some,
      show ([.li .a4 3, .addi .a0 sb ((8 * wSlot : Nat) : Int)] : List Instr) =
        [.li .a4 3] ++ [.addi .a0 sb ((8 * wSlot : Nat) : Int)] from rfl,
      runBlock_append', e₃, Option.bind_some, e₅]
  · rw [AtEntry, hg _ (by decide) (by decide), mv.regs _ (by decide) (by decide)]; exact hp.kp
  · rw [r₅, o₃ _ (by decide), mv.regs _ (by decide) (by decide)]
  · rw [m₅, m₃]; exact mv.frame

/-- `kaKb`: the three pairs, leaving `KA` and `KB` in their slots. -/
theorem kaKb_wp {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KaPre s₀ KL KR) :
    WP isa kaKb s₀ (KaInv s₀ KL KR 6 3 0 (kaD3 KL KR)) := by
  obtain ⟨k₁s, k₂s, k₃s, k₄s, k₅s, k₆s, k₇s, k₈s⟩ := kaKb_slots
  unfold kaKb
  refine WP.seq (WP.mono (WP.of_runBlock (kaPrefix_ok hp)) fun s h => ?_)
  refine WP.loop (M := isa)
    (fun n s => ∃ i, n = 3 - i ∧ i < 3 ∧ KaInv s₀ KL KR (2 * i) i (3 - i) (kaW KL KR i) s)
    (fun n s hs => ?_) 3 s ⟨0, rfl, by decide, h⟩
  obtain ⟨i, rfl, hi, hI⟩ := hs
  obtain ⟨s₁, e₁, h₁⟩ := hI.pair_ok hi
  -- `t1 := r7 >>> 1`.
  let s₂ := s₁.write t1 (s₁.gpr .a4 >>> 1)
  obtain e₂ : runBlock isa [shrI t1 .a4 1] s₁ = some s₂ := by
    simp only [shrI, runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 1 < 64 by decide)]; rfl
  obtain t₂ : s₂.gpr t1 = BitVec.ofNat 64 (3 - i) >>> 1 := by
    rw [RegUpd.gpr_write_self, h₁.cnt]
  obtain h₂ := h₁.regs1 (s' := s₂) (r₀ := t1) (by simp) (fun r hr => RegUpd.gpr_write_of_ne _ _ hr) rfl rfl rfl
    ((RegUpd.gpr_write_of_ne s₁ (s₁.gpr .a4 >>> 1) (show Reg.a4 ≠ t1 by decide)).trans h₁.cnt)
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append', e₁, Option.bind_some, e₂], ?_⟩)
  refine WP.seq (WP.mono (Q := KaInv s₀ KL KR (2 * i + 2) (i + 1) (3 - i) (kaW KL KR (i + 1))) ?_
    fun s₃ h₃ => ?_)
  · have ht : (s₂.gpr t1 == 0) = decide (2 ≤ i) := by
      rw [t₂]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_arith) with rfl | rfl | rfl <;> decide
    refine WP.ite (decide (i ≤ 1)) ((eval_nonzero s₂ t1).trans (by rw [ht]; by_cases h : i ≤ 1 <;> simp [h] <;> omega_arith))
      (fun ht => ?_) (fun hf => ?_)
    · have hi1 : i ≤ 1 := by simpa using ht
      obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := subI_ok s₂ t1 .a4 3 (by decide)
      obtain h₃ := h₂.regs1 (r₀ := t1) (by simp) o₃ m₃ rd₃ wr₃ (by rw [o₃ _ (by decide)]; exact h₂.cnt)
      obtain hz : (s₃.gpr t1 == 0) = decide (i = 0) := by
        rw [r₃, h₂.cnt]
        rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl <;> decide
      refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
      refine WP.ite (decide (i = 0)) ((eval_zero s₃ t1).trans (by rw [hz])) (fun h0 => ?_) (fun h0 => ?_)
      · obtain rfl : i = 0 := by simpa using h0
        obtain ⟨s₄, e₄, mv₄, w₄, -⟩ := xorW_ok h₃.ctx.al h₃.ctx.scr (by omega_arith) (by omega_arith) h₃.w (h₃.kl hp)
        exact WP.of_runBlock ⟨s₄, e₄, h₃.move mv₄ w₄ (fun h => absurd h (by decide))
          (fun h => absurd h (by decide))⟩
      · obtain rfl : i = 1 := by simp at h0; omega_arith
        obtain ⟨s₄, e₄, mv₄, w₄, o₄⟩ := copyW_ok (w := kaSlot) (x := wSlot) h₃.ctx.al h₃.ctx.scr (by omega_arith) (by omega_arith)
          (by omega_arith) (by omega_arith) h₃.w
        obtain hscr₄ : (⟨s₄.gpr sb, 8 * slots⟩ : Region) ∈ s₄.wr := by
          rw [mv₄.regs _ (by decide) (by decide), mv₄.wr]; exact h₃.ctx.scr
        obtain ⟨s₅, e₅, mv₅, w₅, o₅⟩ := xorW_ok (by rw [mv₄.regs _ (by decide) (by decide)]; exact h₃.ctx.al) hscr₄ (by omega_arith) (by omega_arith)
          (h₃.w.congr (o₄ _ (by omega_arith) (by omega_arith) (by omega_arith)) (o₄ _ (by omega_arith) (by omega_arith) (by omega_arith)))
          ((h₃.kr hp).congr (mv₄.keep _ (by omega_arith) (Or.inl (by omega_arith)))
            (mv₄.keep _ (by omega_arith) (Or.inl (by omega_arith))))
        refine WP.of_runBlock ⟨s₅, by rw [runBlock_append', e₄, Option.bind_some, e₅],
          h₃.move (mv₄.trans mv₅) w₅ (fun _ => w₄.congr (o₅ _ (by omega_arith) (by omega_arith) (by omega_arith))
            (o₅ _ (by omega_arith) (by omega_arith) (by omega_arith))) (fun h => absurd h (by decide))⟩
    · obtain rfl : i = 2 := by simp at hf; omega_arith
      obtain ⟨s₃, e₃, mv₃, w₃, o₃⟩ := copyW_ok (w := kbSlot) (x := wSlot) h₂.ctx.al h₂.ctx.scr (by omega_arith) (by omega_arith)
        (by omega_arith) (by omega_arith) h₂.w
      exact WP.of_runBlock ⟨s₃, e₃, h₂.move mv₃
        (h₂.w.congr (o₃ _ (by omega_arith) (by omega_arith) (by omega_arith)) (o₃ _ (by omega_arith) (by omega_arith) (by omega_arith)))
        (fun _ => (h₂.ka (by decide)).congr (o₃ _ (by omega_arith) (by omega_arith) (by omega_arith))
          (o₃ _ (by omega_arith) (by omega_arith) (by omega_arith))) (fun _ => w₃)⟩
  · obtain ⟨s₄, e₄, c₄, o₄, m₄, rd₄, wr₄⟩ := subI_ok s₃ .a4 .a4 1 (by decide)
    obtain hsub : s₃.gpr .a4 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (3 - (i + 1)) := by
      rw [h₃.cnt, VG.Offset.ofNat_sub_ofNat (by omega_arith), show 3 - i - 1 = 3 - (i + 1) by omega_arith]
    obtain h₄ := h₃.regs1 (r₀ := .a4) (by simp) o₄ m₄ rd₄ wr₄ (by rw [c₄, hsub])
    obtain hz : (s₄.gpr .a4 == 0) = decide (3 - (i + 1) = 0) := by
      rw [c₄, hsub, ofNat_beq_zero (by omega_arith)]
    refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
    by_cases hl : i + 1 = 3
    · obtain rfl : i = 2 := by omega_arith
      exact .inl ⟨(eval_nonzero s₄ .a4).trans (by rw [hz]; rfl), h₄⟩
    · exact .inr ⟨(eval_nonzero s₄ .a4).trans (by rw [hz]; simp; omega_arith), 3 - (i + 1), by omega_arith, i + 1, rfl,
        by omega_arith, by rw [Nat.mul_add, Nat.mul_one]; exact h₄⟩

end VG.Proof.Camellia.RISCV64
