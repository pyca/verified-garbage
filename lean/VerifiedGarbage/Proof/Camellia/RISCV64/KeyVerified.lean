module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Prologue
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Camellia.RISCV64.Group
public import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Camellia.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Camellia.Bitsliced
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Proof.Camellia.RISCV64.KeyContract
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Camellia.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Camellia.RISCV64.Linear

/-! ### `Camellia.RISCV64.KaKb`, which only this module used -/

section

/-! ### `Camellia.RISCV64.KeyPair`, which this module and modules that import it used -/

section

/-! ### `Camellia.RISCV64.KeyChecks2`, which only this module used -/

section

/-!
# The key schedule's evaluated facts on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyVerified.lean`): `spread d`, which
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

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyVerified.lean`): `pairPlain_ok`: with the running value's halves as words at
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

end

end

/-! ### `Camellia.RISCV64.KeyStore`, which only this module used -/

section

/-!
# Storing the subkeys on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyVerified.lean`). The key schedule
keeps the 64-bit halves of `KL`, `KR`, `KA` and `KB` as ECB loads them:
little-endian words of their big-endian bytes (`WordOf`), whose bytes read
big-endian (`loadBE64`) are the halves as numbers (`be64_of_wordOf`).

`storeSubkeys_ok`: with the halves of `KL`, `KR`, `KA` and `KB` in their
registers (`hiReg`, `loReg`), `storeSubkeys ks` stores each subkey of `ks`,
the half of a rotation (`rotHalf`), big-endian a byte at a time
(`storeBE`), at its word of the schedule at `a2`.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.Impl.Camellia.RISCV64 VG.WriteBytes VG.Impl.Words.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR shlI shrI)

/-! ## Halves as little-endian words -/

/-- A word is its bytes, the most significant first. -/
theorem bytes_concat (H : BitVec 64) :
    H = Camellia.byteOf H 0 ++ Camellia.byteOf H 1 ++ Camellia.byteOf H 2 ++ Camellia.byteOf H 3 ++
      Camellia.byteOf H 4 ++ Camellia.byteOf H 5 ++ Camellia.byteOf H 6 ++ Camellia.byteOf H 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [Camellia.byteOf, BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  repeat' split
  all_goals (rw [decide_eq_true (by omega_arith), Bool.true_and]; congr 1; omega_arith)

/-- The bytes of such a word, read big-endian, are the half. -/
theorem be64_of_wordOf {m : Mem} {p : Addr} {off : Nat} {H : BitVec 64}
    (hw : WordOf (m.readW (p + BitVec.ofNat 64 off) 64) H) : ByteLoad.be64 m p off = H := by
  have hb : ∀ i < 8, m (p + BitVec.ofNat 64 (off + i)) = Camellia.byteOf H i := fun i hi =>
    BitVec.eq_of_getLsbD_eq fun j hj => by
      rw [← hw i hi j hj, Camellia.readW64_bit _ _ hi hj, Offset.add_add]
  have h0 := hb 0 (by decide)
  rw [Nat.add_zero] at h0
  rw [ByteLoad.be64, h0, hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
    hb 5 (by decide), hb 6 (by decide), hb 7 (by decide)]
  exact (bytes_concat H).symm

/-- Byte `j` of a word stored big-endian is byte `j` of the word, the most significant first. -/
theorem writeBytes_be_byte (m : Mem) (a : Addr) (w : BitVec 64) {j : Nat} (hj : j < 8) :
    writeBytes m a (ByteLoad.beBytes 8 w) (a + BitVec.ofNat 64 j) = Camellia.byteOf w j := by
  simp only [writeBytes, ByteLoad.beBytes_length, Mem.sub_ofNat_toNat a (show j < 2 ^ 64 by omega_using [hj]), hj,
    ↓reduceIte]
  simp only [ByteLoad.beBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Camellia.byteOf]
  rw [show 8 * (8 - 1 - j) = 56 - 8 * j by omega_using []]

/-! ## Single instructions -/

theorem shift_ok (s : State) (left : Bool) (d n : Reg) {sh : Nat} (h : sh < 64) :
    ∃ s', runBlock isa [if left then shlI d n sh else shrI d n sh] s = some s' ∧
      s'.gpr d = (if left then s.gpr n <<< sh else s.gpr n >>> sh) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases left
  · exact ⟨s.write d (s.gpr n >>> sh), by
      simp only [Bool.false_eq_true, ↓reduceIte, shrI, runBlock_cons, exec_shift_d h, runStep_some, runBlock_nil],
      RegUpd.gpr_write_self _ _ _, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩
  · exact ⟨s.write d (s.gpr n <<< sh), by
      simp only [↓reduceIte, shlI, runBlock_cons, exec_shift_d h, runStep_some, runBlock_nil],
      RegUpd.gpr_write_self _ _ _, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

theorem orr_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [orR d n m] s = some s' ∧ s'.gpr d = s.gpr n ||| s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (s.gpr n ||| s.gpr m), by
    simp only [orR, runBlock_cons, runStep_some, runBlock_nil, exec_logic],
    RegUpd.gpr_write_self _ _ _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- `storeBE 8 t0 t1 a2 d`: `t0` big-endian at `d(a2)`. -/
theorem strBE_ok (s : State) {d : Nat} (hd : d + 8 ≤ 2048)
    (hw : InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (storeBE 8 t0 t1 .a2 d) s = some s' ∧
      s'.mem = writeBytes s.mem (s.gpr .a2 + BitVec.ofNat 64 d) (ByteLoad.beBytes 8 (s.gpr t0)) ∧
      (∀ r, r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e', h'⟩ := WP.runBlock_of (ByteLoad.storeBE_ok (s := s) (v := t0) (tmp := t1) (n := .a2) (off := d)
    (w := 8) (by decide) (by decide) (by decide) (by decide) hd (fun j hj => ByteLoad.in_byte' hw hj))
  subst h'
  exact ⟨_, e', rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl⟩

/-! ## The subkeys -/

theorem hiReg_ne : ∀ v < 4, hiReg v ≠ t0 ∧ hiReg v ≠ t1 ∧ loReg v ≠ t0 ∧ loReg v ≠ t1 := by decide

/-- One subkey, stored big-endian at word `i` of `a2`. -/
theorem subkey_ok (s : State) {i v r : Nat} {hi : Bool} (hv : v < 4) (hi34 : i < 34)
    (hw : InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 (8 * i)) 8) :
    ∃ s', runBlock isa (subkey i v r hi) s = some s' ∧
      s'.mem = writeBytes s.mem (s.gpr .a2 + BitVec.ofNat 64 (8 * i))
        (ByteLoad.beBytes 8 (Camellia.rotHalf (s.gpr (hiReg v)) (s.gpr (loReg v)) r hi)) ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨n1, n2, n3, n4⟩ := hiReg_ne v hv
  have hr3 : Reg.a2 ≠ t0 := by decide
  have hx1 : Reg.a2 ≠ t1 := by decide
  have hd : 8 * i + 8 ≤ 2048 := by omega_arith
  -- The two halves, `a` first.
  let a := if (r < 64) = (hi = true) then hiReg v else loReg v
  let b := if (r < 64) = (hi = true) then loReg v else hiReg v
  have ha : a ≠ t0 ∧ a ≠ t1 := by simp only [a]; split <;> exact ⟨by assumption, by assumption⟩
  have hb : b ≠ t0 ∧ b ≠ t1 := by simp only [b]; split <;> exact ⟨by assumption, by assumption⟩
  have hrot : Camellia.rotHalf (s.gpr (hiReg v)) (s.gpr (loReg v)) r hi =
      if r % 64 = 0 then s.gpr a else (s.gpr a <<< (r % 64)) ||| (s.gpr b >>> (64 - r % 64)) := by
    by_cases h64 : r < 64 <;> cases hi <;> simp [Camellia.rotHalf, a, b, h64]
  have hcode : subkey i v r hi =
      (if r % 64 = 0 then [movR t0 a] else [shlI t0 a (r % 64), shrI t1 b (64 - r % 64), orR t0 t0 t1]) ++
        storeBE 8 t0 t1 .a2 (8 * i) := by
    by_cases h64 : r < 64 <;> cases hi <;> simp [subkey, a, b, h64]
  by_cases h0 : r % 64 = 0
  · obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s t0 a
    obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := strBE_ok s₁ hd (by rw [wr₁, o₁ _ hr3]; exact hw)
    refine ⟨s₃, by rw [hcode, ite_eq_left h0, runBlock_append', e₁, Option.bind_some, e₃], ?_, ?_, ?_, ?_⟩
    · rw [m₃, m₁, o₁ _ hr3, r₁, hrot, ite_eq_left h0]
    · intro r' h1 h2; rw [g₃ _ h2, o₁ _ h1]
    · rw [rd₃, rd₁]
    · rw [wr₃, wr₁]
  · obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := shift_ok s true t0 a (sh := r % 64) (by omega_arith)
    obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := shift_ok s₁ false t1 b (sh := 64 - r % 64) (by omega_arith)
    obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := orr_ok s₂ t0 t0 t1
    have g₃ : ∀ r', r' ≠ t0 → r' ≠ t1 → s₃.gpr r' = s.gpr r' := fun r' h1 h2 => by
      rw [o₃ _ h1, o₂ _ h2, o₁ _ h1]
    obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅⟩ := strBE_ok s₃ hd (by rw [wr₃, wr₂, wr₁, g₃ _ hr3 hx1]; exact hw)
    refine ⟨s₅, by
      rw [hcode, ite_eq_right h0, show ([shlI t0 a (r % 64), shrI t1 b (64 - r % 64), orR t0 t0 t1] :
          List Instr) = [if true then shlI t0 a (r % 64) else shrI t0 a (r % 64)] ++
          ([if false then shlI t1 b (64 - r % 64) else shrI t1 b (64 - r % 64)] ++ [orR t0 t0 t1]) from rfl,
        runBlock_append', runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some, e₃,
        Option.bind_some, e₅], ?_, ?_, ?_, ?_⟩
    · have v0 : s₂.gpr t0 = s.gpr a <<< (r % 64) := by
        rw [o₂ _ (by decide : t0 ≠ t1), r₁]; rfl
      have v1 : s₂.gpr t1 = s.gpr b >>> (64 - r % 64) := by
        rw [r₂, o₁ _ hb.1]; rfl
      rw [m₅, m₃, m₂, m₁, g₃ _ hr3 hx1, r₃, v0, v1, hrot, ite_eq_right h0]
    · intro r' h1 h2; rw [g₅ _ h2, g₃ _ h1 h2]
    · rw [rd₅, rd₃, rd₂, rd₁]
    · rw [wr₅, wr₃, wr₂, wr₁]

theorem q_ne_t (n : Nat) : q n ≠ t0 ∧ q n ≠ t1 := by
  unfold q; split <;> decide

theorem regs_ne_t (x : Nat) : hiReg x ≠ t0 ∧ hiReg x ≠ t1 ∧ loReg x ≠ t0 ∧ loReg x ≠ t1 :=
  ⟨(q_ne_t _).1, (q_ne_t _).2, (q_ne_t _).1, (q_ne_t _).2⟩

/-- The subkey words `ks` from word `n` of `a2` on. -/
theorem storeSubkeys_ok (ks : List (Nat × Nat × Bool)) (hv : ∀ k ∈ ks, k.1 < 4) :
    ∀ (n : Nat) (s : State), (∀ i < ks.length, InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 (8 * (n + i))) 8) →
      n + ks.length ≤ 34 →
    ∃ s', runBlock isa ((ks.zipIdx n).flatMap fun ((v, r, hi), i) => subkey i v r hi) s = some s' ∧
      (∀ i < ks.length, ∀ j < 8,
        s'.mem (s.gpr .a2 + BitVec.ofNat 64 (8 * (n + i) + j)) =
          Camellia.byteOf (Camellia.rotHalf (s.gpr (hiReg (ks.getD i (0, 0, true)).1))
            (s.gpr (loReg (ks.getD i (0, 0, true)).1)) (ks.getD i (0, 0, true)).2.1
            (ks.getD i (0, 0, true)).2.2) j) ∧
      Frame [⟨s.gpr .a2 + BitVec.ofNat 64 (8 * n), 8 * ks.length⟩] s.mem s'.mem ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction ks with
  | nil => intro n s _ _; exact ⟨s, rfl, fun i hi => by simp at hi, Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl⟩
  | cons k ks ih =>
    intro n s hw hfit
    obtain ⟨v, r, hi⟩ := k
    have hv0 : v < 4 := hv _ List.mem_cons_self
    simp only [List.length_cons] at hfit
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := subkey_ok s (i := n) (r := r) (hi := hi) hv0 (by omega_arith)
      (by simpa using hw 0 (by simp))
    have hx2 : s₁.gpr .a2 = s.gpr .a2 := g₁ _ (by decide) (by decide)
    obtain ⟨s', e', b', f', g', rd', wr'⟩ := ih (fun k hk => hv k (List.mem_cons_of_mem _ hk)) (n + 1) s₁
      (fun i hi => by
        rw [wr₁, hx2, show n + 1 + i = n + (i + 1) by omega_arith]
        exact hw (i + 1) (by simp; omega_arith)) (by omega_arith)
    refine ⟨s', by
      rw [List.zipIdx_cons, List.flatMap_cons, runBlock_append', e₁, Option.bind_some]; exact e',
      fun i hi j hj => ?_, ?_, fun r' h1 h2 => by rw [g' r' h1 h2, g₁ r' h1 h2], by rw [rd', rd₁],
      by rw [wr', wr₁]⟩
    · cases i with
      | zero =>
        have hout : ∀ R ∈ [(⟨s₁.gpr .a2 + BitVec.ofNat 64 (8 * (n + 1)), 8 * ks.length⟩ : Region)],
            ¬ R.Contains (s.gpr .a2 + BitVec.ofNat 64 (8 * (n + 0) + j)) 1 := fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR; rw [hx2]
          by_cases h0 : ks.length = 0
          · simp only [Region.Contains, h0]; omega_arith
          · exact not_contains_off _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)
        rw [f' _ hout, m₁, Nat.add_zero, ← Offset.add_add, writeBytes_be_byte _ _ _ hj]
        simp only [List.getD_cons_zero]
      | succ i =>
        have := b' i (by simp at hi; omega_arith) j hj
        simp only [hx2, g₁ _ (regs_ne_t _).1 (regs_ne_t _).2.1,
          g₁ _ (regs_ne_t _).2.2.1 (regs_ne_t _).2.2.2] at this
        rw [show n + (i + 1) = n + 1 + i by omega_arith, this, List.getD_cons_succ]
    · have f₁ : Frame [⟨s.gpr .a2 + BitVec.ofNat 64 (8 * n), 8 * ((v, r, hi) :: ks).length⟩] s.mem s₁.mem := by
        rw [m₁]; exact writeBytes_frame _ _ _ (by
          simp only [ByteLoad.beBytes_length, List.length_cons]
          simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)
      refine f₁.trans (f'.sub fun R hR => ⟨_, List.mem_singleton_self _, ?_⟩)
      simp only [List.mem_singleton] at hR; subst hR
      rw [hx2]
      exact VG.Offset.sub _ (by omega_arith) (by simp; omega_arith)

end VG.Proof.Camellia.RISCV64

end

end

/-! ### `Camellia.RISCV64.ExpandKey`, which only this module used -/

section

/-! ### `Camellia.RISCV64.KeySetup`, which only this module used -/

section

/-!
# The Camellia key schedule on RISC-V: its parts

As on PPC64LE (`Proof/Camellia/PPC64LE/KeySetup.lean`): the prologue saves
the callee-saved registers, sets the masks and stores the planes of
`Sigma1 … Sigma6` as a table of subkeys (`ekPrologue_ok`; each plane built
by `movImm64` and stored: `sigmaStores_ok`); `loadKey_wp` copies `KL` and
`KR` into their slots a byte at a time, and `loadValues_ok` reads the four
values big-endian into registers.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 t2 u7 kp movR ldS stS xorR notR)
open VG.Proof.Camellia (HalfRel pair hiW loW pos)

/-! ## Single instructions -/

/-- `sd r, 8 k(sb)`, as slots. -/
theorem st_ok {s : State} {k : Nat} (r : Reg) (hal : (s.gpr sb).toNat % 8 = 0)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < keySlot) :
    ∃ s', runBlock isa [stS k r] s = some s' ∧ slotW s' k = s.gpr r ∧
      (∀ j < slots, j ≠ k → slotW s' j = slotW s j) ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hk' : k < slots := by rw [keySlot_eq] at hk; rw [slots_eq]; omega_arith
  obtain ⟨s', e, m, g, rd, wr⟩ := stS_slot (k := k) r rfl hal hscr hk
  refine ⟨s', e, ?_, fun j hj hjk => ?_, g, by rw [m]; exact frame_slot _ hk', rd, wr⟩
  · rw [slotW_store m g hk' hk', ite_eq_left rfl]
  · rw [slotW_store m g hj hk', ite_eq_right hjk]

/-! ## The table of `Sigma1 … Sigma6` -/

/-- Plane `j` of the constant `x`, built in `t0` and stored to the entry at `kp`. -/
def sigmaStore (x : BitVec 64) (j : Nat) : List Instr :=
  Impl.Words64.RISCV64.movImm64 t0 t1 (keyPlane x j) ++ [.store .d t0 kp (8 * j)]

theorem sigmaOne_eq (x : BitVec 64) :
    sigmaOne x = (List.range 8).flatMap (sigmaStore x) ++ ([.addi kp kp 64] : List Instr) := rfl

/-- The planes stored so far. -/
structure SigInv (x : BitVec 64) (s : State) (n : Nat) (s' : State) : Prop where
  planes : ∀ j < n, s'.mem.readW (wordAddr (s.gpr kp) j) 64 = keyPlane x j
  frame : Frame [⟨s.gpr kp, 64⟩] s.mem s'.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The stores of `sigmaOne x`: the planes of `x` to the entry at `kp`. -/
theorem sigmaStores_ok (x : BitVec 64) (s : State) (hal : (s.gpr kp).toNat % 8 = 0)
    (hw : ∀ j < 8, InRegions s.wr (s.gpr kp + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa ((List.range 8).flatMap (sigmaStore x)) s = some s' ∧ SigInv x s 8 s' := by
  refine WP.runBlock_of (wp_range_flatMap (M := isa) (SigInv x s) (fun k s₁ hk h => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_using []), Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl⟩)
  rw [sigmaStore, WP.block_append_iff (M := isa)]
  refine WP.mono (Words64.movImm64_ok (s := s₁) (d := t0) (tmp := t1) (by decide) (keyPlane x k))
    fun s₂ ⟨v₂, g₂, m₂, rd₂, wr₂, _⟩ => ?_
  obtain hkp : s₂.gpr kp = s.gpr kp := by rw [g₂ _ (by decide) (by decide), h.regs _ (by decide) (by decide)]
  refine Steps.wp_sd (a := wordAddr (s.gpr kp) k) (by omega_using [hk]) (by rw [hkp])
    (Spill.al8 hal (by omega_using [])) (by rw [wr₂, h.wr]; exact hw k hk) fun s₃ u₃ => WP.block_nil ?_
  obtain hm₃ : s₃.mem = s₁.mem.writeW (wordAddr (s.gpr kp) k) (keyPlane x k) := by rw [u₃.mem, m₂, v₂]
  refine ⟨fun j hj => ?_, ?_, fun r h0 h1 => by rw [u₃.gpr, g₂ r h0 h1, h.regs r h0 h1],
    by rw [u₃.rd, rd₂, h.rd], by rw [u₃.wr, wr₂, h.wr]⟩
  · rw [hm₃]
    by_cases hjk : j = k
    · subst hjk; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (slot_sep _ (by omega_using [hk, hj]) (by omega_using [hk]) hjk) (by decide)]
      exact h.planes j (by omega_using [hj, hjk])
  · rw [hm₃]
    exact h.frame.trans (frame_writeW _ (by rw [wordAddr]; exact VG.Offset.sub_base _ (by omega_using [hk])))

/-- `sigmaOne x`: the planes of `x` to the entry at `kp`, and `kp` to the next. -/
theorem sigmaOne_ok (x : BitVec 64) (s : State) (hal : (s.gpr kp).toNat % 8 = 0)
    (hw : ∀ j < 8, InRegions s.wr (s.gpr kp + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (sigmaOne x) s = some s' ∧
      (∀ j < 8, s'.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * j)) 64 = keyPlane x j) ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 ∧ Frame [⟨s.gpr kp, 64⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, h₁⟩ := sigmaStores_ok x s hal hw
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 64 (by decide)
  refine ⟨s₂, by rw [sigmaOne_eq, runBlock_append', e₁, Option.bind_some, e₂], fun j hj => by
      rw [m₂]; exact h₁.planes j hj,
    by rw [a₂, h₁.regs _ (by decide) (by decide)], by rw [m₂]; exact h₁.frame,
    fun r h0 h1 h2 => by rw [o₂ r h2, h₁.regs r h0 h1], by rw [rd₂, h₁.rd], by rw [wr₂, h₁.wr]⟩

theorem sigmaList_ok {b : Addr} (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) (hal : b.toNat % 8 = 0) :
    ∀ (xs : List (BitVec 64)) (e : Nat) (s : State), (⟨b, 8 * slots⟩ : Region) ∈ s.wr →
      s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e) → e + xs.length ≤ 34 →
      ∃ s', runBlock isa (xs.flatMap sigmaOne) s = some s' ∧
        (∀ i < xs.length, ∀ j < 8, entryW s'.mem b (e + i) j = keyPlane (xs.getD i 0) j) ∧
        Frame [⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64 * xs.length⟩] s.mem s'.mem ∧
        s'.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e + xs.length)) ∧
        (∀ r, r ≠ t0 → r ≠ t1 → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], e, s, _, hr, _ => ⟨s, rfl, fun i hi => absurd hi (by simp), Frame.refl _ _, by simpa using hr,
      fun _ _ _ _ => rfl, rfl, rfl⟩
  | x :: xs, e, s, hscr, hr, hl => by
    rw [slots_eq] at hfit
    have hk := keySlot_eq
    simp only [List.length_cons] at hl
    obtain ⟨s₁, e₁, v₁, r₁, f₁, g₁, rd₁, wr₁⟩ := sigmaOne_ok x s (by rw [hr]; exact Spill.al8 hal (by omega_arith))
      (fun j hj => ⟨_, hscr, by
        rw [hr, Offset.add_add]
        exact VG.Offset.contains_base _ (by rw [slots_eq]; omega_arith) (by omega_arith)⟩)
    obtain ⟨s', e', v', f', r', g', rd', wr'⟩ := sigmaList_ok hfit hal xs (e + 1) s₁
      (by rw [wr₁]; exact hscr)
      (by rw [r₁, hr, Offset.add_add, show 8 * keySlot + 64 * e + 64 = 8 * keySlot + 64 * (e + 1) by omega_arith])
      (by omega_arith)
    refine ⟨s', by rw [List.flatMap_cons, runBlock_append', e₁, Option.bind_some, e'], fun i hi j hj => ?_,
      ?_, by rw [r', List.length_cons, show e + 1 + xs.length = e + (xs.length + 1) by omega_arith],
      fun r h0 h1 h2 => by rw [g' r h0 h1 h2, g₁ r h0 h1 h2], by rw [rd', rd₁], by rw [wr', wr₁]⟩
    · rcases i with _ | i
      · rw [entryW, Nat.add_zero, ← Offset.add_add, ← hr]
        refine (f'.readW (Region.contains_self _ _) (fun r hr' => ?_) (by decide)).trans (v₁ j hj)
        simp only [List.mem_singleton] at hr'; subst hr'
        rw [hr, Offset.add_add]
        exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
      · rw [show e + (i + 1) = e + 1 + i by omega_arith]
        exact v' i (by simpa using hi) j hj
    · refine Frame.trans (f₁.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩)
        (f'.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
        (simp only [List.mem_singleton] at hr'; subst hr')
      · rw [hr]; exact Region.sub_prefix (by simp only [List.length_cons]; omega_arith)
      · exact VG.Offset.sub b (by omega_arith) (by simp only [List.length_cons]; omega_arith)

/-- The table's entries `0 … 5` hold `Sigma1 … Sigma6`, as `KeyCtx` reads them. -/
theorem sigmas_rel {m : Mem} {b : Addr}
    (h : ∀ i < 6, ∀ j < 8, entryW m b i j = keyPlane (sigmas.getD i 0) j) :
    ∀ i < 6, HalfRel (entryW m b i) fun _ => sigE i := fun i hi bb hb c hc j hj => by
  rw [h i hi j hj]; exact sigma_planes _ hb hc hj

/-! ## Loading the key -/

/-- Eight bytes copied: the word they make, in the order ECB loads it. -/
theorem wordOf_copy {m m' : Mem} {a b : Addr} (h : ∀ i < 8, m' (b + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) :
    WordOf (m'.readW b 64) (Spec.Camellia.wordAt m a) := fun i hi j hj => by
  rw [Camellia.readW64_bit m' b hi hj, h i hi, Camellia.byteOf_wordAt m a hi]

/-- A step that writes only `t0` and `t1`. -/
structure Pure (s s' : State) : Prop where
  mem : s'.mem = s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- What a part of `loadKey` keeps: the slots but those of `KL` and `KR`,
the registers but `t0` and `t1`. -/
structure LkKeep (s s' : State) : Prop where
  keep : ∀ k < slots, (k < klSlot ∨ krSlot + 2 ≤ k) → slotW s' k = slotW s k
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem LkKeep.trans {s₁ s₂ s₃ : State} (h₁ : LkKeep s₁ s₂) (h₂ : LkKeep s₂ s₃) : LkKeep s₁ s₃ where
  keep k hk h := (h₂.keep k hk h).trans (h₁.keep k hk h)
  regs r h0 h1 := (h₂.regs r h0 h1).trans (h₁.regs r h0 h1)
  frame := h₁.frame.trans (by have := h₂.frame; rw [h₁.regs _ (by decide) (by decide)] at this; exact this)
  rd := h₂.rd.trans h₁.rd
  wr := h₂.wr.trans h₁.wr

theorem LkKeep.of_pure {s s' : State} (h : Pure s s') : LkKeep s s' :=
  ⟨fun k _ _ => slotW_eq_of h.mem (h.regs _ (by decide) (by decide)) k, h.regs,
    by rw [h.mem]; exact Frame.refl _ _, h.rd, h.wr⟩

/-- `copyBytes t0 a0 sb soff (8 k) nb`, `nb = 8 n`: `n` words of the key to
slots `k … k + n - 1`. -/
theorem copyKey_ok {s : State} {len soff k n nb : Nat} (hnb : nb = 8 * n)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hkey : (⟨s.gpr .a0, len⟩ : Region) ∈ s.rd)
    (hks : Region.Disjoint ⟨s.gpr .a0, len⟩ ⟨s.gpr sb, 8 * slots⟩) (hlen : len ≤ 32)
    (hsl : soff + 8 * n ≤ len) (hk2 : k + n ≤ keySlot) :
    ∃ s', runBlock isa (copyBytes t0 .a0 sb soff (8 * k) nb) s = some s' ∧
      (∀ w < n, WordOf (slotW s' (k + w))
        (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 (soff + 8 * w)))) ∧
      (∀ j < slots, (j < k ∨ k + n ≤ j) → slotW s' j = slotW s j) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  subst hnb
  have hK := keySlot_eq
  have hS := slots_eq
  obtain ⟨s', e', c'⟩ := WP.runBlock_of (Bytes.copyBytes_ok (s := s) (tmp := t0) (src := .a0) (dst := sb)
    (soff := soff) (doff := 8 * k) (n := 8 * n) (by decide) (by decide) (by omega_arith) (by omega_arith)
    (fun i hi => ⟨_, List.mem_append_left _ hkey, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi => ⟨_, hscr, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi hc => hks _ (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
      ((VG.Offset.sub_base _ (by omega_arith)) _ hc)))
  obtain hb : s'.gpr sb = s.gpr sb := c'.gpr _ (by decide)
  refine ⟨s', e', fun w hw => ?_, fun j hj hjk => ?_, c'.gpr, ?_, c'.rd, c'.wr⟩
  · simp only [slotW, hb, wordAddr]
    refine wordOf_copy fun i hi => ?_
    have := c'.copied (8 * w + i) (by omega_arith)
    rw [Offset.add_add, Offset.add_add, show 8 * (k + w) + i = 8 * k + (8 * w + i) by omega_arith,
      show soff + 8 * w + i = soff + (8 * w + i) by omega_arith]
    exact this
  · simp only [slotW, hb]
    refine c'.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [wordAddr]
    exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · exact c'.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base _ (by omega_arith)⟩

/-- `KL` and `KR`, from the key's bytes. -/
abbrev klOf (m : Mem) (a : Addr) (len : Nat) : BitVec 128 := (Spec.Camellia.klkr (Spec.Camellia.bytesAt m a len)).1
abbrev krOf (m : Mem) (a : Addr) (len : Nat) : BitVec 128 := (Spec.Camellia.klkr (Spec.Camellia.bytesAt m a len)).2

theorem ofInt_neg_one : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := by decide

/-- What `loadKey` needs: the scratch buffer and the key, apart. -/
structure LkPre (s : State) (len : Nat) : Prop where
  al : (s.gpr sb).toNat % 8 = 0
  scr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr
  key : (⟨s.gpr .a0, len⟩ : Region) ∈ s.rd
  sep : Region.Disjoint ⟨s.gpr .a0, len⟩ ⟨s.gpr sb, 8 * slots⟩
  alen : s.gpr .a3 = BitVec.ofNat 64 len
  hl : len = 16 ∨ len = 24 ∨ len = 32

theorem LkPre.of_keep {s t : State} {len : Nat} (h : LkPre s len) (hk : LkKeep s t)
    (ha3 : t.gpr .a3 = s.gpr .a3) : LkPre t len where
  al := by rw [hk.regs _ (by decide) (by decide)]; exact h.al
  scr := by rw [hk.regs _ (by decide) (by decide), hk.wr]; exact h.scr
  key := by rw [hk.regs _ (by decide) (by decide), hk.rd]; exact h.key
  sep := by rw [hk.regs _ (by decide) (by decide), hk.regs _ (by decide) (by decide)]; exact h.sep
  alen := by rw [ha3]; exact h.alen
  hl := h.hl

/-- The key's words are those on entry, as long as only the scratch buffer changes. -/
theorem LkPre.word {s t : State} {len : Nat} (h : LkPre s len) (hk : LkKeep s t) {off : Nat}
    (hoff : off + 8 ≤ len) :
    Spec.Camellia.wordAt t.mem (t.gpr .a0 + BitVec.ofNat 64 off) =
      Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 off) := by
  rw [hk.regs _ (by decide) (by decide)]
  refine wordAt_frame hk.frame fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact h.sep.sub_left (VG.Offset.sub_base _ (by omega_arith))

/-- What each of `loadKey`'s branches leaves, from `u`: `KR`'s halves. -/
structure KrDone (s u u' : State) (len : Nat) : Prop where
  kr : WordsAt u' krSlot (hiW (krOf s.mem (s.gpr .a0) len), loW (krOf s.mem (s.gpr .a0) len))
  keep : LkKeep u u'
  low : ∀ k < slots, k < krSlot → slotW u' k = slotW u k

/-- A key of 16 bytes: `KR = 0`. -/
theorem kr16_ok {s u : State} {len : Nat} (hp : LkPre u len) (h16 : len = 16) :
    ∃ u', runBlock isa [.li t0 0, stS krSlot t0, stS (krSlot + 1) t0] u = some u' ∧ KrDone s u u' len := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨-, -, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) (Or.inl h16)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := liN_ok u t0 0 (by decide)
  obtain lk₃ : LkKeep u s₃ := LkKeep.of_pure ⟨m₃, fun r h0 _ => o₃ r h0, rd₃, wr₃⟩
  obtain hp₃ := hp.of_keep lk₃ (o₃ _ (by decide))
  obtain ⟨s₄, e₄, v₄, k₄, g₄, f₄, rd₄, wr₄⟩ := st_ok (k := krSlot) t0 hp₃.al hp₃.scr (by omega_arith)
  obtain ⟨s₅, e₅, v₅, k₅, g₅, f₅, rd₅, wr₅⟩ := st_ok (k := krSlot + 1) t0
    (by rw [g₄]; exact hp₃.al) (by rw [g₄, wr₄]; exact hp₃.scr) (by omega_arith)
  refine ⟨s₅, by
    rw [show ([.li t0 0, stS krSlot t0, stS (krSlot + 1) t0] : List Instr) =
        [.li t0 0] ++ ([stS krSlot t0] ++ [stS (krSlot + 1) t0]) from rfl,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅],
    ⟨?_, ?_⟩, ?_, fun k hk h => ?_⟩
  · rw [k₅ _ (by omega_arith) (by omega_arith), v₄, a₃, hK2, ite_eq_left h16]; exact WordOf.zero
  · rw [v₅, g₄, a₃, hK3, ite_eq_left h16]; exact WordOf.zero
  · refine lk₃.trans ⟨fun k hk h => by rw [k₅ k hk (by omega_arith), k₄ k hk (by omega_arith)],
      fun r _ _ => by rw [g₅, g₄], ?_, by rw [rd₅, rd₄], by rw [wr₅, wr₄]⟩
    exact f₄.trans (by rw [g₄] at f₅; exact f₅)
  · rw [k₅ k hk (by omega_arith), k₄ k hk (by omega_arith)]
    exact slotW_eq_of m₃ (o₃ _ (by decide)) k

/-- A key of 24 bytes: `KR`'s low half is the complement of its high half. -/
theorem kr24_ok {s u : State} {len : Nat} (hs : LkPre s len) (hp : LkPre u len)
    (h24 : len = 24) (hw : WordOf (slotW u krSlot) (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 16))) :
    ∃ u', runBlock isa [ldS t0 krSlot, notR t0, stS (krSlot + 1) t0] u = some u' ∧ KrDone s u u' len := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨-, -, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) hs.hl
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅⟩ := ldS_ok (k := krSlot) t0 rfl hp.al hp.scr (by omega_arith)
  let s₆ := s₅.write t0 (s₅.gpr t0 ^^^ BitVec.ofInt 64 (-1))
  obtain e₆ : runBlock isa [notR t0] s₅ = some s₆ := by
    simp only [notR, runBlock_cons, exec_logicImm (show imm12 (-1 : Int) by decide), runStep_some,
      runBlock_nil]
    rfl
  obtain a₆ : s₆.gpr t0 = ~~~ slotW u krSlot := by
    rw [RegUpd.gpr_write_self, a₅, ofInt_neg_one, BitVec.xor_allOnes]
  obtain o₆ : ∀ r, r ≠ t0 → s₆.gpr r = u.gpr r := fun r hr => by
    rw [RegUpd.gpr_write_of_ne _ _ hr, o₅ r hr]
  obtain lk₆ : LkKeep u s₆ := LkKeep.of_pure ⟨m₅, fun r h0 _ => o₆ r h0, rd₅, wr₅⟩
  obtain hp₆ := hp.of_keep lk₆ (o₆ _ (by decide))
  obtain ⟨s₇, e₇, v₇, k₇, g₇, f₇, rd₇, wr₇⟩ := st_ok (k := krSlot + 1) t0 hp₆.al hp₆.scr (by omega_arith)
  obtain hs₆ : ∀ k, slotW s₆ k = slotW u k := slotW_eq_of m₅ (o₆ _ (by decide))
  refine ⟨s₇, by
    rw [show ([ldS t0 krSlot, notR t0, stS (krSlot + 1) t0] : List Instr) =
        [ldS t0 krSlot] ++ ([notR t0] ++ [stS (krSlot + 1) t0]) from rfl,
      runBlock_append', e₅, Option.bind_some, runBlock_append', e₆, Option.bind_some, e₇],
    ⟨?_, ?_⟩, lk₆.trans ⟨fun k hk h => k₇ k hk (by omega_arith), fun r _ _ => by rw [g₇], f₇, rd₇, wr₇⟩,
    fun k hk h => ?_⟩
  · rw [k₇ _ (by omega_arith) (by omega_arith), hs₆, hK2, ite_eq_right (by omega_arith)]; exact hw
  · rw [v₇, a₆, hK3, ite_eq_right (by omega_arith), ite_eq_left h24]; exact hw.not
  · rw [k₇ k hk (by omega_arith), hs₆]

/-- A key of 32 bytes: `KR`'s low half is the key's fourth word. -/
theorem kr32_ok {s u : State} {len : Nat} (hs : LkPre s len) (hk : LkKeep s u) (hp : LkPre u len)
    (h16 : len ≠ 16) (h24 : len ≠ 24)
    (hw : WordOf (slotW u krSlot) (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 16))) :
    ∃ u', runBlock isa (copyBytes t0 .a0 sb 24 (8 * (krSlot + 1)) 8) u = some u' ∧ KrDone s u u' len := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨-, -, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) hs.hl
  obtain h32 : len = 32 := by rcases hs.hl with h | h | h <;> omega_arith
  obtain ⟨s₅, e₅, w₅, k₅, g₅, f₅, rd₅, wr₅⟩ := copyKey_ok (s := u) (soff := 24) (k := krSlot + 1) (n := 1)
    (nb := 8) rfl hp.scr hp.key hp.sep (by omega_arith) (by omega_arith) (by omega_arith)
  obtain lk₅ : LkKeep u s₅ := ⟨fun k hk h => k₅ k hk (by omega_arith), fun r h0 _ => g₅ r h0, f₅, rd₅, wr₅⟩
  refine ⟨s₅, e₅, ⟨?_, ?_⟩, lk₅, fun k hk h => k₅ k hk (by omega_arith)⟩
  · rw [k₅ _ (by omega_arith) (by omega_arith), hK2, ite_eq_right h16]; exact hw
  · have := w₅ 0 (by decide)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero, hs.word hk (by omega_arith)] at this
    rw [hK3, ite_eq_right h16, ite_eq_right h24]; exact this

/-- The first block of `loadKey`: `KL`, and `t1 := len - 16`. -/
theorem klBlock_ok {s : State} {len : Nat} (hs : LkPre s len) :
    ∃ s', runBlock isa (copyBytes t0 .a0 sb 0 (8 * klSlot) 16 ++ ([.addi t1 .a3 (-16)] : List Instr)) s =
        some s' ∧ LkKeep s s' ∧ s'.gpr .a3 = s.gpr .a3 ∧
      WordsAt s' klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)) ∧
      (s'.gpr t1 == 0) = decide (len = 16) := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨hK0, hK1, -, -⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) hs.hl
  obtain hl32 : len ≤ 32 := by rcases hs.hl with h | h | h <;> omega_arith
  obtain hz : s.gpr .a0 + BitVec.ofNat 64 (0 + 8 * 0) = s.gpr .a0 := by simp
  obtain ⟨s₁, e₁, w₁, k₁, g₁, f₁, rd₁, wr₁⟩ := copyKey_ok (soff := 0) (k := klSlot) (n := 2) (nb := 16) rfl
    hs.scr hs.key hs.sep hl32 (by rcases hs.hl with h | h | h <;> omega_arith) (by omega_arith)
  obtain ⟨s₂, e₂, z₂, o₂, m₂, rd₂, wr₂⟩ := subI_ok s₁ t1 .a3 16 (by decide)
  obtain hs₂ : ∀ k, slotW s₂ k = slotW s₁ k := slotW_eq_of m₂ (o₂ _ (by decide))
  refine ⟨s₂, by rw [runBlock_append', e₁, Option.bind_some]; exact e₂,
    ⟨fun k hk h => by rw [hs₂, k₁ k hk (by omega_arith)], fun r h0 h1 => by rw [o₂ r h1, g₁ r h0],
      by rw [m₂]; exact f₁, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩,
    by rw [o₂ _ (by decide), g₁ _ (by decide)], ⟨?_, ?_⟩, ?_⟩
  · rw [hs₂, hK0, ← hz]; exact w₁ 0 (by decide)
  · rw [hs₂, hK1]; exact w₁ 1 (by decide)
  · rw [z₂, g₁ _ (by decide), hs.alen, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]

/-- The block of `loadKey` for keys of 24 or 32 bytes: `KR`'s high half, and `t1 := len - 24`. -/
theorem krBlock_ok {s u : State} {len : Nat} (hs : LkPre s len) (hk : LkKeep s u) (hp : LkPre u len)
    (h16 : len ≠ 16) :
    ∃ u', runBlock isa (copyBytes t0 .a0 sb 16 (8 * krSlot) 8 ++ ([.addi t1 .a3 (-24)] : List Instr)) u =
        some u' ∧ LkKeep u u' ∧ u'.gpr .a3 = u.gpr .a3 ∧ (∀ k < slots, k < krSlot → slotW u' k = slotW u k) ∧
      WordOf (slotW u' krSlot) (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 16)) ∧
      (u'.gpr t1 == 0) = decide (len = 24) := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain hl32 : len ≤ 32 := by rcases hs.hl with h | h | h <;> omega_arith
  obtain hl24 : 24 ≤ len := by rcases hs.hl with h | h | h <;> omega_arith
  obtain ⟨s₃, e₃, w₃, k₃, g₃, f₃, rd₃, wr₃⟩ := copyKey_ok (s := u) (soff := 16) (k := krSlot) (n := 1) (nb := 8)
    rfl hp.scr hp.key hp.sep hl32 (by omega_arith) (by omega_arith)
  obtain ⟨s₄, e₄, z₄, o₄, m₄, rd₄, wr₄⟩ := subI_ok s₃ t1 .a3 24 (by decide)
  obtain hs₄ : ∀ k, slotW s₄ k = slotW s₃ k := slotW_eq_of m₄ (o₄ _ (by decide))
  refine ⟨s₄, by rw [runBlock_append', e₃, Option.bind_some]; exact e₄,
    ⟨fun k hk h => by rw [hs₄, k₃ k hk (by omega_arith)], fun r h0 h1 => by rw [o₄ r h1, g₃ r h0],
      by rw [m₄]; exact f₃, by rw [rd₄, rd₃], by rw [wr₄, wr₃]⟩,
    by rw [o₄ _ (by decide), g₃ _ (by decide)], fun k hk h => by rw [hs₄, k₃ k hk (Or.inl h)], ?_, ?_⟩
  · have := w₃ 0 (by decide)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero, hs.word hk (by omega_arith)] at this
    rw [hs₄]; exact this
  · rw [z₄, g₃ _ (by decide), hp.alen, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]

/-- `loadKey`'s postcondition, from `KL`'s block and `KR`'s branch. -/
theorem lkPost_of {s s₂ s' : State} {len : Nat}
    (hkl : WordsAt s₂ klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)))
    (lk₂ : LkKeep s s₂) (h : KrDone s s₂ s' len) :
    WordsAt s' klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)) ∧
      WordsAt s' krSlot (hiW (krOf s.mem (s.gpr .a0) len), loW (krOf s.mem (s.gpr .a0) len)) ∧
      LkKeep s s' := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  exact ⟨hkl.congr (h.low _ (by omega_arith) (by omega_arith)) (h.low _ (by omega_arith) (by omega_arith)),
    h.kr, lk₂.trans h.keep⟩

/-- `KrDone` from the state before the block of `KR`'s high half. -/
theorem krDone_trans {s s₂ s₄ s' : State} {len : Nat} (lk₄ : LkKeep s₂ s₄)
    (lo₄ : ∀ k < slots, k < krSlot → slotW s₄ k = slotW s₂ k) (h : KrDone s s₄ s' len) : KrDone s s₂ s' len :=
  ⟨h.kr, lk₄.trans h.keep, fun k hk h' => by rw [h.low k hk h', lo₄ k hk h']⟩

/-- `loadKey`: `KL`'s and `KR`'s halves, as words, in their slots. -/
theorem loadKey_wp {s : State} {len : Nat} (hs : LkPre s len) :
    WP isa loadKey s fun s' =>
      WordsAt s' klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)) ∧
      WordsAt s' krSlot (hiW (krOf s.mem (s.gpr .a0) len), loW (krOf s.mem (s.gpr .a0) len)) ∧
      LkKeep s s' := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨s₂, e₂, lk₂, a3₂, hkl, hz₂⟩ := klBlock_ok hs
  obtain hp₂ := hs.of_keep lk₂ a3₂
  unfold loadKey
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  refine WP.mono (Q := fun s' => KrDone s s₂ s' len)
    (WP.ite (decide (len = 16)) ((eval_zero s₂ t1).trans (by rw [hz₂])) (fun h16 => ?_) (fun h16 => ?_))
    fun s' h => lkPost_of hkl lk₂ h
  · obtain ⟨u', e', h'⟩ := kr16_ok (s := s) hp₂ (by simpa using h16)
    exact WP.of_runBlock ⟨u', e', h'⟩
  · have h16 : len ≠ 16 := by simpa using h16
    obtain ⟨s₄, e₄, lk₄, a3₄, lo₄, w₄, hz₄⟩ := krBlock_ok hs lk₂ hp₂ h16
    obtain lk₂₄ := lk₂.trans lk₄
    obtain hp₄ := hs.of_keep lk₂₄ (a3₄.trans a3₂)
    refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
    refine WP.mono (Q := fun s' => KrDone s s₄ s' len)
      (WP.ite (decide (len = 24)) ((eval_zero s₄ t1).trans (by rw [hz₄])) (fun h24 => ?_) (fun h24 => ?_))
      fun s' h => krDone_trans lk₄ lo₄ h
    · obtain ⟨u', e', h'⟩ := kr24_ok hs hp₄ (by simpa using h24) w₄
      exact WP.of_runBlock ⟨u', e', h'⟩
    · obtain ⟨u', e', h'⟩ := kr32_ok hs lk₂₄ hp₄ h16 (by simpa using h24) w₄
      exact WP.of_runBlock ⟨u', e', h'⟩


/-! ## Loading the values -/

def lvChunk (v k : Nat) : List Instr :=
  loadBE64 (hiReg v) t0 sb (8 * k) ++ loadBE64 (loReg v) t0 sb (8 * (k + 1))

theorem loadValues_eq :
    loadValues = lvChunk 0 klSlot ++ (lvChunk 1 krSlot ++ (lvChunk 2 kaSlot ++ lvChunk 3 kbSlot)) := by
  rfl

theorem regs_lt4 {v : Nat} (hv : v < 4) : hiReg v ≠ sb ∧ loReg v ≠ sb ∧ hiReg v ≠ loReg v ∧
    hiReg v ≠ t0 ∧ loReg v ≠ t0 := by
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide

/-- `loadBE64 t t0 sb (8 k)`: slot `k`, read big-endian. -/
theorem ldBE_ok {s : State} {k : Nat} (t : Reg) (ht : t ≠ sb) (ht0 : t ≠ t0)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < keySlot) {H : BitVec 64}
    (hw : WordOf (slotW s k) H) :
    ∃ s', runBlock isa (loadBE64 t t0 sb (8 * k)) s = some s' ∧ s'.gpr t = H ∧
      (∀ r, r ≠ t → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hk' : k < slots := by rw [keySlot_eq] at hk; rw [slots_eq]; omega_arith
  obtain ⟨r, hr, hc⟩ := scr_in hscr hk'
  obtain ⟨s', e', h'⟩ := WP.runBlock_of (ByteLoad.loadBE64_ok (s := s) (d := t) (tmp := t0) (n := sb)
    (off := 8 * k) ht (by decide) ht0 (by rw [keySlot_eq] at hk; omega_arith) ⟨r, List.mem_append_right _ hr, hc⟩)
  subst h'
  refine ⟨_, e', ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · rw [RegUpd.gpr_write_self]; exact be64_of_wordOf hw
  · rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]

theorem lvChunk_ok {s : State} {v k : Nat} (hv : v < 4) (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hk : k + 1 < keySlot) {H L : BitVec 64} (hw : WordsAt s k (H, L)) :
    ∃ s', runBlock isa (lvChunk v k) s = some s' ∧ s'.gpr (hiReg v) = H ∧ s'.gpr (loReg v) = L ∧
      (∀ r, r ≠ hiReg v → r ≠ loReg v → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := regs_lt4 hv
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := ldBE_ok (k := k) (hiReg v) n1 n4 hscr (by omega_arith) hw.1
  obtain hb₂ : s₂.gpr sb = s.gpr sb := o₂ _ n1.symm (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := ldBE_ok (s := s₂) (k := k + 1) (loReg v) n2 n5
    (by rw [hb₂, wr₂]; exact hscr) hk (by rw [slotW_eq_of m₂ hb₂]; exact hw.2)
  refine ⟨s₄, by rw [lvChunk, runBlock_append', e₂, Option.bind_some, e₄], ?_, a₄,
    fun r h1 h2 h3 => by rw [o₄ r h2 h3, o₂ r h1 h3], by rw [m₄, m₂], by rw [rd₄, rd₂], by rw [wr₄, wr₂]⟩
  rw [o₄ _ n3 n4, a₂]

/-- `loadValues`: the four values' halves, read big-endian into `hiReg v` and `loReg v`. -/
theorem loadValues_ok {s : State} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (vs : List (BitVec 128))
    (hw : ∀ v < 4, WordsAt s ([klSlot, krSlot, kaSlot, kbSlot].getD v 0) (hiW (vs.getD v 0), loW (vs.getD v 0))) :
    ∃ s', runBlock isa loadValues s = some s' ∧
      (∀ v < 4, s'.gpr (hiReg v) = hiW (vs.getD v 0) ∧ s'.gpr (loReg v) = loW (vs.getD v 0)) ∧
      (∀ r, (∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v) → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl, hr, hW, hA, hB, -, hK, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, h₁, l₁, o₁, m₁, rd₁, wr₁⟩ := lvChunk_ok (v := 0) (k := klSlot) (by decide) hscr (by omega_arith)
    (hw 0 (by decide))
  obtain hb₁ : s₁.gpr sb = s.gpr sb := o₁ _ (by decide) (by decide) (by decide)
  obtain hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ hb₁
  obtain ⟨s₂, e₂, h₂, l₂, o₂, m₂, rd₂, wr₂⟩ := lvChunk_ok (v := 1) (k := krSlot) (by decide)
    (by rw [hb₁, wr₁]; exact hscr) (by omega_arith) ((hw 1 (by decide)).congr (hs₁ _) (hs₁ _))
  obtain hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide) (by decide) (by decide), hb₁]
  obtain hs₂ : ∀ k, slotW s₂ k = slotW s k := fun k => by rw [slotW_eq_of m₂ (by rw [hb₂, hb₁]), hs₁]
  obtain ⟨s₃, e₃, h₃, l₃, o₃, m₃, rd₃, wr₃⟩ := lvChunk_ok (v := 2) (k := kaSlot) (by decide)
    (by rw [hb₂, wr₂, wr₁]; exact hscr) (by omega_arith) ((hw 2 (by decide)).congr (hs₂ _) (hs₂ _))
  obtain hb₃ : s₃.gpr sb = s.gpr sb := by rw [o₃ _ (by decide) (by decide) (by decide), hb₂]
  obtain hs₃ : ∀ k, slotW s₃ k = slotW s k := fun k => by rw [slotW_eq_of m₃ (by rw [hb₃, hb₂]), hs₂]
  obtain ⟨s₄, e₄, h₄, l₄, o₄, m₄, rd₄, wr₄⟩ := lvChunk_ok (v := 3) (k := kbSlot) (by decide)
    (by rw [hb₃, wr₃, wr₂, wr₁]; exact hscr) (by omega_arith) ((hw 3 (by decide)).congr (hs₃ _) (hs₃ _))
  refine ⟨s₄, by rw [loadValues_eq, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂,
      Option.bind_some, runBlock_append', e₃, Option.bind_some, e₄], fun v hv => ?_,
    fun r hr h0 => by
      obtain ⟨a0, b0⟩ := hr 0 (by decide); obtain ⟨a1, b1⟩ := hr 1 (by decide)
      obtain ⟨a2, b2⟩ := hr 2 (by decide); obtain ⟨a3, b3⟩ := hr 3 (by decide)
      rw [o₄ r a3 b3 h0, o₃ r a2 b2 h0, o₂ r a1 b1 h0, o₁ r a0 b0 h0],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · exact ⟨by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide),
        o₂ _ (by decide) (by decide) (by decide), h₁],
      by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide),
        o₂ _ (by decide) (by decide) (by decide), l₁]⟩
  · exact ⟨by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide), h₂],
      by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide), l₂]⟩
  · exact ⟨by rw [o₄ _ (by decide) (by decide) (by decide), h₃],
      by rw [o₄ _ (by decide) (by decide) (by decide), l₃]⟩
  · exact ⟨h₄, l₄⟩

/-! ## The prologue -/

theorem sreg_ne' (i : Nat) (hi : i < 12) : sreg i ≠ sb ∧ sreg i ≠ .a3 := by
  revert i; decide

theorem ekPrologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .a3 = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr)
    (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) (hal : b.toNat % 8 = 0) :
    ∃ s, runBlock isa ([movR sb .a3, movR .a3 .a1] ++ saveRegs ++ setSlots allMasks ++ tableSetup ++
        sigmas.flatMap sigmaOne) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .a3 = s₀.gpr .a1 ∧
      (∀ r, r ≠ sb → r ≠ .a3 → r ≠ t0 → r ≠ t1 → r ≠ kp → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧
      (∀ i < 6, ∀ j < 8, entryW s.mem b i j = keyPlane (sigmas.getD i 0) j) ∧
      Frame [⟨b, 8 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hk := keySlot_eq
  have hsv := savedSlot_eq
  have hS := slots_eq
  obtain ⟨s₁a, e₁a, r₁a, o₁a, m₁a, rd₁a, wr₁a⟩ := movR_ok s₀ sb .a3
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₁a .a3 .a1
  obtain hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), r₁a, hb]
  obtain g₁ : ∀ r, r ≠ sb → r ≠ .a3 → s₁.gpr r = s₀.gpr r := fun r h1 h2 => by rw [o₁ r h2, o₁a r h1]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁, wr₁a]; exact hw) hb₁ hal
  obtain ⟨s₃, e₃, v₃, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) (by rw [wr₂, wr₁, wr₁a]; exact hw)
    (by rw [g₂, hb₁]) hal
  obtain hb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide), g₂, hb₁]
  obtain ⟨s₄, e₄, k₄, o₄, m₄, rd₄, wr₄⟩ := setKp_ok s₃
  obtain hb₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), hb₃]
  obtain ⟨s₅, e₅, v₅, f₅, r₅, g₅, rd₅, wr₅⟩ := sigmaList_ok hfit hal sigmas 0 s₄
    (by rw [wr₄, wr₃, wr₂, wr₁, wr₁a]; exact hw)
    (by rw [k₄, hb₃]; simp) (by decide)
  obtain hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide) (by decide), hb₄]
  -- The slots outside the table keep their values.
  obtain hs₅ : ∀ k, k < keySlot ∨ keySlot + 48 ≤ k → k < slots → slotW s₅ k = slotW s₃ k := fun k h1 h2 => by
    simp only [slotW, hb₅, hb₃]
    rw [← m₄]
    refine f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    simp only [wordAddr, Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
    exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨s₅, ?_, hb₅, ?_, fun r h1 h2 h3 h4 h5 => ?_, fun i hi => ?_, fun kv hkv => ?_,
    fun i hi j hj => ?_, ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁, rd₁a],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁, wr₁a]⟩
  · rw [runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      show ([movR sb .a3, movR .a3 .a1] : List Instr) = [movR sb .a3] ++ [movR .a3 .a1] from rfl,
      runBlock_append', e₁a, Option.bind_some, e₁, Option.bind_some, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some, e₅]
  · rw [g₅ _ (by decide) (by decide) (by decide), o₄ _ (by decide), g₃ _ (by decide) (by decide), g₂, r₁,
      o₁a _ (by decide)]
  · rw [g₅ r h3 h4 h5, o₄ r h5, g₃ r h3 h4, g₂, g₁ r h1 h2]
  · have n := sreg_ne' i hi
    have := sv₂ i hi
    rw [show s₁.gpr (sreg i) = s₀.gpr (sreg i) from g₁ _ n.1 n.2] at this
    rw [← this]
    obtain h' := hs₅ (savedSlot + i) (Or.inl (by omega_arith)) (by omega_arith)
    simp only [slotW, hb₅, hb₃] at h'
    rw [h']
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by omega_arith) (by omega_arith)
  · have := mask_lt hkv
    rw [hs₅ _ (Or.inl (by omega_arith)) (by omega_arith)]
    exact v₃ kv hkv
  · have := v₅ i (by simpa [sigmas] using hi) j hj
    rw [Nat.zero_add] at this
    exact this
  · have sub : ∀ {r : Region}, Region.Sub r ⟨b, 8 * slots⟩ → ∀ r' ∈ [r], ∃ r'' ∈ [(⟨b, 8 * slots⟩ : Region)],
        Region.Sub r' r'' := fun hs r' hr' => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr'; subst hr'; exact hs⟩
    obtain f₂' : Frame [⟨b, 8 * slots⟩] s₁.mem s₂.mem :=
      f₂.sub (sub (VG.Offset.sub_base b (by omega_arith)))
    obtain f₃' : Frame [⟨b, 8 * slots⟩] s₂.mem s₃.mem := f₃.sub (sub (Region.sub_prefix (by omega_arith)))
    obtain f₅' : Frame [⟨b, 8 * slots⟩] s₄.mem s₅.mem := f₅.sub (sub (by
      simp only [Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
      exact VG.Offset.sub_base b (by omega_arith)))
    rw [m₁, m₁a] at f₂'
    rw [m₄] at f₅'
    exact f₂'.trans (f₃'.trans f₅')

end VG.Proof.Camellia.RISCV64

end

end


/-!
# The Camellia key schedule on RISCV64: the whole function

As on PPC64LE (`Proof/Camellia/PPC64LE/ExpandKey.lean`). `expandKey_wp`:
`expandKey` meets `expandKeyRISCV64`. After the prologue
(`ekPrologue_ok`), `loadKey_wp` and `kaKb_wp` leave `KL`, `KR`, `KA` and
`KB` in their slots; `loadValues_ok` reads them big-endian into registers, and
`storeSubkeys_ok` stores the subkeys, which are the specification's
(`scheduleWords_expandKey`, `schedule_of_stores`).
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 u7 kp movR ldS stS)
open VG.Proof.Camellia (hiW loW)

theorem entryW_slot (s : State) (i j : Nat) : entryW s.mem (s.gpr sb) i j = slotW s (keySlot + 8 * i + j) := by
  simp only [entryW, slotW, wordAddr]
  rw [show 8 * (keySlot + 8 * i + j) = 8 * keySlot + 64 * i + 8 * j by omega_using []]

/-- What the subkeys' stores leave: the schedule's bytes. -/
structure StoresPost (s₈ : State) (S : Addr) (len : Nat) (key : List Byte) (s : State) : Prop where
  bytes : Spec.Camellia.bytesAt s.mem S (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
    Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key)
  frame : Frame [⟨S, 272⟩] s₈.mem s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s.gpr r = s₈.gpr r
  rd : s.rd = s₈.rd
  wr : s.wr = s₈.wr

/-- The stores of one key length's subkeys. -/
theorem stores_wp {s₈ : State} {S : Addr} {len : Nat} {key : List Byte} {ks : List (Nat × Nat × Bool)}
    (hS : s₈.gpr .a2 = S) (hw : (⟨S, 272⟩ : Region) ∈ s₈.wr) (hv : ∀ k ∈ ks, k.1 < 4)
    (hks : ks.length ≤ 34)
    (hg : ∀ v < 4, s₈.gpr (hiReg v) = hiW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) ∧
      s₈.gpr (loReg v) = loW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0))
    (hlen : 8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len) = 8 * ks.length)
    (hks' : ks = if key.length = 16 then Impl.Camellia.subkeys128 else Impl.Camellia.subkeys256) :
    WP isa (.block (storeSubkeys ks)) s₈ (StoresPost s₈ S len key) := by
  obtain ⟨s₉, e₉, b₉, f₉, g₉, rd₉, wr₉⟩ := storeSubkeys_ok ks hv 0 s₈ (fun i hi => ⟨_, hw, by
    rw [hS]; exact VG.Offset.contains_base _ (by omega_using [hks, hi]) (by omega_using [hks, hi])⟩) (by omega_using [hks])
  refine WP.of_runBlock ⟨s₉, e₉, ⟨?_, ?_, g₉, rd₉, wr₉⟩⟩
  · rw [hlen, schedule_of_stores (H := fun v => s₈.gpr (hiReg v)) (L := fun v => s₈.gpr (loReg v)) hv hg (by rw [← hS]; exact b₉), Spec.Camellia.scheduleBytes,
      Proof.Camellia.scheduleWords_expandKey, ← hks']
  · rw [hS] at f₉
    exact f₉.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base S (by omega_using [hks])⟩

theorem expandKey_wp {s₀ : State} (hp : expandKeyRISCV64.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 12, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      expandKeyRISCV64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB, hlen, hal⟩ := hp
  obtain ⟨hl', hr', hW, hA, hB, hE, hK, hS⟩ := kaKb_slots
  have ht := tailSlot_eq
  have hsv := savedSlot_eq
  obtain hwB : (⟨s₀.gpr .a3, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  obtain hwS : (⟨s₀.gpr .a2, 272⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  obtain hrK : (⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  unfold expandKey
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r6₁, g₁, sv₁, mk₁, ent₁, f₁, rd₁, wr₁⟩ := ekPrologue_ok (b := s₀.gpr .a3) rfl hwB fitB hal
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain r3₁ : s₁.gpr .a0 = s₀.gpr .a0 := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain r5₁ : s₁.gpr .a2 = s₀.gpr .a2 := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The key, unchanged so far.
  obtain hkey₁ : Spec.Camellia.bytesAt s₁.mem (s₁.gpr .a0) (s₀.gpr .a1).toNat =
      Spec.Camellia.bytesAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat := by
    rw [r3₁]
    refine Proof.Camellia.bytesAt_congr fun i hi => f₁.bytes (R := ⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩)
      (fun r hr => ?_) (by simp only; omega_using []) hi
    simp only [List.mem_singleton] at hr; subst hr
    exact dKB.sub_right (Region.sub_prefix (by omega_using []))
  -- `KL` and `KR`.
  refine WP.seq (WP.mono (loadKey_wp (len := (s₀.gpr .a1).toNat) (s := s₁)
    ⟨by rw [b₁]; exact hal, by rw [b₁, wr₁]; exact hwB, by rw [r3₁, rd₁]; exact hrK, by rw [r3₁, b₁]; exact dKB,
      by rw [r6₁, BitVec.ofNat_toNat, BitVec.setWidth_eq], hlen⟩) fun s₂ h₂ => ?_)
  obtain ⟨kl₂, kr₂, ⟨sl₂, g₂, f₂, rd₂, wr₂⟩⟩ := h₂
  simp only [klOf, krOf] at kl₂ kr₂
  rw [hkey₁] at kl₂ kr₂
  -- Abbreviations.
  generalize hkey : Spec.Camellia.bytesAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat = key at kl₂ kr₂
  obtain hb₂ : s₂.gpr sb = s₀.gpr .a3 := by rw [g₂ _ (by decide) (by decide), b₁]
  -- `kp` at the table.
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := setKp_ok s₂
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have hg₄ : ∀ r, r ≠ kp → s₄.gpr r = s₂.gpr r := o₄
  obtain hb₄ : s₄.gpr sb = s₀.gpr .a3 := by rw [hg₄ _ (by decide), hb₂]
  obtain hs₄ : ∀ k, slotW s₄ k = slotW s₂ k := slotW_eq_of m₄ (hg₄ _ (by decide))
  obtain r5₄ : s₄.gpr .a2 = s₀.gpr .a2 := by
    rw [hg₄ _ (by decide), g₂ _ (by decide) (by decide), r5₁]
  obtain r6₄ : s₄.gpr .a3 = s₀.gpr .a1 := by
    rw [hg₄ _ (by decide), g₂ _ (by decide) (by decide), r6₁]
  obtain wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₂, wr₁]
  obtain hlow : ∀ k < slots, (k < klSlot ∨ krSlot + 2 ≤ k) → slotW s₄ k = slotW s₁ k := fun k hk h => by
    rw [hs₄, sl₂ k hk h]
  let KL : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).1, loW (Spec.Camellia.klkr key).1)
  let KR : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).2, loW (Spec.Camellia.klkr key).2)
  obtain hpre : KaPre s₄ KL KR := by
    refine ⟨⟨?_, by rw [hb₄]; exact hal, ?_, by decide, fun kv hkv => ?_, fun i hi => ?_⟩, ?_,
      kl₂.congr (hs₄ _) (hs₄ _), kr₂.congr (hs₄ _) (hs₄ _)⟩
    · rw [hb₄, wr₄']; exact hwB
    · rw [hb₄]; exact fitB
    · have := mask_lt hkv
      rw [hlow _ (by omega_using [hE, hS, this]) (Or.inl (by omega_using [hl', hE, this]))]; exact mk₁ kv hkv
    · refine sigmas_rel (m := s₄.mem) (b := s₄.gpr sb) (fun i hi j hj => ?_) i hi
      rw [entryW_slot, hlow _ (by omega_using [hK, hS, hi, hj]) (Or.inr (by omega_using [hr', hK])), ← entryW_slot, b₁]
      exact ent₁ i hi j hj
    · rw [AtEntry, a₄, hb₄, hb₂]; simp
  -- `KA` and `KB`.
  refine WP.seq (WP.mono (kaKb_wp hpre) fun s₅ h₅ => ?_)
  obtain hb₅ : s₅.gpr sb = s₀.gpr .a3 := h₅.base.trans hb₄
  obtain wr₅ : s₅.wr = s₀.wr := h₅.wr.trans wr₄'
  obtain hscr₅ : (⟨s₀.gpr .a3, 8 * slots⟩ : Region) ∈ s₅.wr := by rw [wr₅]; exact hwB
  -- The values, byte-swapped into registers.
  obtain ⟨hKA, hKB⟩ := kaD_eq (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2
  have hKA' : kaD2 KL KR = _ := hKA
  have hKB' : kaD3 KL KR = _ := hKB
  obtain ⟨s₆, e₆, v₆, o₆, m₆, rd₆, wr₆⟩ := loadValues_ok (s := s₅) (by rw [hb₅]; exact hscr₅)
    [(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
      (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
      (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2] (fun v hv => by
      rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_using [hv]) with rfl | rfl | rfl | rfl
      · exact h₅.kl hpre
      · exact h₅.kr hpre
      · have := h₅.ka (by decide); rw [hKA'] at this; exact this
      · have := h₅.kb (by decide); rw [hKB'] at this; exact this)
  obtain hnv : ∀ r : Reg, r ∈ [sb, Reg.a2, Reg.a3] → ∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v := by decide
  obtain hb₆ : s₆.gpr sb = s₀.gpr .a3 := by rw [o₆ _ (hnv _ (by simp)) (by decide), hb₅]
  obtain r6₅ : s₅.gpr .a3 = s₀.gpr .a1 := by
    rw [h₅.regs _ (by decide) (by decide) (by decide) (by decide), r6₄]
  -- The key's length.
  obtain ⟨s₈, e₈, z₈, g₈, m₈, rd₈, wr₈⟩ := subI_ok s₆ t0 .a3 16 (by decide)
  obtain hz₈ : (s₈.gpr t0 == 0) = decide ((s₀.gpr .a1).toNat = 16) := by
    rw [z₈, o₆ _ (hnv _ (by simp)) (by decide), r6₅]
    conv => lhs; rw [show s₀.gpr .a1 = BitVec.ofNat 64 (s₀.gpr .a1).toNat by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [VG.Offset.ofNat_sub_ofNat_beq (by omega_using []) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₈, by rw [runBlock_append', e₆, Option.bind_some, e₈], ?_⟩)
  -- The subkeys.
  obtain hx2₈ : s₈.gpr .a2 = s₀.gpr .a2 := by
    rw [g₈ _ (by decide), o₆ _ (hnv _ (by simp)) (by decide), h₅.regs _ (by decide) (by decide) (by decide) (by decide), r5₄]
  obtain hwS₈ : (⟨s₀.gpr .a2, 272⟩ : Region) ∈ s₈.wr := by rw [wr₈, wr₆, wr₅]; exact hwS
  obtain hg₈ : ∀ v < 4, s₈.gpr (hiReg v) = hiW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) ∧
      s₈.gpr (loReg v) = loW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) :=
    fun v hv => by
      obtain ⟨n1, -, n3, -⟩ := hiReg_ne v hv
      rw [g₈ _ n1, g₈ _ n3]; exact v₆ v hv
  obtain hklen : key.length = (s₀.gpr .a1).toNat := by rw [← hkey]; simp [Spec.Camellia.bytesAt]
  refine WP.seq (WP.mono (Q := StoresPost s₈ (s₀.gpr .a2) (s₀.gpr .a1).toNat key)
    (WP.ite (decide ((s₀.gpr .a1).toNat = 16)) ((eval_zero s₈ t0).trans (by rw [hz₈])) (fun h16 => ?_)
      (fun h16 => ?_))
    fun s₉ h₉ => ?_)
  · have h16 : (s₀.gpr .a1).toNat = 16 := by simpa using h16
    exact stores_wp hx2₈ hwS₈ subkeys_lt4.1 (by rw [subkeys_length.1]; omega_using []) hg₈
      (by rw [h16, subkeys_length.1]; rfl) (by rw [hklen, ite_eq_left h16])
  · have h16 : (s₀.gpr .a1).toNat ≠ 16 := by simpa using h16
    exact stores_wp hx2₈ hwS₈ subkeys_lt4.2 (by rw [subkeys_length.2]) hg₈
      (by rw [subkeys_length.2]; simp only [Spec.Camellia.rounds, h16, ↓reduceIte]; rfl)
      (by rw [hklen, ite_eq_right h16])
  -- The epilogue.
  obtain hb₉ : s₉.gpr sb = s₀.gpr .a3 := by rw [h₉.regs _ (by decide) (by decide), g₈ _ (by decide), hb₆]
  obtain hSB : ∀ k, savedSlot ≤ k → k < savedSlot + 12 →
      s₉.mem.readW (wordAddr (s₀.gpr .a3) k) 64 = s₁.mem.readW (wordAddr (s₀.gpr .a3) k) 64 := by
    intro k h1 h2
    rw [h₉.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dSB.sub_right (by rw [wordAddr]; exact VG.Offset.sub_base _ (by omega_using [hE, hS, h2]))).symm) (by decide)]
    have := h₅.keep k (by omega_using [h1]) (by omega_using [hE, hS, h2]) (Or.inl (by omega_using [hW, hE, h2]))
    rw [hs₄, sl₂ k (by omega_using [hE, hS, h2]) (Or.inl (by omega_using [hl', hE, h2]))] at this
    simp only [slotW, hb₅, b₁] at this
    rw [m₈, m₆]
    exact this
  obtain ⟨s₁₀, e₁₀, rg₁₀, -, m₁₀, -, -⟩ := restore_ok (s₀ := s₀) (b := s₀.gpr .a3)
    (by rw [h₉.wr, wr₈, wr₆, wr₅]; exact hwB) hb₉ hal (fun i hi => by
      rw [hSB _ (by omega_using []) (by omega_using [hi])]; exact sv₁ i hi)
  refine WP.of_runBlock ⟨s₁₀, e₁₀, rg₁₀, ?_⟩
  show Spec.Camellia.bytesAt s₁₀.mem (s₀.gpr .a2) _ = _
  rw [hkey, m₁₀, ← h₉.bytes]

end VG.Proof.Camellia.RISCV64

end

end


/-!
# The Camellia key schedule on RISC-V meets its contracts

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyVerified.lean`):
`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time (`expandKey_ct`). `expandKey_framed` runs it with its working space on
the stack, zeroed on return: 3200 bytes, for the 400 words of the scratch
buffer.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.Impl.Camellia.RISCV64

/-- The registers the key schedule writes. -/
def expandKeyWrites : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7,
   .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

theorem expandKey_correct (s : State) (hs : expandKeyRISCV64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyRISCV64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, hk⟩ := WP.keep expandKeyWrites (expandKey_wp hs) (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hk.gpr (by decide)⟩, h₂⟩
  obtain ⟨i, hi, rfl⟩ := preserved_sreg r hr
  exact h₁ i hi

/-- A state satisfying the precondition (a key of 16 bytes). -/
def expandKeySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x3000, 272⟩, ⟨0x4000, 8 * 400⟩]

theorem expandKey_verified :
    Verified target expandKey (Proof.Camellia.expandKeyScratchContract abi slots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Camellia.expandKeyScratchContract, Proof.Camellia.expandKeyScratchSig,
      Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre, Spec.Camellia.expandKeyPost, expandKeyRISCV64,
      abi, argRegs, slots, tailSlot, savedSlot, keySlot] [expandKeySat]
      using expandKeySat)

/-- A state satisfying the key schedule's precondition: a key of 16 bytes at
`0x1000`, the schedule at `0x3000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x3000, 272⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Camellia.expandKeyContract abi 3200).pre s := by
  implies_sat [Spec.Camellia.expandKeyContract, Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre,
    Spec.Camellia.expandKeyPost, abi, argRegs] [expandKeyFrameSat] using expandKeyFrameSat

/-- The key schedule, with its working space on the stack. -/
theorem expandKey_framed :
    Verified target (Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a3 400 expandKey)
      (Spec.Camellia.expandKeyContract abi 3200) :=
  Verified.stackScratchWiped (sig := Spec.Camellia.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 400) (pre := Spec.Camellia.expandKeyPre abi.ptrBits)
    (post := Spec.Camellia.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3200) (words := 400) (by rw [← Proof.Camellia.expandKeyScratchContract_eq]; exact expandKey_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Camellia.RISCV64
