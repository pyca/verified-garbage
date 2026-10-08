import VerifiedGarbage.Proof.Camellia.AArch64.Linear
import VerifiedGarbage.Proof.Camellia.AArch64.Sbox
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Camellia.AArch64.Fl

/-!
# A round of bitsliced Camellia on AArch64

`round_ok`: with the half `D1` (or `D2`) in the state registers, the other
half in its slots and the subkey's planes at `kp`, `round off d` leaves
`d2 ^ F(d1, k)` in both the state registers and the other half's slots,
keeping the masks and the first half's slots, and writing only the slots
below the table. The layers are composed from their checks
(`Linear.lean`, `Sbox.lean`) and `round_rel`.
-/

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 kp)
open VG.Proof.Camellia (HalfRel toBsG fromBsG keyInG outPG inSrc outSrc pRow pos cpos rowBits round_rel)
open VG.Proof.Aes (bsByte)

/-- The planes in the state registers. -/
abbrev Qs (s : State) (i : Nat) : BitVec 64 := s.gpr (q i)

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr sb) k) 64

/-- Word `k` of the table entry at `kp`. -/
abbrev keyW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr kp) k) 64

/-- The masks are in their slots. -/
def MasksOk (s : State) : Prop := ∀ kv ∈ layerMasks, slotW s kv.1 = kv.2

theorem ok_sbox {s : State} (h : Ok layerCfg s) : Ok sboxCfg s where
  slotIn k hk := h.slotIn k (by simp [sboxCfg, layerCfg, keySlot] at hk ⊢; omega)
  extIn k hk := by simp [sboxCfg] at hk
  slots := by simp [sboxCfg]
  sep k _ j hj := by simp [sboxCfg] at hj

theorem xorBits_map_rows (W : Nat → BitVec 64) (S : Nat → BitVec 64) (hS : ∀ i < 8, W i = S i)
    (j b : Nat) (hb : b < 8) (hj : j < 8) (l : List Nat) (hl : ∀ i ∈ l, i < 8) :
    xorBits W (l.map fun i => 64 * outSrc (cpos i) j + 8 * cpos i + b) = rowBits S j b l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hi := hl i List.mem_cons_self
    have hc : cpos i < 8 := Camellia.cpos_lt hi
    have ho : outSrc (cpos i) j < 8 := by simp only [outSrc]; split <;> (try split) <;> omega
    simp only [List.map_cons, xorBits_cons, rowBits, List.foldr_cons] at ih ⊢
    rw [Nat.add_assoc, bitOf_word _ _ _ (by omega), hS _ ho, ih fun i' hi' => hl i' (List.mem_cons_of_mem _ hi')]

/-- The frame of the S-box (its spills) keeps the slots from 48 on. -/
theorem slot_above {m m' : Mem} {b : Addr} {n k : Nat} (hf : Frame [⟨b, 8 * n⟩] m m') (hk : n ≤ k)
    (hk' : k < 2 ^ 58) : m'.readW (wordAddr b k) 64 = m.readW (wordAddr b k) 64 :=
  hf.readW (r := ⟨wordAddr b k, 8⟩) (by simp only [Region.Contains]; simp) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base b (by omega) (by omega)) (by decide)

/-- A round, with the subkey at word `off` of `kp` and the other half at slot `d`. -/
theorem round_ok {off d : Nat}
    (hkc : check (lanes 64 12) layerCfg (linExt 8) (keyXor off ++ inSel) keyInEnv
      (linPostG 12 (qOuts (keyInG off)) [] (maskSlots ++ halvesIns.map (·.1)) keyInEnv) = true)
    (hfc : check (lanes 64 12) layerCfg (linExt 24) (feistel d) bothEnv
      (linPostG 12 (qOuts (feistelG d)) ((List.range 8).map fun j => (d + j, feistelG d j))
        (feistelKeep d) bothEnv) = true)
    (hoff : off = 0 ∨ off = 8) (hd : d = d1Slot ∨ d = d2Slot)
    {s : State} (hok : Ok layerCfg s) (hm : MasksOk s) {d1 d2 : Nat → BitVec 64} {k : BitVec 64}
    (hQ : HalfRel (Qs s) d1) (hK : HalfRel (fun j => keyW s (off + j)) fun _ => k)
    (hR : HalfRel (fun j => slotW s (d + j)) d2) :
    ∃ s', runBlock isa (round off d) s = some s' ∧
      HalfRel (Qs s') (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) ∧
      HalfRel (fun j => slotW s' (d + j)) (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) ∧
      MasksOk s' ∧ (∀ j < 16, d1Slot + j < d ∨ d + 8 ≤ d1Slot + j →
        slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem := by
  have hcode : round off d = (keyXor off ++ inSel) ++ (Impl.Camellia.AArch64.sboxCode ++
      ((outSel ++ pLayer) ++ feistel d)) := by simp only [round, List.append_assoc]
  have hsb : ∀ is : List Instr, ∀ s₁ s₂ : State,
      (∀ r, (is.all fun i => dstOf i != some r) = true → s₂.gpr r = s₁.gpr r) →
      (is.all fun i => dstOf i != some sb) = true → s₂.gpr sb = s₁.gpr sb := fun _ _ _ h h' => h _ h'
  -- The subkey XOR and input selection.
  let W₁ : Nat → BitVec 64 := fun i =>
    if i < 8 then Qs s i else if i < 24 then keyW s (i - 8) else slotW s (d1Slot + (i - 24))
  obtain ⟨s₁, h₁, x₁, -, k₁, rd₁, wr₁, sp₁, o₁, f₁, -, -⟩ := linG_ok hkc hok W₁
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega, by simp [W₁, hi]⟩)
    (fun j i hji => by
      simp only [halvesIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨j, hj, rfl, rfl⟩ := hji
      refine ⟨by simp [layerCfg, d1Slot, keySlot]; omega, by omega, ?_⟩
      simp [W₁, show ¬ 24 + j < 8 by omega, show ¬ 24 + j < 24 by omega]; rfl)
    (fun kv hkv => ⟨by simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [layerCfg, keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot], hm kv hkv⟩)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega, by simp [W₁, show ¬ 8 + j < 8 by omega, show 8 + j < 24 by omega]; rfl⟩)
  have hX : ∀ j < 8, ∀ p < 64, (Qs s₁ j).getLsbD p =
      ((Qs s (inSrc (p / 8) j)).getLsbD p ^^ (keyW s (off + inSrc (p / 8) j)).getLsbD p) := by
    intro j hj p hp
    have hi : inSrc (p / 8) j < 8 := by simp only [inSrc]; split <;> omega
    have := x₁ (q j) (keyInG off j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp
    rw [this, keyInG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false,
      bitOf_word _ _ _ hp, bitOf_word _ _ _ hp]
    simp [W₁, hi, show ¬ 8 + off + inSrc (p / 8) j < 8 by omega,
      show 8 + off + inSrc (p / 8) j < 24 by rcases hoff with h | h <;> subst h <;> omega,
      show 8 + off + inSrc (p / 8) j - 8 = off + inSrc (p / 8) j by omega]
  have hok₁ : Ok layerCfg s₁ := hok.congr (o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)) (o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)) rd₁ wr₁
  have hm₁ : MasksOk s₁ := fun kv hkv => by
    have hb : s₁.gpr sb = s.gpr sb := o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)
    have := k₁ kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [layerCfg, keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot])
    simp only [layerCfg] at this
    rw [slotW, hb, this]; exact hm kv hkv
  have hh₁ : ∀ j < 16, slotW s₁ (d1Slot + j) = slotW s (d1Slot + j) := fun j hj => by
    have hb : s₁.gpr sb = s.gpr sb := o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)
    have := k₁ (d1Slot + j) (List.mem_append_right _ (by
      simp only [halvesIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp [layerCfg, keySlot, d1Slot]; omega)
    simp only [layerCfg] at this
    rw [slotW, hb, this]
  -- The S-box.
  obtain ⟨s₂, h₂, sx₂, rd₂, wr₂, sp₂, o₂, f₂⟩ := sbox_ok (ok_sbox hok₁)
  have b₂ : s₂.gpr sb = s.gpr sb := (o₂ sb (by decide)).trans (o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel))
  have kp₂ : s₂.gpr kp = s.gpr kp := (o₂ kp (by decide)).trans (o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel))
  have hok₂ : Ok layerCfg s₂ := hok₁.congr (o₂ sb (by decide)) (o₂ kp (by decide)) rd₂ wr₂
  have above₂ : ∀ k, 48 ≤ k → k < keySlot → slotW s₂ k = slotW s₁ k := fun k h1 h2 => by
    simp only [slotW, o₂ sb (by decide)]
    exact slot_above (n := 48) f₂ h1 (by simp [keySlot] at h2; omega)
  have hm₂ : MasksOk s₂ := fun kv hkv => by
    rw [above₂ _ (by simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot])
      (by simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot])]
    exact hm₁ kv hkv
  have hh₂ : ∀ j < 16, slotW s₂ (d1Slot + j) = slotW s (d1Slot + j) := fun j hj => by
    rw [above₂ _ (by simp [d1Slot]; omega) (by simp [d1Slot, keySlot]; omega), hh₁ j hj]
  -- The output selection and the P-function.
  let W₃ : Nat → BitVec 64 := fun i =>
    if i < 8 then Qs s₂ i else if i < 24 then slotW s₂ (d1Slot + (i - 8)) else keyW s₂ (i - 24)
  have bothIns_ok : ∀ s' : State, (W : Nat → BitVec 64) →
      (∀ i, 8 ≤ i → i < 24 → W i = slotW s' (d1Slot + (i - 8))) →
      ∀ j i, (j, i) ∈ bothIns → j < layerCfg.slots ∧ 64 * i + 64 ≤ 2 ^ 12 ∧
        W i = s'.mem.readW (wordAddr (s'.gpr layerCfg.base) j) 64 := by
    intro s' W hW j i hji
    simp only [bothIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
    obtain ⟨j, hj, rfl, rfl⟩ := hji
    refine ⟨by simp [layerCfg, d1Slot, keySlot]; omega, by omega, ?_⟩
    rw [hW _ (by omega) (by omega), show 8 + j - 8 = j by omega]; rfl
  have masks_ok : ∀ s' : State, MasksOk s' → ∀ kv ∈ layerMasks, kv.1 < layerCfg.slots ∧
      s'.mem.readW (wordAddr (s'.gpr layerCfg.base) kv.1) 64 = kv.2 := fun s' hm' kv hkv =>
    ⟨by simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
      simp [layerCfg, keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot], hm' kv hkv⟩
  obtain ⟨s₃, h₃, y₃, -, k₃, rd₃, wr₃, sp₃, o₃, f₃, -, -⟩ := linG_ok outP_check hok₂ W₃
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega, by simp [W₃, hi]⟩)
    (bothIns_ok s₂ W₃ fun i h1 h2 => by simp [W₃, show ¬ i < 8 by omega, h2])
    (masks_ok s₂ hm₂)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega, by simp [W₃, show ¬ 24 + j < 8 by omega, show ¬ 24 + j < 24 by omega]; rfl⟩)
  have hY : ∀ j < 8, ∀ p < 64, (Qs s₃ j).getLsbD p = rowBits (Qs s₂) j (p % 8) (pRow (pos (p / 8))) := by
    intro j hj p hp
    rw [y₃ (q j) (outPG j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp,
      outPG]
    exact xorBits_map_rows W₃ (Qs s₂) (fun i hi => by simp [W₃, hi]) j (p % 8) (by omega) hj _
      fun i hi => Camellia.pRow_lt hi
  have b₃ : s₃.gpr sb = s₂.gpr sb := o₃ _ (by decide +kernel)
  have kp₃ : s₃.gpr kp = s₂.gpr kp := o₃ _ (by decide +kernel)
  have hok₃ : Ok layerCfg s₃ := hok₂.congr b₃ kp₃ rd₃ wr₃
  have hm₃ : MasksOk s₃ := fun kv hkv => by
    have := k₃ kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (masks_ok s₂ hm₂ kv hkv).1
    simp only [layerCfg] at this
    rw [slotW, b₃, this]; exact hm₂ kv hkv
  have hh₃ : ∀ j < 16, slotW s₃ (d1Slot + j) = slotW s (d1Slot + j) := fun j hj => by
    have := k₃ (d1Slot + j) (List.mem_append_right _ (by
      simp only [bothIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp [layerCfg, keySlot, d1Slot]; omega)
    simp only [layerCfg] at this
    rw [slotW, b₃, this, ← hh₂ j hj]
  -- The Feistel XOR.
  let W₄ : Nat → BitVec 64 := fun i =>
    if i < 8 then Qs s₃ i else if i < 24 then slotW s₃ (d1Slot + (i - 8)) else keyW s₃ (i - 24)
  obtain ⟨s₄, h₄, r₄, sl₄, k₄, rd₄, wr₄, sp₄, o₄, f₄, -, -⟩ := linG_ok hfc hok₃ W₄
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega, by simp [W₄, hi]⟩)
    (bothIns_ok s₃ W₄ fun i h1 h2 => by simp [W₄, show ¬ i < 8 by omega, h2])
    (masks_ok s₃ hm₃)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega, by simp [W₄, show ¬ 24 + j < 8 by omega, show ¬ 24 + j < 24 by omega]; rfl⟩)
  have hdj : ∀ j < 8, d + j = d1Slot + (d - d1Slot + j) := fun j _ => by
    rcases hd with rfl | rfl <;> simp [d1Slot, d2Slot] <;> omega
  have hd8 : d - d1Slot < 16 - 7 := by rcases hd with rfl | rfl <;> simp [d1Slot, d2Slot]
  have hfe : ∀ j < 8, ∀ p < 64, xorBits W₄ (feistelG d j p) =
      ((Qs s₃ j).getLsbD p ^^ (slotW s (d + j)).getLsbD p) := by
    intro j hj p hp
    rw [feistelG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp,
      bitOf_word _ _ _ hp, hdj j hj, ← hh₃ _ (by omega)]
    simp [W₄, hj, show ¬ 8 + (d - d1Slot) + j < 8 by omega, show 8 + (d - d1Slot) + j < 24 by omega,
      show 8 + (d - d1Slot) + j - 8 = d - d1Slot + j by omega]
  have b₄ : s₄.gpr sb = s₃.gpr sb := o₄ _ (by rcases hd with rfl | rfl <;> decide +kernel)
  have hD : HalfRel (Qs s₄) (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) :=
    round_rel hQ hK hR hX sx₂ hY fun j hj p hp => by
      rw [r₄ (q j) (feistelG d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
        p hp, hfe j hj p hp, Bool.xor_comm]
  have hS : HalfRel (fun j => slotW s₄ (d + j)) (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) :=
    round_rel hQ hK hR hX sx₂ hY fun j hj p hp => by
      have := sl₄ (d + j) (feistelG d j) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
        (by rcases hd with rfl | rfl <;> simp [layerCfg, keySlot, d1Slot, d2Slot] <;> omega) p hp
      simp only [layerCfg] at this
      rw [slotW, b₄, this, hfe j hj p hp, Bool.xor_comm]
  have keep_any : ∀ r, r ∉ layerWrites → ∀ is : List Instr,
      (layerKeep.all fun r => is.all fun i => dstOf i != some r) = true →
      (is.all fun i => dstOf i != some r) = true := fun r hr is h =>
    List.all_eq_true.mp h r (not_layerWrites r hr)
  refine ⟨s₄, ?_, hD, hS, ?_, ?_, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁],
    by rw [sp₄, sp₃, sp₂, sp₁], ?_, ?_⟩
  · rw [hcode, runBlock_append', h₁, Option.bind_some, runBlock_append', h₂, Option.bind_some,
      runBlock_append', h₃, Option.bind_some, h₄]
  · intro kv hkv
    have := k₄ kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (masks_ok s₃ hm₃ kv hkv).1
    simp only [layerCfg] at this
    rw [slotW, b₄, this]; exact hm₃ kv hkv
  · intro j hj hjd
    have hb : s₄.gpr sb = s.gpr sb := by rw [b₄, b₃, b₂]
    have hmem : d1Slot + j ∈ feistelKeep d := by
      refine List.mem_append_right _ ?_
      simp only [List.mem_map, List.mem_range]
      rcases hd with rfl | rfl
      · exact ⟨j - 8, by simp [d1Slot] at hjd; omega, by simp [d1Slot, d2Slot]; omega⟩
      · exact ⟨j, by simp [d1Slot, d2Slot] at hjd; omega, by simp [d1Slot, d2Slot]⟩
    have := k₄ _ hmem (by simp [layerCfg, keySlot, d1Slot]; omega)
    simp only [layerCfg] at this
    rw [slotW, b₄, this, ← hh₃ j hj, slotW, b₃]
  · intro r hr
    rw [o₄ r (keep_any r hr _ (by rcases hd with rfl | rfl <;> decide +kernel)),
      o₃ r (keep_any r hr _ (by decide +kernel)), o₂ r hr,
      o₁ r (keep_any r hr _ (by rcases hoff with rfl | rfl <;> decide +kernel))]
  · have e₁ : slotRegion layerCfg s₁ = slotRegion layerCfg s := by
      simp only [slotRegion, layerCfg]; rw [o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)]
    have e₂ : slotRegion layerCfg s₂ = slotRegion layerCfg s := by
      simp only [slotRegion, layerCfg]; rw [b₂]
    have e₃ : slotRegion layerCfg s₃ = slotRegion layerCfg s := by
      simp only [slotRegion, layerCfg]; rw [b₃, b₂]
    refine f₁.trans ((f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      ((e₂ ▸ f₃).trans (e₃ ▸ f₄)))
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, sboxCfg, layerCfg]
    rw [o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)]
    exact Region.sub_prefix (by simp [keySlot])

end VG.Proof.Camellia.AArch64
