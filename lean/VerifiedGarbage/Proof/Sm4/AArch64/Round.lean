import VerifiedGarbage.Proof.Sm4.AArch64.Linear
import VerifiedGarbage.Proof.Sm4.AArch64.Sbox
import VerifiedGarbage.Proof.Sm4.Rounds
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A round of bitsliced SM4 on AArch64

`round_ok`: with the state's four words in their slots (`StRel`) and the
round key's planes at entry `a` of `kp`, `round l a a b c d` (the other words
`b`, `c`, `d` the next ones, cyclically) replaces word `a` of every block's
state with its new value (`sround`), keeping the other words and the masks,
and writing only the slots below the table. The layers are composed from
their checks (`Linear.lean`, `Sbox.lean`) and `round_rel`.
-/

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Sm4.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1)
open VG.AArch64.Straight (linEnvG linPostG linG_ok)
open VG.Proof.Sm4 (WordRel rotP round_rel sround)
open VG.Impl.Sm4 (Lin)
open VG.Proof.Aes (bsByte termsXor xorBits_map)

/-- The planes in the state registers. -/
abbrev Qs (s : State) (i : Nat) : BitVec 64 := s.gpr (q i)

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr sb) k) 64

/-- Word `k` of the table entries at `kp`. -/
abbrev keyW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr kp) k) 64

/-- The masks are in their slots. -/
def MasksOk (s : State) : Prop := ∀ kv ∈ keyMasks, slotW s kv.1 = kv.2

/-- The planes of the state's word `w`. -/
def planes (s : State) (w : Nat) : Nat → BitVec 64 := fun j => slotW s (stateSlot w j)

/-- The state's words hold the blocks' states: word `w` of block `b` is `X b w`. -/
def StRel (s : State) (X : Nat → Nat → Spec.Sm4.Word) : Prop :=
  ∀ w < 4, WordRel (planes s w) (fun b => X b w)

theorem mask_lt {kv : Nat × BitVec 64} (hkv : kv ∈ keyMasks) : kv.1 < 64 := by
  simp [keyMasks] at hkv; rcases hkv with h | h | h <;> subst h <;> simp [evenSlot, oddSlot, grpSlot]

theorem ok_sbox {s : State} (h : Ok layerCfg s) : Ok sboxCfg s where
  slotIn k hk := h.slotIn k (by simp [sboxCfg, layerCfg, tableSlot] at hk ⊢; omega)
  extIn k hk := by simp [sboxCfg] at hk
  slots := by simp [sboxCfg]
  sep k _ j hj := by simp [sboxCfg] at hj

/-- The frame of the S-box (its spills) keeps the slots from 48 on. -/
theorem slot_above {m m' : Mem} {b : Addr} {n k : Nat} (hf : Frame [⟨b, 8 * n⟩] m m') (hk : n ≤ k)
    (hk' : k < 2 ^ 58) : m'.readW (wordAddr b k) 64 = m.readW (wordAddr b k) 64 :=
  hf.readW (r := ⟨wordAddr b k, 8⟩) (by simp only [Region.Contains]; simp) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base b (by omega) (by omega)) (by decide)

theorem stateIns_mem {x j i : Nat} (h : (j, i) ∈ stateIns x) : ∃ k < 32, j = 64 + k ∧ i = x + k := by
  simp only [stateIns, List.mem_map, List.mem_range, Prod.mk.injEq] at h
  obtain ⟨k, hk, rfl, rfl⟩ := h
  exact ⟨k, hk, rfl, rfl⟩

theorem masks_in {s : State} (hm : MasksOk s) : ∀ kv ∈ keyMasks, kv.1 < layerCfg.slots ∧
    s.mem.readW (wordAddr (s.gpr layerCfg.base) kv.1) 64 = kv.2 := fun kv hkv =>
  ⟨by have := mask_lt hkv; simp only [layerCfg, tableSlot]; omega, hm kv hkv⟩

theorem planes_eq (s : State) (w j : Nat) : planes s w j = slotW s (64 + (8 * w + j)) := by
  simp only [planes, stateSlot, Nat.add_assoc]

theorem termsXor_congr {W S : Nat → BitVec 64} (hS : ∀ i < 8, W i = S i) :
    ∀ l : List (Nat × Nat), (∀ wt ∈ l, wt.1 < 8) → termsXor W l = termsXor S l
  | [], _ => rfl
  | wt :: l, h => by
    have ih := termsXor_congr hS l fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [termsXor, List.foldr_cons] at ih ⊢
    rw [hS wt.1 (h wt List.mem_cons_self), ih]

/-- The linear layer's terms, as the bits of the S-box's output. -/
theorem xorBits_terms (W S : Nat → BitVec 64) (hS : ∀ i < 8, W i = S i) (l : List (Nat × Nat))
    (hl : ∀ sm ∈ l, sm.1 < 8) (p : Nat) :
    xorBits W (l.map fun sm => 64 * sm.1 + rotP p sm.2) =
      termsXor S (l.map fun sm => (sm.1, rotP p sm.2)) := by
  rw [show (l.map fun sm => 64 * sm.1 + rotP p sm.2) =
      ((l.map fun sm => (sm.1, rotP p sm.2)).map fun wt => 64 * wt.1 + wt.2) by simp,
    xorBits_map W _ (fun wt hwt => by
      simp only [List.mem_map] at hwt; obtain ⟨sm, _, rfl⟩ := hwt; exact Nat.mod_lt _ (by decide))]
  exact termsXor_congr hS _ fun wt hwt => by
    simp only [List.mem_map] at hwt; obtain ⟨sm, hsm, rfl⟩ := hwt; exact hl sm hsm

theorem ok_lin {s : State} (h : Ok layerCfg s) : Ok linCfg s where
  slotIn k hk := h.slotIn k (by simpa [linCfg, layerCfg] using hk)
  extIn k hk := by simp [linCfg] at hk
  slots := by simp [linCfg, tableSlot]
  sep k _ j hj := by simp [linCfg] at hj

theorem runBlock_app (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some, ih]

/-- A round, with the round key at entry `a` of `kp`. -/
theorem round_ok (l : Lin) {a b c d : Nat} (ha : a < 4)
    (hb : b = (a + 1) % 4) (hc : c = (a + 2) % 4) (hd : d = (a + 3) % 4)
    (hpre : check (lanes 64 12) layerCfg (linExt 32) (preX a b c d) preEnv
      (linPostG 12 (qOuts (preG a b c d)) [] (keyMaskSlots ++ stateSlots) preEnv) = true)
    (hlin : check (lanes 64 12) linCfg (linExt 40) (lin l a) linEnv
      (linPostG 12 [] (linOuts l a) (linKeep a) linEnv) = true)
    (hall : (layerKeep.all fun r =>
      (preX a b c d ++ lin l a).all fun i => dstOf i != some r) = true)
    {s : State} (hok : Ok layerCfg s) (hm : MasksOk s) {X : Nat → Nat → Spec.Sm4.Word} {k : Spec.Sm4.Word}
    (hX : StRel s X) (hK : WordRel (fun j => keyW s (8 * a + j)) fun _ => k) :
    ∃ s', runBlock isa (round l a a b c d) s = some s' ∧
      StRel s' (fun b' => sround l k a (X b')) ∧ MasksOk s' ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem := by
  have hall' : ∀ r, r ∉ layerWrites → ((preX a b c d).all fun i => dstOf i != some r) = true ∧
      ((lin l a).all fun i => dstOf i != some r) = true := fun r hr => by
    have := List.all_eq_true.mp hall r (not_layerWrites r hr)
    rw [List.all_append, Bool.and_eq_true] at this
    exact this
  have hsb : sb ∉ layerWrites := by decide
  have hkp : kp ∉ layerWrites := by decide
  -- The S-box's input.
  let W₁ : Nat → BitVec 64 := fun i => if i < 32 then slotW s (64 + i) else keyW s (i - 32)
  obtain ⟨s₁, h₁, x₁, -, k₁, rd₁, wr₁, sp₁, o₁, f₁, -, -⟩ := linG_ok hpre hok W₁
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [layerCfg, tableSlot]; omega, by omega, by simp [W₁, hk]; rfl⟩)
    (masks_in hm)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega, by simp [W₁, show ¬ 32 + j < 32 by omega]; rfl⟩)
  have b₁ : s₁.gpr sb = s.gpr sb := o₁ _ (hall' sb hsb).1
  have kp₁ : s₁.gpr kp = s.gpr kp := o₁ _ (hall' kp hkp).1
  have hW₁ : ∀ w < 4, ∀ j < 8, W₁ (8 * w + j) = planes s w j := fun w hw j hj => by
    simp only [W₁, show 8 * w + j < 32 by omega, ↓reduceIte, planes_eq]
  have hXb : ∀ j < 8, ∀ p < 64, (Qs s₁ j).getLsbD p =
      ((((planes s b j).getLsbD p ^^ (planes s c j).getLsbD p) ^^ (planes s d j).getLsbD p) ^^
        (keyW s (8 * a + j)).getLsbD p) := by
    intro j hj p hp
    have hb4 : b < 4 := by omega
    have hc4 : c < 4 := by omega
    have hd4 : d < 4 := by omega
    rw [x₁ (q j) (preG a b c d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp,
      preG, xorBits_cons, xorBits_cons, xorBits_cons, xorBits_cons, xorBits_nil, bitOf_word _ _ _ hp,
      bitOf_word _ _ _ hp, bitOf_word _ _ _ hp, bitOf_word _ _ _ hp, hW₁ b hb4 j hj, hW₁ c hc4 j hj,
      hW₁ d hd4 j hj]
    simp only [W₁, show ¬ 32 + 8 * a + j < 32 by omega, ↓reduceIte, show 32 + 8 * a + j - 32 = 8 * a + j by omega,
      Bool.xor_false, Bool.xor_assoc]
  have hok₁ : Ok layerCfg s₁ := hok.congr b₁ kp₁ rd₁ wr₁
  have keep₁ : ∀ k ∈ keyMaskSlots ++ stateSlots, slotW s₁ k = slotW s k := fun k hk => by
    have hk' : k < layerCfg.slots := by
      simp only [keyMaskSlots, stateSlots, keyMasks, List.mem_append, List.mem_map, List.mem_range,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
      simp only [layerCfg, tableSlot]
      rcases hk with ((h | h | h) | ⟨x, hx, rfl⟩) <;> (try subst h) <;> (try simp only [evenSlot, oddSlot, grpSlot]) <;> omega
    have := k₁ k hk hk'
    simp only [layerCfg] at this
    rw [slotW, b₁, this]
  -- The S-box.
  obtain ⟨s₂, h₂, sx₂, rd₂, wr₂, sp₂, o₂, f₂⟩ := sbox_ok (ok_sbox hok₁)
  have b₂ : s₂.gpr sb = s.gpr sb := (o₂ sb hsb).trans b₁
  have kp₂ : s₂.gpr kp = s.gpr kp := (o₂ kp hkp).trans kp₁
  have hok₂ : Ok layerCfg s₂ := hok₁.congr (o₂ sb hsb) (o₂ kp hkp) rd₂ wr₂
  have above₂ : ∀ k, 48 ≤ k → k < tableSlot → slotW s₂ k = slotW s₁ k := fun k h1 h2 => by
    simp only [slotW, o₂ sb hsb]
    exact slot_above (n := 48) f₂ h1 (by simp [tableSlot] at h2; omega)
  have keep₂ : ∀ k ∈ keyMaskSlots ++ stateSlots, slotW s₂ k = slotW s k := fun k hk => by
    have hk' : 48 ≤ k ∧ k < tableSlot := by
      simp only [keyMaskSlots, stateSlots, keyMasks, List.mem_append, List.mem_map, List.mem_range,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with ((h | h | h) | ⟨x, hx, rfl⟩) <;> (try subst h) <;> (try simp only [evenSlot, oddSlot, grpSlot, tableSlot]) <;> omega
    rw [above₂ k hk'.1 hk'.2, keep₁ k hk]
  have hm₂ : MasksOk s₂ := fun kv hkv => by
    rw [keep₂ kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv))]; exact hm kv hkv
  have hst₂ : ∀ w < 4, ∀ j < 8, slotW s₂ (64 + (8 * w + j)) = planes s w j := fun w hw j hj => by
    rw [keep₂ _ (List.mem_append_right _ (by
      simp only [stateSlots, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega, rfl⟩)), planes_eq]
  -- The linear layer, into word `a`.
  let W₃ : Nat → BitVec 64 := fun i => if i < 8 then Qs s₂ i else slotW s₂ (64 + (i - 8))
  obtain ⟨s₃, h₃, -, y₃, k₃, rd₃, wr₃, sp₃, o₃, f₃, -, -⟩ := linG_ok hlin (ok_lin hok₂) W₃
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega, by simp [W₃, hi]⟩)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [linCfg, tableSlot]; omega, by omega, by
        simp [W₃, show ¬ 8 + k < 8 by omega]; rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [linCfg, tableSlot]; omega, hm₂ kv hkv⟩)
    (fun j hj => by simp [linCfg] at hj)
  have b₃ : s₃.gpr sb = s.gpr sb := (o₃ _ ((hall' sb hsb).2)).trans b₂
  have hA' : ∀ j < 8, ∀ p < 64, (planes s₃ a j).getLsbD p =
      ((planes s a j).getLsbD p ^^ termsXor (Qs s₂) ((l.terms j).map fun sm => (sm.1, rotP p sm.2))) := by
    intro j hj p hp
    have := y₃ (stateSlot a j) (linG l a j) (by simp only [linOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      (by simp [stateSlot, linCfg, tableSlot]; omega) p hp
    simp only [linCfg] at this
    rw [planes, slotW, b₃, ← b₂, this, linG, xorBits_cons, bitOf_word _ _ _ hp,
      xorBits_terms W₃ (Qs s₂) (fun i hi => by simp [W₃, hi]) _ (Proof.Sm4.terms_lt l j hj)]
    simp only [W₃, show ¬ 8 + 8 * a + j < 8 by omega, ↓reduceIte, show 64 + (8 + 8 * a + j - 8) = 64 + (8 * a + j) by omega,
      hst₂ a ha j hj]
  have keep₃ : ∀ k ∈ linKeep a, slotW s₃ k = slotW s₂ k := fun k hk => by
    have hk' : k < linCfg.slots := by
      simp only [linKeep, keyMaskSlots, keyMasks, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
      simp only [linCfg, tableSlot]
      rcases hk with ((h | h | h) | ⟨x, ⟨hx, -⟩, rfl⟩) <;> (try subst h) <;> (try simp only [evenSlot, oddSlot, grpSlot]) <;> omega
    have := k₃ k hk hk'
    simp only [linCfg] at this
    rw [slotW, b₃, ← b₂, this]
  refine ⟨s₃, ?_, fun w hw => ?_, fun kv hkv => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁],
    by rw [sp₃, sp₂, sp₁], fun r hr => ?_, ?_⟩
  · rw [round, runBlock_app, runBlock_app, h₁, Option.bind_some, h₂, Option.bind_some, h₃]
  · by_cases hwa : w = a
    · subst hwa
      have hr := round_rel l (hX b (by omega)) (hX c (by omega)) (hX d (by omega)) hK (hX w hw) hXb sx₂ hA'
      refine hr.congr_right fun b' _ => ?_
      simp only [sround, ↓reduceIte, hb, hc, hd]
    · refine (hX w hw).congr (fun j hj => ?_) |>.congr_right fun b' _ => by simp only [sround, hwa, ↓reduceIte]
      show planes s₃ w j = planes s w j
      rw [planes_eq, planes_eq, keep₃ _ (List.mem_append_right _ (by
        simp only [List.mem_map, List.mem_filter, List.mem_range]
        exact ⟨8 * w + j, ⟨by omega, by simp; omega⟩, rfl⟩)), hst₂ w hw j hj, planes_eq]
  · rw [keep₃ kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv))]; exact hm₂ kv hkv
  · rw [o₃ r (hall' r hr).2, o₂ r hr, o₁ r (hall' r hr).1]
  · have e₁ : slotRegion layerCfg s₁ = slotRegion layerCfg s := by simp only [slotRegion, layerCfg, b₁]
    have e₂ : slotRegion linCfg s₂ = slotRegion layerCfg s := by simp only [slotRegion, linCfg, layerCfg, b₂]
    refine f₁.trans ((f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans (e₂ ▸ f₃))
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, sboxCfg, layerCfg, b₁]
    exact Region.sub_prefix (by simp [tableSlot])

end VG.Proof.Sm4.AArch64
