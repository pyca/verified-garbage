import VerifiedGarbage.Proof.Sm4.X86.Linear
import VerifiedGarbage.Proof.Sm4.X86.Sbox
import VerifiedGarbage.Proof.Sm4.Rounds
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A round of bitsliced SM4 on x86 (32-bit)

As on ARMv7 (`Proof/Sm4/Arm/Round.lean`): `round_ok`, with the state's four
words in their slots (`StRel`) and the round key's planes at entry `a` of
`kp`, `round l a a b c d` replaces word `a` of every block's state with its
new value (`sround`), keeping the other words and writing only the slots
below the table. The layers are composed from their checks
(`Linear.lean`, `Sbox.lean`) and `W32.round_rel`.
-/

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Bitslice (lanes bitOf xorBits bitOf_word xorBits_cons xorBits_nil)
open VG.Impl.Aes.X86 (sb tmpRegs)
open VG.Proof.Sm4 (sround W32.WordRel W32.termsXor W32.round_rel)
open VG.Impl.Sm4 (Lin)

/-- Word `k` of the table entries at `kp`. -/
abbrev keyW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr kp) k) 32

/-- The planes of the state's word `w`. -/
def planes (s : State) (w : Nat) : Nat → BitVec 32 := fun j => slotW s (stateSlot w j)

/-- The state's words hold the blocks' states: word `w` of block `b` is `X b w`. -/
def StRel (s : State) (X : Nat → Nat → Spec.Sm4.Word) : Prop :=
  ∀ w < 4, W32.WordRel (planes s w) (fun b => X b w)

theorem planes_eq (s : State) (w j : Nat) : planes s w j = slotW s (32 + (8 * w + j)) := by
  simp only [planes, stateSlot, Nat.add_assoc]

theorem stateIns_mem {x j i : Nat} (h : (j, i) ∈ stateIns x) : ∃ k < 32, j = 32 + k ∧ i = x + k := by
  simp only [stateIns, List.mem_map, List.mem_range, Prod.mk.injEq] at h
  obtain ⟨k, hk, rfl, rfl⟩ := h
  exact ⟨k, hk, rfl, rfl⟩

theorem stateKeep_mem {x a k : Nat} (hk : k < 32) (ha : k / 8 ≠ a) :
    (32 + k, fun p => [32 * (x + k) + p]) ∈ stateKeep x a := by
  simp only [stateKeep, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨k, ⟨hk, by simpa using ha⟩, rfl⟩

/-- A slot kept by a linear block: its output is its own input word. -/
theorem keep_word {W : Nat → BitVec 32} {i : Nat} {v v' : BitVec 32} (hW : W i = v)
    (h : ∀ p < 32, v'.getLsbD p = xorBits W [32 * i + p]) : v' = v :=
  BitVec.eq_of_getLsbD_eq fun p hp => by
    rw [h p hp, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, hW]

theorem xorBits_map32 (W : Nat → BitVec 32) (l : List (Nat × Nat)) (hl : ∀ wt ∈ l, wt.2 < 32) :
    xorBits W (l.map fun wt => 32 * wt.1 + wt.2) = W32.termsXor W l := by
  induction l with
  | nil => rfl
  | cons wt l ih =>
    simp only [List.map_cons, xorBits_cons, W32.termsXor, List.foldr_cons] at ih ⊢
    rw [bitOf_word _ _ _ (hl wt (by simp)), ih fun v hv => hl v (by simp [hv])]

theorem termsXor_congr {W S : Nat → BitVec 32} (hS : ∀ i < 8, W i = S i) :
    ∀ l : List (Nat × Nat), (∀ wt ∈ l, wt.1 < 8) → W32.termsXor W l = W32.termsXor S l
  | [], _ => rfl
  | wt :: l, h => by
    have ih := termsXor_congr hS l fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [W32.termsXor, List.foldr_cons] at ih ⊢
    rw [hS wt.1 (h wt List.mem_cons_self), ih]

/-- The linear layer's terms, as the bits of the S-box's output. -/
theorem xorBits_terms (W S : Nat → BitVec 32) (hS : ∀ i < 8, W i = S i) (l : List (Nat × Nat))
    (hl : ∀ sm ∈ l, sm.1 < 8) (p : Nat) :
    xorBits W (l.map fun sm => 32 * sm.1 + W32.rotP p sm.2) =
      W32.termsXor S (l.map fun sm => (sm.1, W32.rotP p sm.2)) := by
  rw [show (l.map fun sm => 32 * sm.1 + W32.rotP p sm.2) =
      ((l.map fun sm => (sm.1, W32.rotP p sm.2)).map fun wt => 32 * wt.1 + wt.2) by simp,
    xorBits_map32 W _ (fun wt hwt => by
      simp only [List.mem_map] at hwt; obtain ⟨sm, _, rfl⟩ := hwt; exact Nat.mod_lt _ (by decide))]
  exact termsXor_congr hS _ fun wt hwt => by
    simp only [List.mem_map] at hwt; obtain ⟨sm, hsm, rfl⟩ := hwt; exact hl sm hsm

theorem ok_sbox {s : State} (h : Ok layerCfg s) : Ok sboxCfg s where
  slotIn k hk := h.slotIn k (by simp [sboxCfg, layerCfg, tableSlot] at hk ⊢; omega_arith)
  extIn k hk := by simp [sboxCfg] at hk
  fit := by have := h.fit; simp [sboxCfg, layerCfg, tableSlot] at this ⊢; omega_arith
  sep k _ j hj := by simp [sboxCfg] at hj

theorem ok_lin {s : State} (h : Ok layerCfg s) : Ok linCfg s where
  slotIn k hk := h.slotIn k (by simpa [linCfg, layerCfg] using hk)
  extIn k hk := by simp [linCfg] at hk
  fit := by have := h.fit; simpa [linCfg, layerCfg] using this
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

/-- A frame of the first `n` slots keeps slot `k ≥ n`. -/
theorem slot_above {m m' : Mem} {b : BitVec 32} {n k : Nat} (hf : Frame [⟨b.setWidth 64, 4 * n⟩] m m')
    (hk : n ≤ k) (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  have e : wordAddr b k = b.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega_arith)
  rw [e]
  exact hf.readW (r := ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have : (b.setWidth 64).toNat = b.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega_arith)]
      exact VG.Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)

/-- A round, with the round key at entry `a` of `kp`. -/
theorem round_ok (l : Lin) {a b c d : Nat} (ha : a < 4)
    (hb : b = (a + 1) % 4) (hc : c = (a + 2) % 4) (hd : d = (a + 3) % 4)
    (hpre : check (lanes 32 11) layerCfg (linExt 32) (preX a b c d) (linEnv (stateIns 0))
      (linPost tableSlot 11 (preOuts a b c d)) = true)
    (hlin : check (lanes 32 11) linCfg (linExt 40) (lin l a) (linEnv linIns)
      (linPost tableSlot 11 (linOuts l a)) = true)
    (hall : ([Reg.esp, .esi, .edi].all fun r => (preX a b c d ++ lin l a).all fun i => i.dst != some r) = true)
    {s : State} (hok : Ok layerCfg s) {X : Nat → Nat → Spec.Sm4.Word} {k : Spec.Sm4.Word}
    (hX : StRel s X) (hK : W32.WordRel (fun j => keyW s (8 * a + j)) fun _ => k) :
    ∃ s', runBlock isa (round l a a b c d) s = some s' ∧
      StRel s' (fun b' => sround l k a (X b')) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem := by
  have hall' : ∀ r, r ∉ tmpRegs → ((preX a b c d).all fun i => i.dst != some r) = true ∧
      ((lin l a).all fun i => i.dst != some r) = true := fun r hr => by
    have := List.all_eq_true.mp hall r (not_tmp r hr)
    rw [List.all_append, Bool.and_eq_true] at this
    exact this
  have hsb : sb ∉ tmpRegs := by decide
  have hkp : kp ∉ tmpRegs := by decide
  have hfit := hok.fit
  simp only [layerCfg, tableSlot] at hfit
  -- The S-box's input.
  let W₁ : Nat → BitVec 32 := fun i => if i < 32 then slotW s (32 + i) else keyW s (i - 32)
  obtain ⟨s₁, h₁, x₁, rd₁, wr₁, o₁, f₁⟩ := linear_ok hpre hok W₁
    (fun j i hji hj => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by omega_arith, by simp [W₁, hk]; rfl⟩)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₁, show ¬ 32 + j < 32 by omega_arith]; rfl⟩)
  simp only [layerCfg] at x₁
  have b₁ : s₁.gpr sb = s.gpr sb := o₁ _ (hall' sb hsb).1
  have kp₁ : s₁.gpr kp = s.gpr kp := o₁ _ (hall' kp hkp).1
  have hW₁ : ∀ w < 4, ∀ j < 8, W₁ (8 * w + j) = planes s w j := fun w hw j hj => by
    simp only [W₁, show 8 * w + j < 32 by omega_arith, ↓reduceIte, planes_eq]
  have hXb : ∀ j < 8, ∀ p < 32, (slotW s₁ j).getLsbD p =
      ((((planes s b j).getLsbD p ^^ (planes s c j).getLsbD p) ^^ (planes s d j).getLsbD p) ^^
        (keyW s (8 * a + j)).getLsbD p) := by
    intro j hj p hp
    have hb4 : b < 4 := by omega_arith
    have hc4 : c < 4 := by omega_arith
    have hd4 : d < 4 := by omega_arith
    rw [slotW, b₁, x₁ j (preG a b c d j) (List.mem_append_left _
        (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)) p hp,
      preG, xorBits_cons, xorBits_cons, xorBits_cons, xorBits_cons, xorBits_nil, bitOf_word _ _ _ hp,
      bitOf_word _ _ _ hp, bitOf_word _ _ _ hp, bitOf_word _ _ _ hp, hW₁ b hb4 j hj, hW₁ c hc4 j hj,
      hW₁ d hd4 j hj]
    simp only [W₁, show ¬ 32 + 8 * a + j < 32 by omega_arith, ↓reduceIte, show 32 + 8 * a + j - 32 = 8 * a + j by omega_arith,
      Bool.xor_false, Bool.xor_assoc]
  have hok₁ : Ok layerCfg s₁ := hok.congr b₁ kp₁ rd₁ wr₁
  have keep₁ : ∀ k < 32, slotW s₁ (32 + k) = slotW s (32 + k) := fun k hk => by
    rw [slotW, b₁]
    exact keep_word (W := W₁) (i := 0 + k) (by simp [W₁, hk])
      (x₁ (32 + k) _ (List.mem_append_right _ (stateKeep_mem (x := 0) (a := 4) hk (by omega_arith))))
  -- The S-box.
  obtain ⟨s₂, h₂, sx₂, rd₂, wr₂, o₂, f₂⟩ := sbox_ok (ok_sbox hok₁)
  have b₂ : s₂.gpr sb = s.gpr sb := (o₂ sb hsb).trans b₁
  have hok₂ : Ok layerCfg s₂ := hok₁.congr (o₂ sb hsb) (o₂ kp hkp) rd₂ wr₂
  have keep₂ : ∀ k < 32, slotW s₂ (32 + k) = slotW s (32 + k) := fun k hk => by
    rw [← keep₁ k hk]
    simp only [slotW, o₂ sb hsb]
    refine slot_above (n := 32) (by simpa [slotRegion, sboxCfg] using f₂) (by omega_arith) ?_
    rw [b₁]; omega_arith
  -- The linear layer, into word `a`.
  let W₃ : Nat → BitVec 32 := fun i => if i < 8 then slotW s₂ i else slotW s₂ (32 + (i - 8))
  obtain ⟨s₃, h₃, y₃, rd₃, wr₃, o₃, f₃⟩ := linear_ok hlin (ok_lin hok₂) W₃
    (fun j i hji hj => by
      simp only [linIns, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      rcases hji with ⟨k, hk, rfl, rfl⟩ | hji
      · exact ⟨by omega_arith, by simp [W₃, hk]; rfl⟩
      · obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
        exact ⟨by omega_arith, by simp [W₃, show ¬ 8 + k < 8 by omega_arith]; rfl⟩)
    (fun j hj => by simp [linCfg] at hj)
  simp only [linCfg] at y₃
  have b₃ : s₃.gpr sb = s.gpr sb := (o₃ _ ((hall' sb hsb).2)).trans b₂
  have hA' : ∀ j < 8, ∀ p < 32, (planes s₃ a j).getLsbD p =
      ((planes s a j).getLsbD p ^^ W32.termsXor (slotW s₂) ((l.terms j).map fun sm => (sm.1, W32.rotP p sm.2))) := by
    intro j hj p hp
    have := y₃ (stateSlot a j) (linG l a j) (List.mem_append_left _
      (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)) p hp
    rw [planes, slotW, b₃, ← b₂, this, linG, xorBits_cons, bitOf_word _ _ _ hp,
      xorBits_terms W₃ (slotW s₂) (fun i hi => by simp [W₃, hi]) _ (Proof.Sm4.terms_lt l j hj)]
    simp only [W₃, show ¬ 8 + 8 * a + j < 8 by omega_arith, ↓reduceIte, show 32 + (8 + 8 * a + j - 8) = 32 + (8 * a + j) by omega_arith,
      keep₂ _ (show 8 * a + j < 32 by omega_arith), planes_eq]
  refine ⟨s₃, ?_, fun w hw => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], fun r hr => ?_, ?_⟩
  · rw [round, runBlock_app, runBlock_app, h₁, Option.bind_some, h₂, Option.bind_some, h₃]
  · by_cases hwa : w = a
    · subst hwa
      have hr := W32.round_rel l (hX b (by omega_arith)) (hX c (by omega_arith)) (hX d (by omega_arith)) hK (hX w hw) hXb sx₂ hA'
      refine hr.congr_right fun b' _ => ?_
      simp only [sround, ↓reduceIte, hb, hc, hd]
    · refine (hX w hw).congr (fun j hj => ?_) |>.congr_right fun b' _ => by simp only [sround, hwa, ↓reduceIte]
      show planes s₃ w j = planes s w j
      have hk : 8 * w + j < 32 := by omega_arith
      rw [planes_eq, planes_eq, slotW, b₃, ← b₂,
        keep_word (W := W₃) (i := 8 + (8 * w + j)) (v := slotW s₂ (32 + (8 * w + j)))
          (by simp [W₃, show ¬ 8 + (8 * w + j) < 8 by omega_arith])
          (y₃ _ _ (List.mem_append_right _ (stateKeep_mem (x := 8) (a := a) hk (by omega_arith)))),
        keep₂ _ hk]
  · rw [o₃ r (hall' r hr).2, o₂ r hr, o₁ r (hall' r hr).1]
  · have e₂ : slotRegion linCfg s₂ = slotRegion layerCfg s := by simp only [slotRegion, linCfg, layerCfg, b₂]
    refine f₁.trans ((f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans (e₂ ▸ f₃))
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, sboxCfg, layerCfg, b₁]
    exact Region.sub_prefix (by simp [tableSlot])

end VG.Proof.Sm4.X86
