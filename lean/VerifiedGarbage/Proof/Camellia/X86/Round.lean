module

public import VerifiedGarbage.Proof.Camellia.X86.Linear
public import VerifiedGarbage.Proof.Camellia.X86.Sbox
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Camellia.Bitsliced

/-!
# A round of bitsliced Camellia on x86 (32-bit)

As on ARMv7 (`Proof/Camellia/Arm/Round.lean`), with the S-box's planes in
slots 0–7: `round_ok`, with the half `D1` (or `D2`) in its slots, the other
half in its slots and the subkey's planes at `kp`, `round off src dst`
leaves `d2 ^ F(d1, k)` in the other half's slots, keeping the first half's
and writing only the slots below the tail buffer. The layers are composed
from their checks (`Linear.lean`, `Sbox.lean`) and `W32.round_rel`.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Bitslice (lanes bitOf xorBits bitOf_word xorBits_cons xorBits_nil)
open VG.Impl.Aes.X86 (sb tmpRegs)
open VG.Proof.Camellia (pRow pRow_lt)

/-- Word `k` of the table entries at `kp`. -/
abbrev keyW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr kp) k) 32

/-- The sixteen planes of the half at slot `d`. -/
def half (s : State) (d : Nat) : Nat → BitVec 32 := fun i => slotW s (d + i)

/-- A slot kept by a linear block: its output is its own input word. -/
theorem keep_word {W : Nat → BitVec 32} {i : Nat} {v v' : BitVec 32} (hW : W i = v)
    (h : ∀ p < 32, v'.getLsbD p = xorBits W [32 * i + p]) : v' = v :=
  BitVec.eq_of_getLsbD_eq fun p hp => by
    rw [h p hp, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, hW]

theorem ok_sbox {s : State} (h : Ok layerCfg s) : Ok sboxCfg s where
  slotIn k hk := h.slotIn k (by simp [sboxCfg, layerCfg, tailSlot] at hk ⊢; omega)
  extIn k hk := by simp [sboxCfg] at hk
  fit := by have := h.fit; simp [sboxCfg, layerCfg, tailSlot] at this ⊢; omega
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
  have e : wordAddr b k = b.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega)
  rw [e]
  exact hf.readW (r := ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have : (b.setWidth 64).toNat = b.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
      exact VG.Offset.disjoint_base _ (by omega) (by omega)) (by decide)

/-- A frame of the slots keeps the external words. -/
theorem frame_ext {c : Cfg} {s : State} {m' : Mem} (hok : Ok c s) (hf : Frame [slotRegion c s] s.mem m')
    {j : Nat} (hj : j < c.exts) :
    m'.readW (wordAddr (s.gpr c.ext) j) 32 = s.mem.readW (wordAddr (s.gpr c.ext) j) 32 := by
  simp only [Mem.readW]
  rw [Mem.read_congr fun i hi => (hf _ fun r hr hc => ?_).symm]
  simp only [List.mem_singleton] at hr; subst hr
  have hfit := hok.fit
  simp only [slotRegion, Region.Contains] at hc
  have hb : ((s.gpr c.base).setWidth 64).toNat = (s.gpr c.base).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (s.gpr c.base).isLt; omega)]
  have hi' : i < 4 := by simpa using hi
  generalize hx : wordAddr (s.gpr c.ext) j + BitVec.ofNat 64 i = x at hc
  have hk : (x - (s.gpr c.base).setWidth 64).toNat / 4 < c.slots := by omega
  have hsep := hok.sep _ hk j hj x
  rw [wordAddr, addr_eq (by omega)] at hsep
  refine hsep ?_ (by rw [← hx, Mem.sub_ofNat_toNat _ (by omega)]; exact hi')
  generalize (s.gpr c.base).setWidth 64 = B at *
  bv_omega

/-- The P-function's terms, as the selected outputs of the S-boxes. -/
theorem xorBits_sel (W YL SR : Nat → BitVec 32) (hS : ∀ i < 8, W i = SR i) (hY : ∀ j < 8, W (8 + j) = YL j)
    {j b : Nat} (hj : j < 8) (hb : b < 8) :
    ∀ l : List Nat, (∀ c ∈ l, c < 8) → xorBits W (l.map (selG j b)) = W32.rowSel YL SR j b l
  | [], _ => rfl
  | c :: l, hl => by
    have hc := hl c List.mem_cons_self
    have ih := xorBits_sel W YL SR hS hY hj hb l fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, xorBits_cons, W32.rowSel, List.foldr_cons] at ih ⊢
    rw [ih]
    congr 1
    simp only [selG, W32.ySel]
    split
    · rw [Nat.add_assoc, bitOf_word _ _ _ (by omega), hY j hj]
    · rw [Nat.add_assoc, bitOf_word _ _ _ (by omega), hS _ (W32.outSrc_lt hj)]

/-- The two rounds of a pair: `D2 ^= F(D1, k)` with the first entry at
`kp`, `D1 ^= F(D2, k)` with the second. -/
def RoundCase (off src dst : Nat) : Prop :=
  (off = 0 ∧ src = d1Slot ∧ dst = d2Slot) ∨ (off = 16 ∧ src = d2Slot ∧ dst = d1Slot)

theorem halvesIns_mem {x j i : Nat} (h : (j, i) ∈ halvesIns x) : ∃ k < 32, j = d1Slot + k ∧ i = x + k := by
  simp only [halvesIns, List.mem_map, List.mem_range, Prod.mk.injEq] at h
  obtain ⟨k, hk, rfl, rfl⟩ := h
  exact ⟨k, hk, rfl, rfl⟩

theorem halvesKeep_mem {x k : Nat} (hk : k < 32) : keepOut (d1Slot + k) (x + k) ∈ halvesKeep x := by
  simp only [halvesKeep, List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩

/-- A round, with the subkey at word `off` of `kp`. -/
theorem round_ok {off src dst : Nat}
    (hA : check (lanes 32 11) layerCfg (linExt 32) (preL off src) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (preOuts off src)) = true)
    (hC : check (lanes 32 12) layerCfg (linExt 40) (midLR off src) (linEnv midIns)
      (linPost tailSlot 12 (midOuts off src)) = true)
    (hE : check (lanes 32 11) linCfg (linExt 48) (postP dst) (linEnv postIns)
      (linPost tailSlot 11 (postOuts dst)) = true)
    (hall : ([Reg.esp, .esi, .edi].all fun r =>
      (preL off src ++ midLR off src ++ postP dst).all fun i => i.dst != some r) = true)
    (hcase : RoundCase off src dst)
    {s : State} (hok : Ok layerCfg s) {d1 d2 : Nat → BitVec 64} {k : BitVec 64}
    (hQ : W32.HalfRel (half s src) d1) (hK : W32.HalfRel (fun i => keyW s (off + i)) fun _ => k)
    (hR : W32.HalfRel (half s dst) d2) :
    ∃ s', runBlock isa (round off src dst) s = some s' ∧
      W32.HalfRel (half s' dst) (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) ∧
      (∀ i < 16, slotW s' (src + i) = slotW s (src + i)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem := by
  have hall' : ∀ r, r ∉ tmpRegs → ((preL off src).all fun i => i.dst != some r) = true ∧
      ((midLR off src).all fun i => i.dst != some r) = true ∧
      ((postP dst).all fun i => i.dst != some r) = true := fun r hr => by
    have := List.all_eq_true.mp hall r (not_tmp r hr)
    simp only [List.all_append, Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hsb : sb ∉ tmpRegs := by decide
  have hkp : kp ∉ tmpRegs := by decide
  have hfit := hok.fit
  simp only [layerCfg, tailSlot] at hfit
  have hsd : (src = d1Slot ∧ dst = d2Slot) ∨ (src = d2Slot ∧ dst = d1Slot) := by
    rcases hcase with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  have hsrc : d1Slot ≤ src ∧ src + 16 ≤ d1Slot + 32 := by
    rcases hsd with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [d1Slot, d2Slot]
  have hdst : d1Slot ≤ dst ∧ dst + 16 ≤ d1Slot + 32 := by
    rcases hsd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [d1Slot, d2Slot]
  have hother : other dst = src := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hoff : off + 16 ≤ 32 := by rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  -- The left word's S-box input.
  let W₁ : Nat → BitVec 32 := fun i => if i < 32 then slotW s (d1Slot + i) else keyW s (i - 32)
  obtain ⟨s₁, h₁, x₁, rd₁, wr₁, o₁, f₁⟩ := linear_ok hA hok W₁
    (fun j i hji hj => by
      obtain ⟨k, hk, rfl, rfl⟩ := halvesIns_mem hji
      exact ⟨by omega_arith, by simp [W₁, hk]; rfl⟩)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₁, show ¬ 32 + j < 32 by omega_arith]; rfl⟩)
  simp only [layerCfg] at x₁
  have b₁ : s₁.gpr sb = s.gpr sb := o₁ _ (hall' sb hsb).1
  have kp₁ : s₁.gpr kp = s.gpr kp := o₁ _ (hall' kp hkp).1
  have hXL : ∀ j < 8, ∀ p < 32, (slotW s₁ j).getLsbD p =
      ((half s src (W32.inSrc (p / 8) j)).getLsbD p ^^ (keyW s (off + W32.inSrc (p / 8) j)).getLsbD p) := by
    intro j hj p hp
    have hi := W32.inSrc_lt (c := p / 8) hj
    rw [slotW, b₁, x₁ j (preG off src j) (List.mem_append_left _
        (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)) p hp,
      preG, xorBits_cons, xorBits_cons, xorBits_nil, bitOf_word _ _ _ hp, bitOf_word _ _ _ hp, Bool.xor_false]
    simp only [W₁, half, show src - d1Slot + W32.inSrc (p / 8) j < 32 by omega_arith, ↓reduceIte,
      show ¬ 32 + off + W32.inSrc (p / 8) j < 32 by omega_arith,
      show 32 + off + W32.inSrc (p / 8) j - 32 = off + W32.inSrc (p / 8) j by omega_arith,
      show d1Slot + (src - d1Slot + W32.inSrc (p / 8) j) = src + W32.inSrc (p / 8) j by omega_arith]
  have hok₁ : Ok layerCfg s₁ := hok.congr b₁ kp₁ rd₁ wr₁
  have keep₁ : ∀ i < 32, slotW s₁ (d1Slot + i) = slotW s (d1Slot + i) := fun i hi => by
    rw [slotW, b₁]
    exact keep_word (W := W₁) (i := 0 + i) (by simp [W₁, hi])
      (x₁ _ _ (List.mem_append_right _ (halvesKeep_mem (x := 0) hi)))
  have kw₁ : ∀ j < 32, keyW s₁ j = keyW s j := fun j hj => by
    simp only [keyW, kp₁]; exact frame_ext hok f₁ (by simpa [layerCfg] using hj)
  -- The left word's S-box.
  obtain ⟨s₂, h₂, sx₂, rd₂, wr₂, o₂, f₂⟩ := sbox_ok (ok_sbox hok₁)
  have b₂ : s₂.gpr sb = s.gpr sb := (o₂ sb hsb).trans b₁
  have kp₂ : s₂.gpr kp = s.gpr kp := (o₂ kp hkp).trans kp₁
  have hok₂ : Ok layerCfg s₂ := hok₁.congr (o₂ sb hsb) (o₂ kp hkp) rd₂ wr₂
  have above₂ : ∀ k, 32 ≤ k → k < tailSlot → slotW s₂ k = slotW s₁ k := fun k h1 h2 => by
    simp only [slotW, o₂ sb hsb]
    refine slot_above (n := 32) (by simpa [slotRegion, sboxCfg] using f₂) h1 ?_
    rw [b₁]; simp [tailSlot] at h2; omega_arith
  have sub₂ : ∀ {t : State}, Frame [slotRegion sboxCfg t] t.mem s₂.mem →
      Frame [slotRegion layerCfg t] t.mem s₂.mem := fun f => f.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by
      simp only [slotRegion, sboxCfg, layerCfg]; exact Region.sub_prefix (by simp [tailSlot])⟩
  have kw₂ : ∀ j < 32, keyW s₂ j = keyW s j := fun j hj => by
    rw [← kw₁ j hj]; simp only [keyW, o₂ kp hkp]
    exact frame_ext hok₁ (sub₂ f₂) (by simpa [layerCfg] using hj)
  have keep₂ : ∀ i < 32, slotW s₂ (d1Slot + i) = slotW s (d1Slot + i) := fun i hi => by
    rw [above₂ _ (by simp only [d1Slot]; omega_arith) (by simp [d1Slot, tailSlot]; omega_arith), keep₁ i hi]
  -- The left word's output selection, and the right word's S-box input.
  let W₃ : Nat → BitVec 32 := fun i =>
    if i < 8 then slotW s₂ i else if i < 40 then slotW s₂ (d1Slot + (i - 8)) else keyW s₂ (i - 40)
  obtain ⟨s₃, h₃, x₃, rd₃, wr₃, o₃, f₃⟩ := linear_ok hC hok₂ W₃
    (fun j i hji hj => by
      simp only [midIns, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      rcases hji with ⟨k, hk, rfl, rfl⟩ | hji
      · exact ⟨by omega_arith, by simp [W₃, hk]; rfl⟩
      · obtain ⟨k, hk, rfl, rfl⟩ := halvesIns_mem hji
        exact ⟨by omega_arith, by simp [W₃, show ¬ 8 + k < 8 by omega_arith, show 8 + k < 40 by omega_arith]; rfl⟩)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₃, show ¬ 40 + j < 8 by omega_arith, show ¬ 40 + j < 40 by omega_arith]; rfl⟩)
  simp only [layerCfg] at x₃
  have b₃' : s₃.gpr sb = s₂.gpr sb := o₃ _ (hall' sb hsb).2.1
  have b₃ : s₃.gpr sb = s.gpr sb := b₃'.trans b₂
  have kp₃ : s₃.gpr kp = s.gpr kp := (o₃ _ (hall' kp hkp).2.1).trans kp₂
  have hYL : ∀ j < 8, ∀ p < 32, (slotW s₃ (ylSlot + j)).getLsbD p = (slotW s₂ (W32.outSrc (p / 8) j)).getLsbD p := by
    intro j hj p hp
    have := x₃ (ylSlot + j) (ylG j) (List.mem_append_left _ (List.mem_append_right _
      (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))) p hp
    rw [slotW, b₃, ← b₂, this, ylG, xorBits_cons, xorBits_nil, bitOf_word _ _ _ hp, Bool.xor_false]
    simp only [W₃, W32.outSrc_lt hj, ↓reduceIte]
  have hXR : ∀ j < 8, ∀ p < 32, (slotW s₃ j).getLsbD p =
      ((half s src (8 + W32.inSrc (4 + p / 8) j)).getLsbD p ^^
        (keyW s (off + (8 + W32.inSrc (4 + p / 8) j))).getLsbD p) := by
    intro j hj p hp
    have hi := W32.inSrc_lt (c := 4 + p / 8) hj
    rw [slotW, b₃, ← b₂, x₃ j (midG off src j) (List.mem_append_left _ (List.mem_append_left _
        (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))) p hp,
      midG, xorBits_cons, xorBits_cons, xorBits_nil, bitOf_word _ _ _ hp, bitOf_word _ _ _ hp, Bool.xor_false]
    simp only [W₃, half, show ¬ 16 + (src - d1Slot) + W32.inSrc (4 + p / 8) j < 8 by omega_arith,
      show 16 + (src - d1Slot) + W32.inSrc (4 + p / 8) j < 40 by omega_arith, ↓reduceIte,
      show ¬ 48 + off + W32.inSrc (4 + p / 8) j < 8 by omega_arith,
      show ¬ 48 + off + W32.inSrc (4 + p / 8) j < 40 by omega_arith,
      show 48 + off + W32.inSrc (4 + p / 8) j - 40 = off + (8 + W32.inSrc (4 + p / 8) j) by omega_arith,
      kw₂ _ (show off + (8 + W32.inSrc (4 + p / 8) j) < 32 by omega_arith),
      show d1Slot + (16 + (src - d1Slot) + W32.inSrc (4 + p / 8) j - 8) =
        src + (8 + W32.inSrc (4 + p / 8) j) by omega_arith]
    rw [show src + (8 + W32.inSrc (4 + p / 8) j) = d1Slot + (src - d1Slot + 8 + W32.inSrc (4 + p / 8) j) by omega_arith,
      keep₂ _ (by omega_arith)]
  have hok₃ : Ok layerCfg s₃ := hok₂.congr b₃' (o₃ _ (hall' kp hkp).2.1) rd₃ wr₃
  have keep₃ : ∀ i < 32, slotW s₃ (d1Slot + i) = slotW s (d1Slot + i) := fun i hi => by
    rw [slotW, b₃']
    rw [keep_word (W := W₃) (i := 8 + i) (v := slotW s₂ (d1Slot + i))
      (by simp [W₃, show ¬ 8 + i < 8 by omega_arith, show 8 + i < 40 by omega_arith])
      (x₃ _ _ (List.mem_append_right _ (halvesKeep_mem (x := 8) hi)))]
    exact keep₂ i hi
  -- The right word's S-box.
  obtain ⟨s₄, h₄, sx₄, rd₄, wr₄, o₄, f₄⟩ := sbox_ok (ok_sbox hok₃)
  have b₄ : s₄.gpr sb = s.gpr sb := (o₄ sb hsb).trans b₃
  have hok₄ : Ok layerCfg s₄ := hok₃.congr (o₄ sb hsb) (o₄ kp hkp) rd₄ wr₄
  have above₄ : ∀ k, 32 ≤ k → k < tailSlot → slotW s₄ k = slotW s₃ k := fun k h1 h2 => by
    simp only [slotW, o₄ sb hsb]
    refine slot_above (n := 32) (by simpa [slotRegion, sboxCfg] using f₄) h1 ?_
    rw [b₃]; simp [tailSlot] at h2; omega_arith
  -- The right word's output selection, the P-function and the XOR.
  let W₅ : Nat → BitVec 32 := fun i => if i < 8 then slotW s₄ i else slotW s₄ (ylSlot + (i - 8))
  obtain ⟨s₅, h₅, y₅, rd₅, wr₅, o₅, f₅⟩ := linear_ok hE (ok_lin hok₄) W₅
    (fun j i hji hj => by
      simp only [postIns, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      rcases hji with ⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩
      · exact ⟨by omega_arith, by simp [W₅, hk]; rfl⟩
      · exact ⟨by omega_arith, by simp [W₅, show ¬ 8 + k < 8 by omega_arith]; rfl⟩)
    (fun j hj => by simp [linCfg] at hj)
  simp only [linCfg] at y₅
  have b₅' : s₅.gpr sb = s₄.gpr sb := o₅ _ (hall' sb hsb).2.2
  have hW₅ : ∀ i < 32, W₅ (16 + i) = slotW s (d1Slot + i) := fun i hi => by
    simp only [W₅, show ¬ 16 + i < 8 by omega_arith, ↓reduceIte, show ylSlot + (16 + i - 8) = d1Slot + i by
      simp [ylSlot, d1Slot]; omega_arith]
    rw [above₄ _ (by simp only [d1Slot]; omega_arith) (by simp [d1Slot, tailSlot]; omega_arith), keep₃ i hi]
  have hR' : ∀ w < 2, ∀ j < 8, ∀ p < 32, (half s₅ dst (8 * w + j)).getLsbD p =
      ((half s dst (8 * w + j)).getLsbD p ^^
        W32.rowSel (fun j => slotW s₃ (ylSlot + j)) (slotW s₄) j (p % 8) (pRow (4 * w + p / 8))) := by
    intro w hw j hj p hp
    have := y₅ (dst + (8 * w + j)) (postG dst w j)
      (List.mem_append_left _ (by
        simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
        exact ⟨8 * w + j, by omega_arith, rfl, by
          rw [show (8 * w + j) / 8 = w by omega_arith, show (8 * w + j) % 8 = j by omega_arith]⟩)) p hp
    rw [half, slotW, b₅', this, postG, xorBits_cons, bitOf_word _ _ _ hp,
      show 16 + (dst - d1Slot) + 8 * w + j = 16 + (dst - d1Slot + 8 * w + j) by omega_arith,
      hW₅ _ (by omega_arith), show d1Slot + (dst - d1Slot + 8 * w + j) = dst + (8 * w + j) by omega_arith,
      xorBits_sel W₅ (fun j => slotW s₃ (ylSlot + j)) (slotW s₄) (fun i hi => by simp [W₅, hi])
        (fun j hj => by
          simp only [W₅, show ¬ 8 + j < 8 by omega_arith, ↓reduceIte, show 8 + j - 8 = j by omega_arith]
          exact above₄ _ (by simp [ylSlot]) (by simp [ylSlot, tailSlot]; omega_arith))
        hj (by omega_arith) _ fun c hc => pRow_lt hc]
    rfl
  have hD := W32.round_rel hQ hK hR hXL sx₂ (fun j hj p hp => hYL j hj p hp) hXR sx₄ hR'
  refine ⟨s₅, ?_, hD, fun i hi => ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁],
    fun r hr => ?_, ?_⟩
  · rw [round, runBlock_app, runBlock_app, runBlock_app, runBlock_app, h₁, Option.bind_some, h₂,
      Option.bind_some, h₃, Option.bind_some, h₄, Option.bind_some, h₅]
  · have hk : keepOut (other dst + i) (16 + (other dst - d1Slot) + i) ∈ postOuts dst :=
      List.mem_append_right _ (by simp only [List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
    have hv := keep_word (W := W₅) (i := 16 + (other dst - d1Slot) + i) (v := slotW s (src + i)) ?_ (y₅ _ _ hk)
    · rw [hother] at hv; rw [slotW, b₅', hv]
    · rw [hother, show 16 + (src - d1Slot) + i = 16 + (src - d1Slot + i) by omega_arith, hW₅ _ (by omega_arith),
        show d1Slot + (src - d1Slot + i) = src + i by omega_arith]
  · rw [o₅ r (hall' r hr).2.2, o₄ r hr, o₃ r (hall' r hr).2.1, o₂ r hr, o₁ r (hall' r hr).1]
  · have sbs : ∀ {t : State}, t.gpr sb = s.gpr sb → ∀ r ∈ [slotRegion sboxCfg t],
        ∃ r' ∈ [slotRegion layerCfg s], Region.Sub r r' := fun ht r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by
        simp only [slotRegion, sboxCfg, layerCfg, ht]; exact Region.sub_prefix (by decide)⟩
    have e₂ : slotRegion layerCfg s₂ = slotRegion layerCfg s := by simp only [slotRegion, layerCfg, b₂]
    have e₄ : slotRegion linCfg s₄ = slotRegion layerCfg s := by simp only [slotRegion, linCfg, layerCfg, b₄]
    have g₂ : Frame [slotRegion layerCfg s] s₁.mem s₂.mem := f₂.sub (sbs b₁)
    have g₃ : Frame [slotRegion layerCfg s] s₂.mem s₃.mem := by rw [← e₂]; exact f₃
    have g₄ : Frame [slotRegion layerCfg s] s₃.mem s₄.mem := f₄.sub (sbs b₃)
    have g₅ : Frame [slotRegion layerCfg s] s₄.mem s₅.mem := by rw [← e₄]; exact f₅
    exact f₁.trans (g₂.trans (g₃.trans (g₄.trans g₅)))

/-- The checks and the registers of both rounds of a pair. -/
theorem round0_ok {s : State} (hok : Ok layerCfg s) {d1 d2 : Nat → BitVec 64} {k : BitVec 64}
    (hQ : W32.HalfRel (half s d1Slot) d1) (hK : W32.HalfRel (fun i => keyW s (0 + i)) fun _ => k)
    (hR : W32.HalfRel (half s d2Slot) d2) :
    ∃ s', runBlock isa (round 0 d1Slot d2Slot) s = some s' ∧
      W32.HalfRel (half s' d2Slot) (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) ∧
      (∀ i < 16, slotW s' (d1Slot + i) = slotW s (d1Slot + i)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem :=
  round_ok preL0_check mid0_check post2_check (by decide +kernel) (.inl ⟨rfl, rfl, rfl⟩) hok hQ hK hR

theorem round16_ok {s : State} (hok : Ok layerCfg s) {d1 d2 : Nat → BitVec 64} {k : BitVec 64}
    (hQ : W32.HalfRel (half s d2Slot) d1) (hK : W32.HalfRel (fun i => keyW s (16 + i)) fun _ => k)
    (hR : W32.HalfRel (half s d1Slot) d2) :
    ∃ s', runBlock isa (round 16 d2Slot d1Slot) s = some s' ∧
      W32.HalfRel (half s' d1Slot) (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) ∧
      (∀ i < 16, slotW s' (d2Slot + i) = slotW s (d2Slot + i)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem :=
  round_ok preL16_check mid16_check post1_check (by decide +kernel) (.inr ⟨rfl, rfl, rfl⟩) hok hQ hK hR

end VG.Proof.Camellia.X86
