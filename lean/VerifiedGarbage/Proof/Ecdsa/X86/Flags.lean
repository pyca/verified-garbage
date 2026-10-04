import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Impl.Ecdsa.X86

/-!
# ECDSA on x86 (32-bit): the masks of the checks, and the flag

The checks of `Impl/Ecdsa/X86.lean` as masks, all ones or zero:
`nonzero a` sets `edx` to all ones iff `[a] ≠ 0` (`nonzero_ok`), `ltN a` sets
`eax` to all ones iff `[a] < [MN]` (`ltN_ok`), and `andFlag` ands `edx` into
the flag word (`andFlag_ok`); so `checkRange a` ands the mask of
`0 < [a] < [MN]` into the flag (`checkRange_ok`) and `checkNonzero a` the mask
of `[a] ≠ 0` (`checkNonzero_ok`).
-/

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

/-- A mask: all ones if `p`, else zero. -/
abbrev mask32 (p : Prop) [Decidable p] : BitVec 32 := if p then BitVec.allOnes 32 else 0

theorem mask32_and (p q : Prop) [Decidable p] [Decidable q] : mask32 p &&& mask32 q = mask32 (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [mask32, hp, hq, ite_true, ite_false, and_self, and_false, false_and] <;> decide

/-- The flag word. -/
abbrev flagW (c : Cfg) (base : Addr) (s : State) : BitVec 32 := s.mem.readW (off base (c.sl FLAG)) 32

/-! ## Nonzero -/

/-- The `or`s of `nonzero`. -/
theorem ors_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat} :
    ∀ k, a + 4 * (k + 1) ≤ size →
    WP isa (.block ((List.range k).map fun j => .alu .or .edx (.mem (sc (a + 4 * (j + 1)))))) s fun s' =>
      (s'.gpr .edx = 0 ↔ s.gpr .edx = 0 ∧ ∀ j < k, w32 s.mem base (a + 4 * (j + 1)) = 0) ∧
      Keeps [.edx] s s' ∧ s'.mem = s.mem
  | 0, _ => WP.block_nil ⟨⟨fun h => ⟨h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩, fun h => h.1⟩,
      Keeps.refl _ _, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (ors_ok hs k (by omega)) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    refine wp_orS (readSrc_sc hs₁ (d := a + 4 * (k + 1)) (by omega)) fun s₂ u₂ => WP.block_nil
      ⟨?_, k₁.trans u₂.keeps, by rw [u₂.mem, m₁]⟩
    have hor : ∀ x y : BitVec 32, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
    rw [u₂.gpr, hor, e₁, m₁]
    have hw : (s.mem.readW (off base (a + 4 * (k + 1))) 32 = 0) ↔ w32 s.mem base (a + 4 * (k + 1)) = 0 :=
      ⟨fun h => by simp [w32, h], fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hw]
    constructor
    · intro ⟨⟨h₀, h⟩, hw⟩
      refine ⟨h₀, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j k with hj' | hj'
      · exact h j hj'
      · obtain rfl : j = k := by omega
        exact hw
    · intro ⟨h₀, h⟩
      exact ⟨⟨h₀, fun j hj => h j (by omega)⟩, h k (by omega)⟩

/-- `sbb r, r`: the mask of the borrow. -/
theorem sbb_mask (x : BitVec 32) (c : Bool) :
    x - x - (BitVec.ofBool c).setWidth 32 = mask32 (c = true) := by
  rw [BitVec.sub_self]
  cases c <;> decide

/-- `edx` is all ones iff `[a] ≠ 0`; `ecx` changes too. -/
theorem nonzero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) :
    WP isa (.block (c.nonzero a)) s fun s' =>
      s'.gpr .edx = mask32 (wordsVal s.mem base a c.n ≠ 0) ∧ Keeps [.ecx, .edx] s s' ∧ s'.mem = s.mem := by
  simp only [Cfg.nonzero, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs (d := a) (by omega)) fun s₁ u₁ _ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  refine WP.block_append (WP.mono (ors_ok hs₁ (2 * c.n - 1) (by omega)) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  rw [u₁.gpr, u₁.mem] at e₂
  have hz : s₂.gpr .edx = 0 ↔ wordsVal s.mem base a c.n = 0 := by
    rw [e₂, wordsVal_eq_val32, val32_eq_zero_iff]
    have hw : (s.mem.readW (off base a) 32 = 0) ↔ w32 s.mem base a = 0 :=
      ⟨fun h => by simp [w32, h], fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hw]
    constructor
    · intro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · simpa using h₀
      · exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 (by omega), fun j hj => h (j + 1) (by omega)⟩
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_subS rfl fun s₄ u₄ c₄ => ?_
  refine wp_sbbS rfl c₄ fun s₅ u₅ _ => WP.block_nil ⟨?_, ?_, by rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]⟩
  · rw [u₅.gpr, sbb_mask, u₃.gpr, u₃.other _ (by decide)]
    have : ((0 : BitVec 32).toNat < (s₂.gpr .edx).toNat) ↔ s₂.gpr .edx ≠ 0 :=
      ⟨fun h e => by rw [e] at h; exact Nat.lt_irrefl _ h,
        fun h => Nat.pos_of_ne_zero fun e => h (BitVec.eq_of_toNat_eq e)⟩
    simp only [mask32, decide_eq_true_eq, this, ne_eq, hz]
  · exact ((((u₁.keeps.mono (by decide)).widen k₂).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps

/-! ## Less than the order -/

/-- One word of the comparison of `[a]` with `[m]`. -/
def ltStep (a m j : Nat) : List Instr :=
  [.mov .edx (.mem (sc (a + 4 * j))), .alu (if j = 0 then .sub else .sbb) .edx (.mem (sc (m + 4 * j)))]

theorem ltN_eq (c : Cfg) (a : Nat) :
    c.ltN a = (List.range (2 * c.n)).flatMap (ltStep a (c.sl MN)) ++ ([.alu .sbb .eax (.reg .eax)] : List Instr) :=
  rfl

theorem ltStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a m j : Nat} {cin : Bool}
    (hop : (j = 0 ∧ cin = false) ∨ (j ≠ 0 ∧ s.cf = some cin))
    (ha : a + 4 * j + 4 ≤ size) (hm : m + 4 * j + 4 ≤ size) :
    WP isa (.block (ltStep a m j)) s fun s' =>
      s'.cf = some (decide (w32 s.mem base (a + 4 * j) < w32 s.mem base (m + 4 * j) + cin.toNat)) ∧
      Keeps [.edx] s s' ∧ s'.mem = s.mem := by
  simp only [ltStep]
  refine wp_movS (readSrc_sc hs (d := a + 4 * j) (by omega)) fun s₁ u₁ cf₁ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  rcases hop with ⟨rfl, rfl⟩ | ⟨hj, hc⟩
  · simp only [ite_true]
    refine wp_subS (readSrc_sc hs₁ (d := m + 4 * 0) (by omega)) fun s₂ u₂ c₂ => WP.block_nil
      ⟨by rw [c₂, u₁.gpr, u₁.mem]; simp [w32], u₁.keeps.trans u₂.keeps, by rw [u₂.mem, u₁.mem]⟩
  · simp only [hj, ite_false]
    refine wp_sbbS (readSrc_sc hs₁ (d := m + 4 * j) (by omega)) (by rw [cf₁]; exact hc) fun s₂ u₂ c₂ =>
      WP.block_nil ⟨by rw [c₂, u₁.gpr, u₁.mem], u₁.keeps.trans u₂.keeps, by rw [u₂.mem, u₁.mem]⟩

theorem ltSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a m : Nat} :
    ∀ k, a + 4 * (k + 1) ≤ size → m + 4 * (k + 1) ≤ size →
    WP isa (.block ((List.range (k + 1)).flatMap (ltStep a m))) s fun s' =>
      s'.cf = some (decide (val32 s.mem base a (k + 1) < val32 s.mem base m (k + 1))) ∧
      Keeps [.edx] s s' ∧ s'.mem = s.mem
  | 0, ha, hm => by
    rw [show (List.range (0 + 1)).flatMap (ltStep a m) = ltStep a m 0 from rfl]
    refine WP.mono (ltStep_ok hs (cin := false) (.inl ⟨rfl, rfl⟩) (by omega) (by omega))
      fun s' ⟨c', k', m'⟩ => ⟨?_, k', m'⟩
    rw [c']
    simp only [val32, Nat.mul_zero, Nat.add_zero, Bool.toNat_false]
    rfl
  | k + 1, ha, hm => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ltSteps_ok hs k (by omega) (by omega)) fun s₁ ⟨c₁, k₁, m₁⟩ => ?_)
    refine WP.mono (ltStep_ok (hs.of_keeps k₁ (by decide)) (j := k + 1) (.inr ⟨by omega, c₁⟩) (by omega) (by omega))
      fun s₂ ⟨c₂, k₂, m₂⟩ => ⟨?_, k₁.trans k₂, by rw [m₂, m₁]⟩
    rw [c₂, m₁, val32_succ s.mem base a (k + 1), val32_succ s.mem base m (k + 1)]
    exact congrArg some (decide_eq_decide.mpr (lt_top (val32_lt _ _ _ _) (val32_lt _ _ _ _)).symm)

/-- `eax` is all ones iff `[a] < [MN]`; `edx` changes too. -/
theorem ltN_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MN + 8 * c.n ≤ size) :
    WP isa (.block (c.ltN a)) s fun s' =>
      s'.gpr .eax = mask32 (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MN) c.n) ∧
      Keeps [.eax, .edx] s s' ∧ s'.mem = s.mem := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * c.n = k + 1 := ⟨2 * c.n - 1, by omega⟩
  rw [ltN_eq, hk]
  refine WP.block_append (WP.mono (ltSteps_ok hs k (by omega) (by omega)) fun s₁ ⟨c₁, k₁, m₁⟩ => ?_)
  refine wp_sbbS rfl c₁ fun s₂ u₂ _ => WP.block_nil ⟨?_, (k₁.mono (by decide)).widen u₂.keeps,
    by rw [u₂.mem, m₁]⟩
  rw [u₂.gpr, sbb_mask, wordsVal_eq_val32, wordsVal_eq_val32, hk]
  simp only [mask32, decide_eq_true_eq]

/-! ## The flag -/

/-- `[FLAG] &= edx`, through `eax`. -/
theorem andFlag_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block c.andFlag) s fun s' =>
      flagW c base s' = flagW c base s &&& s.gpr .edx ∧
      Keeps [.eax] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  simp only [Cfg.andFlag]
  refine wp_movS (readSrc_sc hs (d := c.sl FLAG) hf) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  have k₂ : Keeps [.eax] s s₂ := u₁.keeps.trans u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  refine wp_storeS (hs₂.ea (d := c.sl FLAG) (by omega)) (hs₂.write hf) fun s₃ m₃ => WP.block_nil
    ⟨?_, k₂.trans (m₃.keeps _), ?_⟩
  · rw [flagW, flagW, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, u₁.gpr, u₁.other _ (by decide)]
    simp only [ite_true]
  · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

/-- `checkRange a`: the flag `&=` the mask of `0 < [a] < [MN]`. -/
theorem checkRange_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MN + 8 * c.n ≤ size) (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block (c.checkRange a)) s fun s' =>
      flagW c base s' = flagW c base s &&&
        mask32 (0 < wordsVal s.mem base a c.n ∧ wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MN) c.n) ∧
      Keeps [.eax, .ebx, .ecx, .edx] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  simp only [Cfg.checkRange, List.append_assoc, List.singleton_append]
  refine WP.block_append (WP.mono (ltN_ok c hs hn ha hm) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  have k₂ : Keeps [.eax, .ebx, .ecx, .edx] s s₂ := (k₁.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (nonzero_ok c hs₂ hn ha) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  have k₄ : Keeps [.eax, .ebx, .ecx, .edx] s s₄ := (k₂.widen k₃).widen u₄.keeps
  have hs₄ := hs.of_keeps k₄ (by decide)
  have mem₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃, u₂.mem, m₁]
  refine WP.mono (andFlag_ok c hs₄ hf) fun s₅ ⟨e₅, k₅, O₅⟩ => ⟨?_, k₄.widen k₅, by rw [← mem₄]; exact O₅⟩
  rw [e₅, flagW, flagW, mem₄, u₄.gpr, e₃, k₃.1 _ (by decide), u₂.gpr, e₁, u₂.mem, m₁]
  simp only [ite_true]
  rw [mask32_and]
  simp only [Nat.pos_iff_ne_zero]

/-- `checkNonzero a`: the flag `&=` the mask of `[a] ≠ 0`. -/
theorem checkNonzero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block (c.checkNonzero a)) s fun s' =>
      flagW c base s' = flagW c base s &&& mask32 (wordsVal s.mem base a c.n ≠ 0) ∧
      Keeps [.eax, .ecx, .edx] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  rw [Cfg.checkNonzero]
  refine WP.block_append (WP.mono (nonzero_ok c hs hn ha) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WP.mono (andFlag_ok c (hs.of_keeps k₁ (by decide)) hf) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine ⟨by rw [e₂, e₁, flagW, flagW, m₁], (k₁.mono (by decide)).widen k₂, by rw [← m₁]; exact O₂⟩

end VG.Proof.Ecdsa.X86
