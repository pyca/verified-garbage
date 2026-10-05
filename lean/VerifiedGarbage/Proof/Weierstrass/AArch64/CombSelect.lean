import VerifiedGarbage.Proof.Weierstrass.AArch64.CombDigit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Weierstrass.Unch

/-!
# The comb on AArch64: the constant-time selection

With `maskReg m` all ones exactly for `m = a` (`a ≤ 8`), `selectWord` builds
every candidate word from immediates, ANDs it with its mask and ORs it into
`x4`, so that word `w` of the candidate for `a` survives (`selectWord_ok`);
`select` writes the entry's `X`, `Y` and `Z` (`select_ok`): `(0 : R : 0)`
for `a = 0`, else `(x : y : R)` of the table's entry `a - 1`.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open CombCfg

/-- The masks of the magnitude `a`. -/
def MasksOf (s : State) (a : Nat) : Prop := ∀ m ≤ 8, s.gpr (maskReg m) = bmask (decide (a = m))

theorem maskRegs_not : ∀ m ≤ 8, maskReg m ≠ .x2 ∧ maskReg m ≠ .x4 ∧ maskReg m ≠ .x9 ∧
    maskReg m ≠ .x0 ∧ maskReg m ≠ .x19 := by decide

theorem MasksOf.keep {s s' : State} {a : Nat} (h : MasksOf s a) (hk : Keeps [.x2, .x4, .x9] s s') :
    MasksOf s' a := fun m hm => by
  have := maskRegs_not m hm
  rw [hk.gpr _ (by simp [this.1, this.2.1, this.2.2.1])]
  exact h m hm

/-- `x4 |= v & mask m`. -/
theorem selectCand_ok (s : State) (v : BitVec 64) {m : Nat} (hm : m ≤ 8) :
    WP isa (.block (selectCand v m)) s fun t =>
      t.gpr .x4 = s.gpr .x4 ||| (v &&& s.gpr (maskReg m)) ∧ Keeps [.x2, .x4, .x9] s t := by
  have hr := maskRegs_not m hm
  rw [selectCand, WP.block_append_iff]
  refine WP.mono (const64_ok s .x9 v) fun a ⟨a9, ka⟩ => ?_
  have am : a.gpr (maskReg m) = s.gpr (maskReg m) := ka.gpr _ (by simpa using hr.2.2.1)
  have a4 : a.gpr .x4 = s.gpr .x4 := ka.gpr _ (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, a9, am, a4,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr' => ?_, ka.mem, ka.rd, ka.wr, ka.sp⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  simp only [RegUpd.gpr_write, hr'.1, hr'.2.1, ite_false]
  exact ka.gpr _ (by simpa using hr'.2.2)

/-- The value of magnitude `a`: `z` for `0`, else entry `a - 1` of `vs`. -/
def selVal (z : Nat) (vs : List Nat) (a : Nat) : Nat := if a = 0 then z else vs.getD (a - 1) 0

theorem bmask_and (v : BitVec 64) (b : Bool) : v &&& bmask b = if b then v else 0 := by
  cases b
  · simp [bmask]
  · exact BitVec.and_allOnes

/-- The candidates `1 … i` ORed into `x4`. -/
theorem selectCands_ok {vs : List Nat} {w a : Nat} (ha : a ≤ 8) (X₀ : BitVec 64) :
    ∀ i ≤ 8, ∀ s : State, s.gpr .x4 = X₀ → MasksOf s a →
      WP isa (.block ((List.range i).flatMap fun i => selectCand (wordOf (vs.getD i 0) w) (i + 1))) s
        fun t => t.gpr .x4 = X₀ ||| (if 1 ≤ a ∧ a ≤ i then wordOf (vs.getD (a - 1) 0) w else 0) ∧
          Keeps [.x2, .x4, .x9] s t := by
  intro i hi s h4 hM
  refine WP.mono (wp_range_flatMap (M := isa) (N := i)
    (fun k t => t.gpr .x4 = X₀ ||| (if 1 ≤ a ∧ a ≤ k then wordOf (vs.getD (a - 1) 0) w else 0) ∧
      Keeps [.x2, .x4, .x9] s t) (fun k t hk ⟨t4, kt⟩ => ?_) i (Nat.le_refl _) s
    ⟨by rw [h4]; simp [show ¬(1 ≤ a ∧ a = 0) by omega], ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩)
    fun t h => h
  refine WP.mono (selectCand_ok t _ (m := k + 1) (by omega)) fun u ⟨u4, ku⟩ => ⟨?_, kt.trans ku⟩
  rw [u4, t4, (hM.keep kt) (k + 1) (by omega), bmask_and, BitVec.or_assoc]
  congr 1
  by_cases h1 : a = k + 1
  · subst h1
    simp [show ¬(k + 1 ≤ k) by omega]
  · by_cases h2 : 1 ≤ a ∧ a ≤ k
    · simp [h1, h2, show 1 ≤ a ∧ a ≤ k + 1 by omega]
    · simp [h1, h2, show ¬(1 ≤ a ∧ a ≤ k + 1) by omega]

theorem wordOf_zero (w : Nat) : wordOf 0 w = 0 := by simp [wordOf]

theorem MasksOf.keepRegs {s s' : State} {a : Nat} (h : MasksOf s a)
    (hk : KeepRegs [.x2, .x4, .x9] s s') : MasksOf s' a := fun m hm => by
  have := maskRegs_not m hm
  rw [hk.gpr _ (by simp [this.1, this.2.1, this.2.2.1])]
  exact h m hm

theorem selectWord_eq (z : Nat) (vs : List Nat) (o w : Nat) : selectWord z vs o w =
    ([.movz .x .x4 0 0] : List Instr) ++ ((if z = 0 then [] else selectCand (wordOf z w) 0) ++
      ((List.range 8).flatMap (fun i => selectCand (wordOf (vs.getD i 0) w) (i + 1)) ++
        ([st .x4 (o + 8 * w)] : List Instr))) := by
  simp only [selectWord, List.append_assoc]

/-- Word `w` of the magnitude's value, into `[o + 8 w]`. -/
theorem selectWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a ≤ 8) (hM : MasksOf s a) (z : Nat) (vs : List Nat) {o w : Nat} (ho : o + 8 * w + 8 ≤ size)
    (ho8 : o % 8 = 0) :
    WP isa (.block (selectWord z vs o w)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * w)) (wordOf (selVal z vs a) w) ∧
      KeepRegs [.x2, .x4, .x9] s t := by
  rw [selectWord_eq, WP.block_append_iff]
  refine WP.mono (movz0_ok s .x4) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hM₁ := hM.keep (k₁.mono (by decide))
  rw [WP.block_append_iff]
  have hopt : WP isa (.block (if z = 0 then [] else selectCand (wordOf z w) 0)) s₁ fun t =>
      t.gpr .x4 = (if a = 0 then wordOf z w else 0) ∧ Keeps [.x2, .x4, .x9] s₁ t := by
    split
    · rename_i hz
      refine WP.block_nil ⟨by rw [z₁, hz, wordOf_zero]; split <;> rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
    · refine WP.mono (selectCand_ok s₁ _ (m := 0) (by decide)) fun t ⟨t4, kt⟩ => ⟨?_, kt⟩
      rw [t4, z₁, hM₁ 0 (by decide), bmask_and]
      by_cases h : a = 0 <;> simp [h]
  refine WP.mono hopt fun s₂ ⟨x₂, k₂⟩ => ?_
  have hM₂ := hM₁.keep k₂
  rw [WP.block_append_iff]
  refine WP.mono (selectCands_ok (vs := vs) (w := w) ha _ 8 (Nat.le_refl _) s₂ x₂ hM₂)
    fun s₃ ⟨x₃, k₃⟩ => ?_
  have hs₃ := (hs.of_keeps k₁ (by decide)).of_keeps (k₂.trans k₃) (by decide)
  refine WP.mono (st_out hs₃ (o := o + 8 * w) ho (by omega) .x4) fun t ⟨m, kt, _⟩ => ⟨?_, ?_⟩
  · rw [m, x₃, k₃.mem, k₂.mem, k₁.mem]
    congr 1
    unfold selVal
    by_cases h : a = 0
    · subst h; simp
    · simp [h, show 1 ≤ a ∧ a ≤ 8 by omega]
  · exact (((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs (k₂.trans k₃)))).trans
      (kt.mono (by decide))

/-- The `n` words of the magnitude's value, into `[o]`. -/
theorem selectWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a ≤ 8) (hM : MasksOf s a) (z : Nat) (vs : List Nat) {o : Nat} (ho8 : o % 8 = 0) :
    ∀ k, o + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (selectWord z vs o))) s fun t =>
      (∀ w < k, word t.mem base (o + 8 * w) = wordOf (selVal z vs a) w) ∧
      KeepRegs [.x2, .x4, .x9] s t ∧ Outside base o (8 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selectWords_ok hs ha hM z vs ho8 k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (selectWord_ok hs₁ ha (hM.keepRegs k₁) z vs (w := k) (by omega) ho8)
      fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, word_writeW_self]

/-- `x4 & ~0 = x4` and `x4 & ~(all ones) = 0`. -/
theorem and_not_bmask (v : BitVec 64) (b : Bool) : v &&& ~~~(bmask b) = if b then 0 else v := by
  cases b
  · show v &&& ~~~(0#64) = v
    rw [BitVec.not_zero, BitVec.and_allOnes]
  · simp [bmask]

theorem rotateRight_zero' (x : BitVec 64) : x.rotateRight 0 = x := by
  ext i hi
  simp [BitVec.getElem_rotateRight, hi]

/-- Word `w` of `Z`, into `[o + 8 w]`. -/
theorem selectZ_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : CombCfg)
    {a : Nat} (hM : MasksOf s a) {o w : Nat} (ho : o + 8 * w + 8 ≤ size) (ho8 : o % 8 = 0) :
    WP isa (.block ((selectZ K) o w)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * w)) (wordOf (if a = 0 then 0 else K.one) w) ∧
      KeepRegs [.x2, .x4, .x9] s t := by
  rw [selectZ, WP.block_append_iff]
  refine WP.mono (const64_ok s .x9 _) fun s₁ ⟨v₁, k₁⟩ => ?_
  have hm₁ : s₁.gpr (maskReg 0) = bmask (decide (a = 0)) := by
    rw [k₁.gpr _ (by decide)]; exact hM 0 (by decide)
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [show ([.bicRor .x .x4 .x9 (maskReg 0) 0, st .x4 (o + 8 * w)] : List Instr) =
    [.bicRor .x .x4 .x9 (maskReg 0) 0] ++ [st .x4 (o + 8 * w)] from rfl, WP.block_append_iff]
  have hb : WP isa (.block [.bicRor .x .x4 .x9 (maskReg 0) 0]) s₁ fun t =>
      t.gpr .x4 = wordOf (if a = 0 then 0 else K.one) w ∧ Keeps [.x4] s₁ t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
      show (0 : Nat) < 64 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq,
      rotateRight_zero', v₁, hm₁, and_not_bmask, Option.some.injEq, exists_eq_left']
    refine ⟨by by_cases h : a = 0 <;> simp [h, wordOf_zero], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)
  refine WP.mono hb fun s₂ ⟨x₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (st_out hs₂ (o := o + 8 * w) ho (by omega) .x4) fun t ⟨m, kt, _⟩ => ⟨?_, ?_⟩
  · rw [m, x₂, k₂.mem, k₁.mem]
  · exact (((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      (kt.mono (by decide))

/-- The `n` words of `Z`, into `[o]`. -/
theorem selectZs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : CombCfg)
    {a : Nat} (hM : MasksOf s a) {o : Nat} (ho8 : o % 8 = 0) :
    ∀ k, o + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap ((selectZ K) o))) s fun t =>
      (∀ w < k, word t.mem base (o + 8 * w) = wordOf (if a = 0 then 0 else K.one) w) ∧
      KeepRegs [.x2, .x4, .x9] s t ∧ Outside base o (8 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selectZs_ok hs K hM ho8 k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (selectZ_ok hs₁ K (hM.keepRegs k₁) (w := k) (by omega) ho8)
      fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, word_writeW_self]

theorem selVal_lt {z : Nat} {vs : List Nat} {B : Nat} (hz : z < B) (hv : ∀ i, vs.getD i 0 < B)
    (a : Nat) : selVal z vs a < B := by
  unfold selVal; split
  · exact hz
  · exact hv _

theorem select_eq (K : CombCfg) (t : List (Nat × Nat)) : (select K) t =
    (List.range K.M.n).flatMap (selectWord 0 (t.map (·.1)) K.E.x) ++
    ((List.range K.M.n).flatMap (selectWord K.one (t.map (·.2)) K.E.y) ++
    (List.range K.M.n).flatMap ((selectZ K) K.E.z)) := by
  simp only [select, List.append_assoc]

/-- The entry of the magnitude `a` from the table `t`, into `E`: `(0 : R : 0)`
for `a = 0`, else `(x : y : R)` of entry `a - 1`. -/
theorem select_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : CombCfg)
    {a : Nat} (ha : a ≤ 8) (hM : MasksOf s a) (t : List (Nat × Nat))
    (hE : ∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ size ∧ d % 8 = 0)
    (hap : (K.E.x + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.x + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.y + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.y))
    (hv : ∀ i, (t.map (·.1)).getD i 0 < 2 ^ (64 * K.M.n) ∧ (t.map (·.2)).getD i 0 < 2 ^ (64 * K.M.n))
    (h1 : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block ((select K) t)) s fun s' =>
      wordsVal s'.mem base K.E.x K.M.n = selVal 0 (t.map (·.1)) a ∧
      wordsVal s'.mem base K.E.y K.M.n = selVal K.one (t.map (·.2)) a ∧
      wordsVal s'.mem base K.E.z K.M.n = (if a = 0 then 0 else K.one) ∧
      KeepRegs [.x2, .x4, .x9] s s' ∧ MasksOf s' a ∧
      Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem s'.mem := by
  have hn := hs.nowrap
  have hx := hE K.E.x (by simp)
  have hy := hE K.E.y (by simp)
  have hz := hE K.E.z (by simp)
  obtain ⟨xy, xz, yz⟩ := hap
  have hP : 0 < 2 ^ (64 * K.M.n) := Nat.two_pow_pos _
  rw [select_eq, WP.block_append_iff]
  have W₁ := selectWords_ok hs ha hM 0 (t.map (·.1)) hx.2 K.M.n hx.1
  refine WP.mono W₁ fun s₁ h₁ => ?_
  obtain ⟨e₁, k₁, O₁⟩ := h₁
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  have W₂ := selectWords_ok hs₁ ha (hM.keepRegs k₁) K.one (t.map (·.2)) hy.2 K.M.n hy.1
  refine WP.mono W₂ fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have W₃ := selectZs_ok hs₂ K ((hM.keepRegs k₁).keepRegs k₂) hz.2 K.M.n hz.1
  refine WP.mono W₃ fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have vx : wordsVal s₁.mem base K.E.x K.M.n = selVal 0 (t.map (·.1)) a :=
    wordsVal_of_shifts _ _ _ _ _ (selVal_lt hP (fun i => (hv i).1) a) e₁
  have vy : wordsVal s₂.mem base K.E.y K.M.n = selVal K.one (t.map (·.2)) a :=
    wordsVal_of_shifts _ _ _ _ _ (selVal_lt h1 (fun i => (hv i).2) a) e₂
  have vz : wordsVal s₃.mem base K.E.z K.M.n = (if a = 0 then 0 else K.one) :=
    wordsVal_of_shifts _ _ _ _ _ (by split <;> omega) e₃
  refine ⟨?_, ?_, vz, (k₁.trans k₂).trans k₃, ((hM.keepRegs k₁).keepRegs k₂).keepRegs k₃,
    (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono (by simp)⟩
  · rw [O₃.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega), vx]
  · rw [O₃.wordsVal (by omega) (by omega), vy]

end VG.Proof.Weierstrass.AArch64
