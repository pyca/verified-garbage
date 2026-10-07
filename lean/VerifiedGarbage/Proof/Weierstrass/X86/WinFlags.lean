import VerifiedGarbage.Proof.Weierstrass.X86.WinQuad
import VerifiedGarbage.Proof.Weierstrass.Words32

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

abbrev winMask32 (p : Prop) [Decidable p] : BitVec 32 := if p then BitVec.allOnes 32 else 0

/-- The `or`s of `nonzero`. -/
theorem winOrs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat} :
    ∀ k, a + 4 * (k + 1) ≤ size →
    WP isa (.block ((List.range k).map fun j => .alu .or .edx (.mem (sc (a + 4 * (j + 1)))))) s fun s' =>
      (s'.gpr .edx = 0 ↔ s.gpr .edx = 0 ∧ ∀ j < k, w32 s.mem base (a + 4 * (j + 1)) = 0) ∧
      Keeps [.edx] s s' ∧ s'.mem = s.mem
  | 0, _ => WP.block_nil ⟨⟨fun h => ⟨h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩, fun h => h.1⟩,
      Keeps.refl _ _, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (winOrs_ok hs k (by omega)) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
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


/-- Compare the accumulated OR with zero. -/
theorem zeroFinish_ok (s : State) :
    WP isa (.block [.alu .cmp .edx (.imm 1), .alu .sbb .edx (.reg .edx)]) s fun t =>
      t.gpr .edx = winMask32 (s.gpr .edx = 0) ∧ CKeeps [.edx] s t := by
  crun []
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h1 : (1 : BitVec 32).toNat = 1 := rfl
    have hz : decide ((s.gpr .edx).toNat < 1) = decide (s.gpr .edx = 0) := by
      apply decide_eq_decide.mpr
      rw [Nat.lt_one_iff]
      exact ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩
    rw [BitVec.sub_self, h1, hz]
    unfold winMask32
    split <;> rename_i h <;> simp only [h, decide_true, decide_false] <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem winZeroMask_ok (K : WinCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 0 < K.M.n) (ha : K.E.z + 8 * K.M.n ≤ size) :
    WP isa (.block (WinCfg.zeroMask K)) s fun t =>
      t.gpr .edx = winMask32 (wordsVal s.mem base K.E.z K.M.n = 0) ∧
      Keeps [.edx] s t ∧ t.mem = s.mem := by
  simp only [WinCfg.zeroMask, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs (d := K.E.z) (by omega)) fun s₁ u₁ _ => ?_
  refine WP.block_append (WP.mono (winOrs_ok (hs.of_keeps u₁.keeps (by decide)) (2 * K.M.n - 1) (by omega))
    fun s₂ ⟨e₂,k₂,m₂⟩ => ?_)
  rw [u₁.gpr, u₁.mem] at e₂
  have hz : s₂.gpr .edx = 0 ↔ wordsVal s.mem base K.E.z K.M.n = 0 := by
    rw [e₂, wordsVal_eq_val32, val32_eq_zero_iff]
    have hw : (s.mem.readW (off base K.E.z) 32 = 0) ↔ w32 s.mem base K.E.z = 0 :=
      ⟨fun h => by simp [w32, h], fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hw]
    constructor
    · intro ⟨h₀,h⟩ j hj
      cases j with
      | zero => simpa using h₀
      | succ j => exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 (by omega), fun j hj => h (j + 1) (by omega)⟩
  refine WP.mono (zeroFinish_ok s₂) fun t ⟨e,k⟩ => ?_
  exact ⟨by simpa only [winMask32, hz] using e, (u₁.keeps.trans k₂).trans k.keeps,
    k.2.1.trans (m₂.trans u₁.mem)⟩

theorem selectMask32 (a b : BitVec 32) (p : Prop) [Decidable p] :
    a ^^^ ((b ^^^ a) &&& winMask32 p) = if p then b else a := by
  by_cases h : p
  · simp only [winMask32, h, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [winMask32, h]

/-- One word of the corrected projective Y coordinate. -/
theorem ySelWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : WinCfg)
    (p : Prop) [Decidable p] (hd : s.gpr .edx = winMask32 p) {w : Nat} (ho : K.R.y + 4 * w + 4 ≤ size) :
    WP isa (.block (WinCfg.ySelWord K w)) s fun t =>
      t.mem = s.mem.writeW (off base (K.R.y + 4 * w))
        (if p then BitVec.ofNat 32 (K.one / 2 ^ (32 * w)) else s.mem.readW (off base (K.R.y + 4 * w)) 32) ∧
      Keeps [.eax, .ebx] s t := by
  simp only [WinCfg.ySelWord]
  refine wp_movS (readSrc_sc hs (d := K.R.y + 4 * w) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₃ u₃ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => ?_
  have keep : Keeps [.eax, .ebx] s s₅ :=
    ((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps
  have hs₅ := hs.of_keeps keep (by decide)
  refine wp_storeS (hs₅.ea (by omega)) (hs₅.write (n := 4) ho) fun t u₆ => WP.block_nil ⟨?_,keep.trans (u₆.keeps _)⟩
  simp only [u₆.mem, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr,
    u₄.other .eax (by decide), u₃.other .eax (by decide), u₂.other .eax (by decide),
    u₃.other .edx (by decide), u₂.other .edx (by decide), u₁.other .edx (by decide), hd,
    u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, reduceCtorEq, ite_false, ite_true, selectMask32]

/-- Correct the first k 32-bit words of Y. -/
theorem ySelWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : WinCfg)
    (p : Prop) [Decidable p] (hd : s.gpr .edx = winMask32 p) :
    ∀ k, K.R.y + 4 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (WinCfg.ySelWord K))) s fun t =>
      (∀ j < k, w32 t.mem base (K.R.y + 4 * j) =
        if p then (K.one / 2 ^ (32 * j)) % 2 ^ 32 else w32 s.mem base (K.R.y + 4 * j)) ∧
      Keeps [.eax, .ebx] s t ∧ Outside base K.R.y (4 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Keeps.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ySelWords_ok hs K p hd k (by omega)) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
    refine WP.mono (ySelWord_ok (hs.of_keeps k₁ (by decide)) K p ((k₁.1 _ (by decide)).trans hd)
      (w := k) (by omega)) fun s₂ ⟨m₂,k₂⟩ => ?_
    have O₂ : Outside base (K.R.y + 4 * k) 4 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.w32 (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      unfold w32
      rw [m₂, Mem.readW_writeW_self32]
      split
      · rfl
      · exact O₁.w32 (by omega) (by omega)

/-- Restore canonical infinity after the Jacobian doublings. -/
theorem ySel_ok {K : WinCfg} {base : Addr} {size : Nat} (hL : WinLay K size)
    {s : State} (hs : Scr s base size) (h1 : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block (WinCfg.ySel K)) s fun t =>
      wordsVal t.mem base K.R.y K.M.n = (if wordsVal s.mem base K.E.z K.M.n = 0 then K.one
        else wordsVal s.mem base K.R.y K.M.n) ∧
      Keeps [.eax, .edx, .ebx] s t ∧ Unch base [(K.R.y, 8 * K.M.n)] s.mem t.mem := by
  have hy : K.R.y ∈ winSlots K := by win_mem
  have hz : K.E.z ∈ winSlots K := by win_mem
  rw [WinCfg.ySel, WP.block_append_iff]
  refine WP.mono (winZeroMask_ok K hs hL.n0 (hL.lay.le _ hz)) fun s₁ ⟨m₁,k₁,mem₁⟩ => ?_
  refine WP.mono (ySelWords_ok (hs.of_keeps k₁ (by decide)) K _ m₁ (2 * K.M.n)
    (by have := hL.lay.le _ hy; omega)) fun t ⟨e,k,O⟩ => ⟨?_,?_,?_⟩
  · by_cases h : wordsVal s.mem base K.E.z K.M.n = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), wordsVal_eq_val32]
      exact val32_of_shifts _ _ _ _ _ (by rw [show 32 * (2 * K.M.n) = 64 * K.M.n by omega]; exact h1) fun j hj => by
        simp only [e j hj, h, ↓reduceIte, Nat.shiftRight_eq_div_pow]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), wordsVal_eq_val32, wordsVal_eq_val32]
      exact val32_congr (fun j hj => by simp only [e j hj, h, ↓reduceIte, mem₁])

  · exact (k₁.mono (by decide)).trans (k.mono (by decide))
  · rw [← mem₁]
    simpa only [show 4 * (2 * K.M.n) = 8 * K.M.n by omega] using O.unch

end VG.Proof.Weierstrass.X86
