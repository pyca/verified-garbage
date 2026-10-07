import VerifiedGarbage.Proof.Weierstrass.X86.TCombJMask
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-- OR a masked constant into one coordinate word. -/
def orConstWord (y v i : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 (v / 2 ^ (32 * i)))), .alu .and .eax (.reg .ecx),
    .alu .or .eax (.mem (sc (y + 4 * i))), .store (sc (y + 4 * i)) .eax]

theorem orConstWord_ok {s : State} {base : Addr} {size y v i : Nat} (hs : Scr s base size)
    {M : BitVec 32} (hc : s.gpr .ecx = M) (hy : y + 4 * i + 4 ≤ size) :
    WP isa (.block (orConstWord y v i)) s fun t =>
      t.mem = s.mem.writeW (off base (y + 4 * i))
        ((BitVec.ofNat 32 (v / 2 ^ (32 * i)) &&& M) ||| s.mem.readW (off base (y + 4 * i)) 32) ∧
      Keeps [.eax] s t := by
  simp only [orConstWord]
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  have hs₂ := (hs.of_keeps u₁.keeps (by decide)).of_keeps u₂.keeps (by decide)
  refine wp_orS (readSrc_sc hs₂ hy) fun s₃ u₃ => ?_
  have hs₃ := hs₂.of_keeps u₃.keeps (by decide)
  refine wp_storeS (hs₃.ea (by omega)) (hs₃.write (n := 4) hy) fun t u₄ => WP.block_nil ⟨?_, ?_⟩
  · simp only [u₄.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₁.other .ecx (by decide), hc,
      u₃.mem, u₂.mem, u₁.mem, ite_true]
  · exact ((u₁.keeps.trans u₂.keeps).trans u₃.keeps).trans (u₄.keeps _)

/-- The masked constant, word by word, without changing the mask. -/
theorem orConstWords_ok {s : State} {base : Addr} {size y v : Nat} (hs : Scr s base size)
    {M : BitVec 32} (hc : s.gpr .ecx = M) : ∀ k, y + 4 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (orConstWord y v))) s fun t =>
      (∀ i < k, t.mem.readW (off base (y + 4 * i)) 32 =
        (BitVec.ofNat 32 (v / 2 ^ (32 * i)) &&& M) ||| s.mem.readW (off base (y + 4 * i)) 32) ∧
      Keeps [.eax] s t ∧ Outside base y (4 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Keeps.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (orConstWords_ok hs hc k (by omega)) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
    refine WP.mono (orConstWord_ok (hs.of_keeps k₁ (by decide)) ((k₁.1 _ (by decide)).trans hc)
      (i := k) (by omega)) fun s₂ ⟨m₂,k₂⟩ => ?_
    have O₂ : Outside base (y + 4 * k) 4 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨fun i hi => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    have read_eq {m m' : Mem} {a b n : Nat} (O : Outside base a n m m')
        (hab : b + 4 ≤ a ∨ a + n ≤ b) (hb : b + 4 ≤ 2 ^ 64) :
        m'.readW (off base b) 32 = m.readW (off base b) 32 :=
      BitVec.eq_of_toNat_eq (O.w32 hab hb)
    rcases Nat.lt_or_ge i k with h | h
    · rw [read_eq O₂ (by omega) (by omega), e₁ i h]
    · obtain rfl : i = k := by omega
      rw [m₂, Mem.readW_writeW_self32, read_eq O₁ (by omega) (by omega)]

theorem notMask_ok (s : State) {b : Bool} (hc : s.gpr .ecx = bmask b) :
    WP isa (.block [.alu .xor .ecx (.imm (-1))]) s fun t =>
      t.gpr .ecx = bmask (!b) ∧ CKeeps [.ecx] s t := by
  crun [hc]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases b <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- Restore Montgomery one in Y where the Jacobian accumulator is infinity. -/
theorem outFix_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn1 : 1 ≤ K.M.n) (hone : K.one < 2 ^ (64 * K.M.n)) (hy : K.A.y + 8 * K.M.n ≤ size)
    (hz : K.A.z + 8 * K.M.n ≤ size) (hzero : K.zero + 8 * K.M.n ≤ size)
    (hy0 : K.A.y + 8 * K.M.n ≤ K.zero ∨ K.zero + 8 * K.M.n ≤ K.A.y)
    (h0 : wordsVal s.mem base K.zero K.M.n = 0) :
    WP isa (.block K.outFix) s fun t =>
      wordsVal t.mem base K.A.y K.M.n =
        (if wordsVal s.mem base K.A.z K.M.n = 0 then K.one else wordsVal s.mem base K.A.y K.M.n) ∧
      KeepRegs [.eax, .ecx, .edx] s t ∧ Outside base K.A.y (8 * K.M.n) s.mem t.mem := by
  have hn := hs.nowrap
  unfold TCombCfg.outFix
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (nzMask_ok hs hn1 hz) fun s₁ ⟨c₁,k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁.keeps (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selWords_ok hs₁ (decide (wordsVal s.mem base K.A.z K.M.n ≠ 0)) c₁
    (o := K.A.y) (a := K.zero) (b := K.A.y) hy hzero hy (by omega) (.inl (Nat.le_refl _)))
    fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (notMask_ok s₂ (b := decide (wordsVal s.mem base K.A.z K.M.n ≠ 0)) (by rw [k₂.1 _ (by decide), c₁])) fun s₃ ⟨c₃,k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃.keeps (by decide)
  refine WP.mono (orConstWords_ok hs₃ c₃ (v := K.one) (2 * K.M.n) (by omega)) fun t ⟨e₄,k₄,O₄⟩ => ?_
  rw [k₁.2.1] at e₂
  refine ⟨?_, ((k₁.keeps.mono (by decide)).trans (k₂.mono (by decide))).trans
    ((k₃.keeps.mono (by decide)).trans (k₄.mono (by decide))), ?_⟩
  · have hor (x : BitVec 32) : x ||| (0 : BitVec 32) = x := BitVec.or_zero
    have hand (x y : BitVec 32) : (x &&& (0 : BitVec 32)) ||| y = y := by
      have hz : x &&& (0 : BitVec 32) = 0 := BitVec.and_zero
      rw [hz]; exact BitVec.zero_or
    rw [wordsVal_eq_val32]
    by_cases h : wordsVal s.mem base K.A.z K.M.n = 0
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        Bool.not_false, bmask, BitVec.and_allOnes] at e₂ e₄ ⊢
      rw [h0, wordsVal_eq_val32] at e₂
      have hw0 := (val32_eq_zero_iff _ _ _ _).mp e₂
      refine val32_of_shifts _ _ _ _ _ (by rw [show 32 * (2 * K.M.n) = 64 * K.M.n by omega]; exact hone) fun i hi => ?_
      have hzword : s₃.mem.readW (off base (K.A.y + 4 * i)) 32 = 0 :=
        BitVec.eq_of_toNat_eq (by rw [k₃.2.1]; exact hw0 i hi)
      simp only [w32, e₄ i hi, hzword, hor, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    · simp only [h, ne_eq, not_false_eq_true, decide_true, ↓reduceIte,
        Bool.not_true, bmask, Bool.false_eq_true, hand] at e₂ e₄ ⊢
      rw [← e₂, wordsVal_eq_val32]
      exact val32_congr fun i hi => by simp only [w32, e₄ i hi, k₃.2.1]
  · intro x hx
    rw [show 4 * (2 * K.M.n) = 8 * K.M.n by omega] at O₄
    rw [O₄ x hx, k₃.2.1, O₂ x hx, k₁.2.1]

end VG.Proof.Weierstrass.X86
