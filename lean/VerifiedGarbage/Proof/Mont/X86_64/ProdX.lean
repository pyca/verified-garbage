import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd

/-!
# Montgomery arithmetic on x86-64: P-256's products with BMI2 and ADX

`mulRX M k o a b` and `sqrRX M k o a` (`Impl/Mont/X86_64.lean`): X25519's
product `a b` (`mul4_ok`) or square `a²` (`sqr4_ok`) into `r8–r15`, then
`redRX`: the low half `L` of the product `t = L + 2²⁵⁶ H` reduced in a window
of four words rotating through `r8–r11`, by four rounds of `redRoundX`, each of
which makes the window's value `(W + t_i m) / 2⁶⁴` for its low word `t_i`
(`redRoundX_ok`: `t_i m' = t_i 2ᵏ + 2¹²⁸ t_i (2⁶⁴ − 2ᵏ + 1)` by two `mulx`,
added in one carry chain, which cannot carry out as `m < 2²⁵⁶`, `sqrBound`).
They leave `(L + U m) / 2²⁵⁶ ≤ m`, to which the high half `H < m` is added
(`addHigh_ok`), the carry into `r8`: `(t + U m) / 2²⁵⁶ < 2m`, which `csub`
reduces below `m` (`redRX_ok`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Impl.X25519.X86_64 (sqrA sqrB sqrC sqrD rowX0)
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono val4 sqr4_ok mul4_ok rowR' rowX_eq se0 add_carry adc_carry
  mulx_arith)

/-- `m < 2²⁵⁶` for `m + 1 = 2⁶⁴ (2ᵏ + 2¹²⁸ (2⁶⁴ − 2ᵏ + 1))`. -/
theorem sqrBound {k m : Nat} (hk : 0 < k ∧ k < 64)
    (hm : 2 ^ 64 * (2 ^ k + 2 ^ 128 * (2 ^ 64 - 2 ^ k + 1)) = m + 1) : m < 2 ^ 256 := by
  have h1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk.1
  have h2 : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  generalize 2 ^ k = K at hm h1 h2
  omega_arith

/-- A round of the reduction (`redRoundX`): the window `t, w₁, w₂, w₃` of value
`W` becomes `w₁, w₂, w₃, t` of value `(W + t m) / 2⁶⁴`, for any `W`, as
`m < 2²⁵⁶`. -/
theorem redRoundX_ok (s : State) {t w1 w2 w3 : Reg} {k m : Nat} (hk : 0 < k ∧ k < 64)
    (hm : 2 ^ 64 * (2 ^ k + 2 ^ 128 * (2 ^ 64 - 2 ^ k + 1)) = m + 1) (hf : Fresh [t, w1, w2, w3]) :
    WP isa (.block (redRoundX k t w1 w2 w3)) s fun s' =>
      2 ^ 64 * regsVal s' [w1, w2, w3, t] = regsVal s [t, w1, w2, w3] + (s.gpr t).toNat * m ∧
        Keeps [.rax, .rcx, .rdx, .rbp, t, w1, w2, w3] s s' := by
  obtain ⟨ht, ta, tc, -, tb, -⟩ := hf.head
  obtain ⟨h1, a1, c1, d1, b1, -⟩ := hf.tail.head
  obtain ⟨h2, a2, c2, d2, b2, -⟩ := hf.tail.tail.head
  obtain ⟨-, a3, c3, d3, b3, -⟩ := hf.tail.tail.tail.head
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ht h1 h2
  obtain ⟨t1, t2, t3⟩ := ht
  obtain ⟨n12, n13⟩ := h1
  have hm256 := sqrBound hk hm
  apply WP.of_runBlock
  simp only [redRoundX, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execMulx, readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    RegUpd.cf_setReg, ↓reduceIte, reduceCtorEq, a1, c1, d1, b1, a2, c2, d2, b2, a3, c3, d3, b3, t1, t2,
    t3, n12, n13, h2, Ne.symm ta, Ne.symm tc, Ne.symm tb, Ne.symm c1, Ne.symm b1, Ne.symm c2, Ne.symm t1,
    Ne.symm t2, Ne.symm t3, Ne.symm n12, Ne.symm n13, Ne.symm h2,
    Option.some.injEq, exists_eq_left', se0, regsVal]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have hK : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk.2
    have hK1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk.1
    have hA : (BitVec.ofNat 64 (2 ^ k)).toNat = 2 ^ k := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hK
    have hC : (BitVec.ofNat 64 (2 ^ 64 - 2 ^ k + 1)).toNat = 2 ^ 64 - 2 ^ k + 1 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
    have p1 := mulx_arith (s.gpr t) (BitVec.ofNat 64 (2 ^ k))
    have p2 := mulx_arith (s.gpr t) (BitVec.ofNat 64 (2 ^ 64 - 2 ^ k + 1))
    rw [hA] at p1 ⊢
    rw [hC] at p2 ⊢
    generalize BitVec.ofNat 64 ((s.gpr t).toNat * 2 ^ k) = l₁ at p1 ⊢
    generalize BitVec.ofNat 64 ((s.gpr t).toNat * 2 ^ k / 2 ^ 64) = h₁ at p1 ⊢
    generalize BitVec.ofNat 64 ((s.gpr t).toNat * (2 ^ 64 - 2 ^ k + 1)) = l₂ at p2 ⊢
    generalize BitVec.ofNat 64 ((s.gpr t).toNat * (2 ^ 64 - 2 ^ k + 1) / 2 ^ 64) = h₂ at p2 ⊢
    have e1 := add_carry (s.gpr w1) l₁
    generalize decide (2 ^ 64 ≤ (s.gpr w1).toNat + l₁.toNat) = c₁ at e1 ⊢
    have e2 := adc_carry (s.gpr w2) h₁ c₁
    generalize decide (2 ^ 64 ≤ (s.gpr w2).toNat + h₁.toNat + c₁.toNat) = c₂ at e2 ⊢
    have e3 := adc_carry (s.gpr w3) l₂ c₂
    generalize decide (2 ^ 64 ≤ (s.gpr w3).toNat + l₂.toNat + c₂.toNat) = c₃ at e3 ⊢
    have e4 := adc_carry h₂ 0 c₃
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz] at e4
    generalize decide (2 ^ 64 ≤ h₂.toNat + 0 + c₃.toNat) = c₄ at e4
    -- `t m + t = 2⁶⁴ (t 2ᵏ) + 2¹⁹² (t (2⁶⁴ − 2ᵏ + 1))`, and `W + t m < 2³²⁰`.
    have hx := (s.gpr t).isLt
    generalize (s.gpr t).toNat = x at p1 p2 hx ⊢
    generalize 2 ^ k = K at hm hK hK1 p1 p2
    generalize 2 ^ 64 - K + 1 = D at hm p2
    have key : x * m + x = 2 ^ 64 * (x * K) + 2 ^ 192 * (x * D) := by
      rw [← Nat.mul_add_one, ← hm, Nat.mul_left_comm, Nat.mul_add, Nat.mul_left_comm x (2 ^ 128),
        Nat.mul_add]
      omega_arith
    have hxm := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt hx)
    have := (s.gpr w1).isLt; have := (s.gpr w2).isLt; have := (s.gpr w3).isLt
    have := l₁.isLt; have := h₁.isLt; have := l₂.isLt; have := h₂.isLt
    have := Bool.toNat_le c₁; have := Bool.toNat_le c₂; have := Bool.toNat_le c₃; have := Bool.toNat_le c₄
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ra, rc, rd, rb, rt, r1, r2, r3⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ra, rc, rd, rb, rt, r1, r2, r3, ite_false]

/-- The high half added to the reduced low half: `r12–r15` and the carry in
`r8` are `r12–r15 + r8–r11`. -/
theorem addHigh_ok (s : State) :
    WP isa (.block [.alu .add .r12 (.reg .r8), .alu .adc .r13 (.reg .r9), .alu .adc .r14 (.reg .r10),
      .alu .adc .r15 (.reg .r11), .mov32 .r8 (.imm 0), .alu .adc .r8 (.imm 0)]) s fun s' =>
      regsVal s' sqLow + 2 ^ 256 * (s'.gpr .r8).toNat = regsVal s sqLow + regsVal s [.r8, .r9, .r10, .r11] ∧
        Keeps [.r8, .r12, .r13, .r14, .r15] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.setReg32,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    RegUpd.cf_setReg, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left', se0, regsVal, sqLow]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e1 := add_carry (s.gpr .r12) (s.gpr .r8)
    generalize decide (2 ^ 64 ≤ (s.gpr .r12).toNat + (s.gpr .r8).toNat) = c₁ at e1 ⊢
    have e2 := adc_carry (s.gpr .r13) (s.gpr .r9) c₁
    generalize decide (2 ^ 64 ≤ (s.gpr .r13).toNat + (s.gpr .r9).toNat + c₁.toNat) = c₂ at e2 ⊢
    have e3 := adc_carry (s.gpr .r14) (s.gpr .r10) c₂
    generalize decide (2 ^ 64 ≤ (s.gpr .r14).toNat + (s.gpr .r10).toNat + c₂.toNat) = c₃ at e3 ⊢
    have e4 := adc_carry (s.gpr .r15) (s.gpr .r11) c₃
    generalize decide (2 ^ 64 ≤ (s.gpr .r15).toNat + (s.gpr .r11).toNat + c₃.toNat) = c₄ at e4 ⊢
    have e5 := adc_carry (BitVec.setWidth 64 (0 : BitVec 32)) 0 c₄
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have hz' : (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 := rfl
    rw [hz, hz'] at e5
    have := (BitVec.ofNat 64 0).isLt
    have := Bool.toNat_le c₁; have := Bool.toNat_le c₂; have := Bool.toNat_le c₃
    have := Bool.toNat_le c₄
    generalize decide (2 ^ 64 ≤ 0 + 0 + c₄.toNat) = c₅ at e5
    have := Bool.toNat_le c₅
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r8, r12, r13, r14, r15⟩ := hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, r8, r12, r13, r14, r15, ite_false]

theorem redRX_eq (M : Mod) (k o : Nat) : redRX M k o =
    redRoundX k .r8 .r9 .r10 .r11 ++ (redRoundX k .r9 .r10 .r11 .r8 ++ (redRoundX k .r10 .r11 .r8 .r9 ++
      (redRoundX k .r11 .r8 .r9 .r10 ++
      (([.alu .add .r12 (.reg .r8), .alu .adc .r13 (.reg .r9), .alu .adc .r14 (.reg .r10),
        .alu .adc .r15 (.reg .r11), .mov32 .r8 (.imm 0), .alu .adc .r8 (.imm 0)] : List Instr) ++
      (csub M sqLow .r8 ++ stores sqLow o))))) := by
  simp only [redRX, List.append_assoc]

theorem sqrRX_eq (M : Mod) (k o a : Nat) :
    sqrRX M k o a = (sqrA a ++ (sqrB a ++ (sqrC a ++ sqrD a))) ++ redRX M k o := by
  simp only [sqrRX, List.append_assoc]

theorem mulRX_eq (M : Mod) (k o a b : Nat) : mulRX M k o a b =
    (rowX0 b a ++ (rowR' b a 1 .r9 .r10 .r11 .r12 .r13 ++
      (rowR' b a 2 .r10 .r11 .r12 .r13 .r14 ++ rowR' b a 3 .r11 .r12 .r13 .r14 .r15))) ++ redRX M k o := by
  simp only [mulRX, rowX_eq, List.append_assoc]; rfl

/-- The registers `redRX`, `mulRX` and `sqrRX` change. -/
abbrev sqrClob : List Reg :=
  [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- X25519's four words are `wordsVal`'s. -/
theorem fe_wordsVal (m : Mem) (base : Addr) (a : Nat) :
    VG.Proof.X25519.X86_64.fe m base a = wordsVal m base a 4 := by
  simp only [VG.Proof.X25519.X86_64.fe, VG.Proof.X25519.X86_64.word,
    VG.Proof.X25519.X86_64.off, val4, wordsVal, word, off, Nat.add_assoc, Nat.reduceAdd]
  omega_arith

/-- `redRX`: `[o] = t R⁻¹ mod m` for the product `t < 2²⁵⁶ m` in `r8–r15` and
`m' = 2ᵏ + 2¹²⁸ (2⁶⁴ − 2ᵏ + 1)` (P-256's `p`). -/
theorem redRX_ok {s₁ : State} {base : Addr} {size : Nat} (hs₁ : Scr s₁ base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s₁.mem base) (hn : M.n = 4) {ws : List MWord} (hr : M.red = .friendly ws)
    {k : Nat} (hk : shiftK? ws = some k) {o : Nat} (ho : o + 32 ≤ size) {T : Nat}
    (hV₁ : (s₁.gpr .r8).toNat + 2 ^ 64 * regsVal s₁ [.r9, .r10, .r11, .r12, .r13, .r14, .r15] = T)
    (hTm : T < 2 ^ 256 * m) :
    WP isa (.block (redRX M k o)) s₁ fun s' =>
      KeepRegs sqrClob s₁ s' ∧
      (∀ x, (ofs base x < o ∨ o + 32 ≤ ofs base x) →
        (ofs base x < M.tmp ∨ M.tmp + 32 ≤ ofs base x) → s'.mem x = s₁.mem x) ∧
      wordsVal s'.mem base o 4 < m ∧ wordsVal s'.mem base o 4 * 2 ^ 256 % m = T % m := by
  -- The modulus: `m + 1 = 2⁶⁴ m'`.
  obtain ⟨hk1, hk2, rfl⟩ := shiftK?_some hk
  have hred := Mod.ok_red hM.red
  rw [hr, hn] at hred
  simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at hred
  obtain ⟨⟨⟨_, hm1⟩, hmv⟩, _⟩ := hred
  have hW : 2 ^ 64 * (2 ^ k + 2 ^ 128 * (2 ^ 64 - 2 ^ k + 1)) = m + 1 := by
    have hmw : mwVal [.pow2 k, .zero, .gen (2 ^ 64 - 2 ^ k + 1), .zero] =
        2 ^ k + 2 ^ 128 * (2 ^ 64 - 2 ^ k + 1) := by
      simp only [mwVal, MWord.val]; omega_arith
    rw [← hmw, hmv]
    have := Nat.div_add_mod (m + 1) (2 ^ 64)
    have : (m + 1) % 2 ^ 64 = 0 := by omega_arith
    omega_arith
  have hm256 := sqrBound ⟨hk1, hk2⟩ hW
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega_arith
    · exact h
  -- The four rounds, in the window rotating through `r8–r11`.
  rw [redRX_eq, WP.block_append_iff]
  refine WP.mono (redRoundX_ok s₁ ⟨hk1, hk2⟩ hW (t := .r8) (w1 := .r9) (w2 := .r10) (w3 := .r11)
    ⟨by decide, by decide⟩) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (redRoundX_ok s₂ ⟨hk1, hk2⟩ hW (t := .r9) (w1 := .r10) (w2 := .r11) (w3 := .r8)
    ⟨by decide, by decide⟩) fun s₃ ⟨e₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (redRoundX_ok s₃ ⟨hk1, hk2⟩ hW (t := .r10) (w1 := .r11) (w2 := .r8) (w3 := .r9)
    ⟨by decide, by decide⟩) fun s₄ ⟨e₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (redRoundX_ok s₄ ⟨hk1, hk2⟩ hW (t := .r11) (w1 := .r8) (w2 := .r9) (w3 := .r10)
    ⟨by decide, by decide⟩) fun s₅ ⟨e₅, k₅⟩ => ?_
  have k₂₅ : Keeps [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11] s₁ s₅ :=
    ((k₂.trans (k₃.mono (by sub_regs))).trans (k₄.mono (by sub_regs))).trans (k₅.mono (by sub_regs))
  have hs₅ := hs₁.of_keeps k₂₅ (by decide)
  -- The high half added.
  rw [WP.block_append_iff]
  refine WP.mono (addHigh_ok s₅) fun s₆ ⟨e₆, k₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have M₆ : s₆.mem = s₁.mem := k₆.2.1.trans k₂₅.2.1
  have hH : regsVal s₅ sqLow = regsVal s₁ sqLow := regsVal_congr fun r hr => k₂₅.1 r (by
    simp only [sqLow, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)
  -- `R = (L + U m) / 2²⁵⁶ + H < 2m`, for the four words `U` of the rounds.
  generalize hR : regsVal s₆ sqLow + 2 ^ 256 * (s₆.gpr .r8).toNat = R
  have hU : ((s₁.gpr .r8).toNat + 2 ^ 64 * (s₂.gpr .r9).toNat + 2 ^ 128 * (s₃.gpr .r10).toNat +
      2 ^ 192 * (s₄.gpr .r11).toNat) * m = (s₁.gpr .r8).toNat * m + 2 ^ 64 * ((s₂.gpr .r9).toNat * m) +
      2 ^ 128 * ((s₃.gpr .r10).toNat * m) + 2 ^ 192 * ((s₄.gpr .r11).toNat * m) := by
    simp only [Nat.add_mul, Nat.mul_assoc]
  generalize (s₁.gpr .r8).toNat + 2 ^ 64 * (s₂.gpr .r9).toNat + 2 ^ 128 * (s₃.gpr .r10).toNat +
    2 ^ 192 * (s₄.gpr .r11).toNat = U at hU
  have hRU : 2 ^ 256 * R = T + U * m ∧ R < 2 * m := by
    have hx := fun (t : State) (r : Reg) => (t.gpr r).isLt
    have b₁ := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₁ .r8))
    have b₂ := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₂ .r9))
    have b₃ := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₃ .r10))
    have b₄ := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₄ .r11))
    have hL := regsVal_lt s₁ [.r8, .r9, .r10, .r11]
    have hT : T = regsVal s₁ [.r8, .r9, .r10, .r11] + 2 ^ 256 * regsVal s₁ sqLow := by
      rw [← hV₁]; simp only [sqLow, regsVal]; omega_arith
    simp only [List.length_cons, List.length_nil] at hL
    rw [← hR]
    omega_using [b₁, b₂, b₃, b₄, e₂, e₃, e₄, e₅, e₆, hH, hU, hTm, hT, hL]
  -- Reduced below `m` and stored.
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hs₆ (M := M) (m := m) (ts := sqLow) (top := .r8) (by rw [hn]; rfl) hM.n0
    ⟨by decide, by decide⟩ hM.mo hM.tmp hM.sep (Mod.ok_sparse hM.red) (by rw [M₆]; exact hM.val)
    (by rw [hn]; exact hR ▸ hRU.2)) fun s₇ ⟨e₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆.of_keepRegs k₇ (by decide)
  refine WP.mono (stores_ok sqLow hs₇ (o := o) (by simp only [sqLow, List.length_cons, List.length_nil]; omega_arith)
    (by decide)) fun s₈ ⟨e₈, k₈, O₈⟩ => ?_
  have hlen : sqLow.length = 4 := rfl
  rw [hlen] at e₈ O₈
  rw [hn] at e₇ O₇
  refine ⟨?_, fun x hx hx' => ?_, ?_, ?_⟩
  · have K : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ r ∈ rs, r ∈ sqrClob) →
        KeepRegs sqrClob t t' := fun k h => (Keeps.regs k).mono h
    exact (((K k₂₅ (by decide)).trans (K k₆ (by decide))).trans (k₇.mono (by decide))).trans
      (k₈.mono (by decide))
  · rw [O₈ x hx, O₇ x hx', M₆]
  · rw [e₈, e₇]; exact Nat.mod_lt _ hm0
  · rw [e₈, e₇, Nat.mod_mul_mod,
      show regsVal s₆ sqLow + 2 ^ (64 * 4) * (s₆.gpr .r8).toNat = R from hR, Nat.mul_comm, hRU.1,
      Nat.add_mul_mod_self_right]

/-- `[o] = [a]² R⁻¹ mod m` for `m' = 2ᵏ + 2¹²⁸ (2⁶⁴ − 2ᵏ + 1)` (P-256's `p`). -/
theorem sqrRX_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) (hn : M.n = 4) {ws : List MWord} (hr : M.red = .friendly ws)
    {k : Nat} (hk : shiftK? ws = some k) {o a : Nat} (ho : o + 32 ≤ size) (ha : a + 32 ≤ size)
    (hA : wordsVal s.mem base a 4 < m) :
    WP isa (.block (sqrRX M k o a)) s fun s' =>
      KeepRegs sqrClob s s' ∧
      (∀ x, (ofs base x < o ∨ o + 32 ≤ ofs base x) →
        (ofs base x < M.tmp ∨ M.tmp + 32 ≤ ofs base x) → s'.mem x = s.mem x) ∧
      wordsVal s'.mem base o 4 < m ∧
      wordsVal s'.mem base o 4 * 2 ^ 256 % m =
        wordsVal s.mem base a 4 * wordsVal s.mem base a 4 % m := by
  rw [sqrRX_eq, WP.block_append_iff]
  refine WP.mono (sqr4_ok (s := s) ⟨hs.rdi, hs.wr, hs.nowrap⟩ ha) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hV₁ : (s₁.gpr .r8).toNat + 2 ^ 64 * regsVal s₁ [.r9, .r10, .r11, .r12, .r13, .r14, .r15] =
      wordsVal s.mem base a 4 * wordsVal s.mem base a 4 := by
    rw [← fe_wordsVal, ← e₁]
    simp only [regsVal, val4]
    omega_arith
  refine WP.mono (redRX_ok (hs.of_keeps k₁ (by decide)) (k₁.2.1 ▸ hM) hn hr hk ho hV₁
    (Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt (wordsVal_lt _ _ _ 4)) hA (Nat.two_pow_pos _))) fun s' ⟨kr, hm, hlt, he⟩ =>
      ⟨((Keeps.regs k₁).mono (by decide)).trans kr, fun x hx hx' => (hm x hx hx').trans (by rw [k₁.2.1]),
        hlt, he⟩

/-- `[o] = [a] [b] R⁻¹ mod m` for `m' = 2ᵏ + 2¹²⁸ (2⁶⁴ − 2ᵏ + 1)` (P-256's `p`). -/
theorem mulRX_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) (hn : M.n = 4) {ws : List MWord} (hr : M.red = .friendly ws)
    {k : Nat} (hk : shiftK? ws = some k) {o a b : Nat} (ho : o + 32 ≤ size) (ha : a + 32 ≤ size)
    (hb : b + 32 ≤ size) (hB : wordsVal s.mem base b 4 < m) :
    WP isa (.block (mulRX M k o a b)) s fun s' =>
      KeepRegs sqrClob s s' ∧
      (∀ x, (ofs base x < o ∨ o + 32 ≤ ofs base x) →
        (ofs base x < M.tmp ∨ M.tmp + 32 ≤ ofs base x) → s'.mem x = s.mem x) ∧
      wordsVal s'.mem base o 4 < m ∧
      wordsVal s'.mem base o 4 * 2 ^ 256 % m =
        wordsVal s.mem base a 4 * wordsVal s.mem base b 4 % m := by
  rw [mulRX_eq, WP.block_append_iff]
  refine WP.mono (mul4_ok (s := s) ⟨hs.rdi, hs.wr, hs.nowrap⟩ hb ha) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hV₁ : (s₁.gpr .r8).toNat + 2 ^ 64 * regsVal s₁ [.r9, .r10, .r11, .r12, .r13, .r14, .r15] =
      wordsVal s.mem base a 4 * wordsVal s.mem base b 4 := by
    rw [← fe_wordsVal, ← fe_wordsVal, Nat.mul_comm (VG.Proof.X25519.X86_64.fe s.mem base a), ← e₁]
    simp only [regsVal, val4]
    omega_arith
  refine WP.mono (redRX_ok (hs.of_keeps k₁ (by decide)) (k₁.2.1 ▸ hM) hn hr hk ho hV₁
    (Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt (wordsVal_lt _ _ _ 4)) hB (Nat.two_pow_pos _))) fun s' ⟨kr, hm, hlt, he⟩ =>
      ⟨((Keeps.regs k₁).mono (by decide)).trans kr, fun x hx hx' => (hm x hx hx').trans (by rw [k₁.2.1]),
        hlt, he⟩

end VG.Proof.Mont.X86_64
