import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-!
# Montgomery arithmetic on x86-64: P-256's squares with BMI2 and ADX

`sqrRX M k o a` (`Impl/Mont/X86_64.lean`): X25519's square `a²` into
`r8–r15` (`sqr4_ok`), then four friendly reductions, each adding `t_i m'` to
the words above `t_i`, which makes `2⁶⁴ V' = V + t_i m` for the value `V` of
the words from `t_i` up (`sqRound_ok`). The first three cannot carry out of
`r15`, as `a² + 2¹⁹² m < 2⁵¹²` for P-256's `p` (any `m` of `sqrRX`'s form,
`m ≤ 2²⁵⁶ − 2¹⁹² + 2⁶⁵`: `sqrBound`); the last carries into `r8`. They leave
`(a² + U m) / 2²⁵⁶ < 2m`, which `csub` reduces below `m` (`sqrRX_ok`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Impl.X25519.X86_64 (sqrA sqrB sqrC sqrD)
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono val4 sqr4_ok)

/-- A round of the reduction: `ts += t₀ m'`, which makes `2⁶⁴ ts' = V + t₀ m`
for the value `V = t₀ + 2⁶⁴ ts` of the words from `t₀` up. -/
theorem sqRound_ok (s : State) {t0 : Reg} {k m : Nat} (hk : 0 < k ∧ k < 64)
    (hm : 2 ^ 64 * (2 ^ k + 2 ^ 128 * (2 ^ 64 - 2 ^ k + 1)) = m + 1) {ts : List Reg}
    (hl : 4 ≤ ts.length) (hf : Fresh ts) (ht0 : t0 ∉ ts)
    (h0 : t0 ≠ .rax ∧ t0 ≠ .rcx ∧ t0 ≠ .rdx ∧ t0 ≠ .rbp)
    (hb : (s.gpr t0).toNat + 2 ^ 64 * regsVal s ts + (s.gpr t0).toNat * m <
      2 ^ 64 * 2 ^ (64 * ts.length)) :
    WP isa (.block (shiftRed true t0 k ts)) s fun s' =>
      2 ^ 64 * regsVal s' ts = (s.gpr t0).toNat + 2 ^ 64 * regsVal s ts + (s.gpr t0).toNat * m ∧
        Keeps (.rax :: .rcx :: .rdx :: .rbp :: ts) s s' := by
  generalize hW : 2 ^ k + 2 ^ 128 * (2 ^ 64 - 2 ^ k + 1) = W at hm
  have key : 2 ^ 64 * ((s.gpr t0).toNat * W) = (s.gpr t0).toNat * m + (s.gpr t0).toNat := by
    rw [Nat.mul_left_comm, hm, Nat.mul_add, Nat.mul_one]
  have hb' : regsVal s ts + (s.gpr t0).toNat * (2 ^ k + 2 ^ 128 * (2 ^ 64 - 2 ^ k + 1)) <
      2 ^ (64 * ts.length) := by
    rw [hW]
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ 64) ?_
    rw [Nat.mul_add, key]
    omega
  refine WP.mono (shiftRed_ok true s hk hl hf ht0 h0 hb') fun s' ⟨e, k'⟩ => ⟨?_, k'⟩
  rw [e, hW, Nat.mul_add, key]
  omega

/-- `m ≤ 2²⁵⁶ − 2¹⁹² + 2⁶⁵` for `m + 1 = 2⁶⁴ (2ᵏ + 2¹²⁸ (2⁶⁴ − 2ᵏ + 1))`, so
that `m² + 2¹⁹² m < 2⁵¹²`. -/
theorem sqrBound {k m : Nat} (hk : 0 < k ∧ k < 64)
    (hm : 2 ^ 64 * (2 ^ k + 2 ^ 128 * (2 ^ 64 - 2 ^ k + 1)) = m + 1) :
    m < 2 ^ 256 ∧ m * m + 2 ^ 192 * m < 2 ^ 512 := by
  have h1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk.1
  have h2 : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  generalize 2 ^ k = K at hm h1 h2
  have hB : m ≤ 2 ^ 256 - 2 ^ 192 + 2 ^ 65 := by omega
  have hmm : m * m ≤ (2 ^ 256 - 2 ^ 192 + 2 ^ 65) * (2 ^ 256 - 2 ^ 192 + 2 ^ 65) :=
    Nat.mul_le_mul hB hB
  have hc : (2 ^ 256 - 2 ^ 192 + 2 ^ 65) * (2 ^ 256 - 2 ^ 192 + 2 ^ 65) +
      2 ^ 192 * (2 ^ 256 - 2 ^ 192 + 2 ^ 65) < 2 ^ 256 * 2 ^ 256 := by decide
  omega

theorem sqrRX_eq (M : Mod) (k o a : Nat) : sqrRX M k o a =
    (sqrA a ++ (sqrB a ++ (sqrC a ++ sqrD a))) ++
      (shiftRed true .r8 k ([.r9, .r10, .r11, .r12, .r13, .r14, .r15] : List Reg) ++
      (shiftRed true .r9 k ([.r10, .r11, .r12, .r13, .r14, .r15] : List Reg) ++
      (shiftRed true .r10 k ([.r11, .r12, .r13, .r14, .r15] : List Reg) ++
      (([.mov32 .r8 (.imm 0)] : List Instr) ++
      (shiftRed true .r11 k (sqLow ++ ([.r8] : List Reg)) ++ (csub M sqLow .r8 ++ stores sqLow o)))))) := by
  simp only [sqrRX, List.append_assoc]

/-- The registers `sqrRX` changes. -/
abbrev sqrClob : List Reg :=
  [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

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
  have hnw := hs.nowrap
  -- The modulus: `m + 1 = 2⁶⁴ m'`.
  obtain ⟨hk1, hk2, rfl⟩ := shiftK?_some hk
  have hred := Mod.ok_red hM.red
  rw [hr, hn] at hred
  simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at hred
  obtain ⟨⟨⟨_, hm1⟩, hmv⟩, _⟩ := hred
  have hW : 2 ^ 64 * (2 ^ k + 2 ^ 128 * (2 ^ 64 - 2 ^ k + 1)) = m + 1 := by
    have hmw : mwVal [.pow2 k, .zero, .gen (2 ^ 64 - 2 ^ k + 1), .zero] =
        2 ^ k + 2 ^ 128 * (2 ^ 64 - 2 ^ k + 1) := by
      simp only [mwVal, MWord.val]; omega
    rw [← hmw, hmv]
    have := Nat.div_add_mod (m + 1) (2 ^ 64)
    have : (m + 1) % 2 ^ 64 = 0 := by omega
    omega
  obtain ⟨hm256, hmm⟩ := sqrBound ⟨hk1, hk2⟩ hW
  have hm0 : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hA
  have hmm2 : m * m < 2 ^ 256 * m := Nat.mul_lt_mul_of_pos_right hm256 hm0
  generalize hT : wordsVal s.mem base a 4 * wordsVal s.mem base a 4 = T
  have hTm : T < m * m := hT ▸ Nat.mul_lt_mul'' hA hA
  -- The square.
  rw [sqrRX_eq, WP.block_append_iff]
  refine WP.mono (sqr4_ok (s := s) ⟨hs.rdi, hs.wr, hs.nowrap⟩ ha) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hV₁ : (s₁.gpr .r8).toNat + 2 ^ 64 * regsVal s₁ [.r9, .r10, .r11, .r12, .r13, .r14, .r15] = T := by
    rw [← hT]
    have hfe : VG.Proof.X25519.X86_64.fe s.mem base a = wordsVal s.mem base a 4 := by
      simp only [VG.Proof.X25519.X86_64.fe, VG.Proof.X25519.X86_64.word,
        VG.Proof.X25519.X86_64.off, val4, wordsVal, word, off, Nat.add_assoc, Nat.reduceAdd]
      omega
    rw [← hfe, ← e₁]
    simp only [regsVal, val4]
    omega
  -- The four reductions.
  have hx := fun (t : State) (r : Reg) => (t.gpr r).isLt
  rw [WP.block_append_iff]
  refine WP.mono (sqRound_ok s₁ ⟨hk1, hk2⟩ hW (t0 := .r8) (by decide) ⟨by decide, by decide⟩ (by decide)
    ⟨by decide, by decide, by decide, by decide⟩ (by
      rw [hV₁]
      have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₁ .r8))
      simp only [List.length_cons, List.length_nil]
      omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [hV₁] at e₂
  rw [WP.block_append_iff]
  refine WP.mono (sqRound_ok s₂ ⟨hk1, hk2⟩ hW (t0 := .r9) (by decide) ⟨by decide, by decide⟩ (by decide)
    ⟨by decide, by decide, by decide, by decide⟩ (by
      have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₁ .r8))
      have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₂ .r9))
      simp only [regsVal] at e₂ ⊢
      simp only [List.length_cons, List.length_nil]
      omega)) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqRound_ok s₃ ⟨hk1, hk2⟩ hW (t0 := .r10) (by decide) ⟨by decide, by decide⟩ (by decide)
    ⟨by decide, by decide, by decide, by decide⟩ (by
      have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₁ .r8))
      have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₂ .r9))
      have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₃ .r10))
      simp only [regsVal] at e₂ e₃ ⊢
      simp only [List.length_cons, List.length_nil]
      omega)) fun s₄ ⟨e₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mov32zero_ok s₄ .r8) fun s₅ ⟨z₅, _, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have g₅ : ∀ r, r ≠ .r8 → s₅.gpr r = s₄.gpr r := fun r h => k₅.1 r (by simpa using h)
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (sqRound_ok s₅ ⟨hk1, hk2⟩ hW (t0 := .r11) (ts := sqLow ++ [.r8]) (by decide)
    ⟨by decide, by decide⟩ (by decide) ⟨by decide, by decide, by decide, by decide⟩ (by
      have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₁ .r8))
      have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₂ .r9))
      have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₃ .r10))
      have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₄ .r11))
      simp only [regsVal] at e₂ e₃ e₄
      simp only [sqLow, List.cons_append, List.nil_append, regsVal, z₅, g₅ _ (by decide : Reg.r11 ≠ .r8),
        g₅ _ (by decide : Reg.r12 ≠ .r8), g₅ _ (by decide : Reg.r13 ≠ .r8),
        g₅ _ (by decide : Reg.r14 ≠ .r8), g₅ _ (by decide : Reg.r15 ≠ .r8), List.length_cons,
        List.length_nil, hz]
      omega)) fun s₆ ⟨e₆, k₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have M₆ : s₆.mem = s.mem :=
    k₆.2.1.trans (k₅.2.1.trans (k₄.2.1.trans (k₃.2.1.trans (k₂.2.1.trans k₁.2.1))))
  -- `R = (a² + U m) / 2²⁵⁶ < 2m`, for the four words `U` of the reductions.
  generalize hR : regsVal s₆ sqLow + 2 ^ 256 * (s₆.gpr .r8).toNat = R
  have hU : ((s₁.gpr .r8).toNat + 2 ^ 64 * (s₂.gpr .r9).toNat + 2 ^ 128 * (s₃.gpr .r10).toNat +
      2 ^ 192 * (s₄.gpr .r11).toNat) * m = (s₁.gpr .r8).toNat * m + 2 ^ 64 * ((s₂.gpr .r9).toNat * m) +
      2 ^ 128 * ((s₃.gpr .r10).toNat * m) + 2 ^ 192 * ((s₄.gpr .r11).toNat * m) := by
    simp only [Nat.add_mul, Nat.mul_assoc]
  generalize (s₁.gpr .r8).toNat + 2 ^ 64 * (s₂.gpr .r9).toNat + 2 ^ 128 * (s₃.gpr .r10).toNat +
    2 ^ 192 * (s₄.gpr .r11).toNat = U at hU
  have hRU : 2 ^ 256 * R = T + U * m ∧ R < 2 * m := by
    have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₁ .r8))
    have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₂ .r9))
    have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₃ .r10))
    have := Nat.mul_le_mul_right m (Nat.le_sub_one_of_lt (hx s₄ .r11))
    simp only [regsVal] at e₂ e₃ e₄
    simp only [sqLow, List.cons_append, List.nil_append, regsVal, z₅, g₅ _ (by decide : Reg.r11 ≠ .r8),
      g₅ _ (by decide : Reg.r12 ≠ .r8), g₅ _ (by decide : Reg.r13 ≠ .r8),
      g₅ _ (by decide : Reg.r14 ≠ .r8), g₅ _ (by decide : Reg.r15 ≠ .r8),
      hz] at e₆
    rw [← hR]
    simp only [sqLow, regsVal]
    omega
  -- Reduced below `m` and stored.
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hs₆ (M := M) (m := m) (ts := sqLow) (top := .r8) (by rw [hn]; rfl) hM.n0
    ⟨by decide, by decide⟩ hM.mo hM.tmp hM.sep (by rw [M₆]; exact hM.val)
    (by rw [hn]; exact hR ▸ hRU.2)) fun s₇ ⟨e₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆.of_keepRegs k₇ (by decide)
  refine WP.mono (stores_ok sqLow hs₇ (o := o) (by simp only [sqLow, List.length_cons, List.length_nil]; omega)
    (by decide)) fun s₈ ⟨e₈, k₈, O₈⟩ => ?_
  have hlen : sqLow.length = 4 := rfl
  rw [hlen] at e₈ O₈
  rw [hn] at e₇ O₇
  refine ⟨?_, fun x hx hx' => ?_, ?_, ?_⟩
  · have K : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ r ∈ rs, r ∈ sqrClob) →
        KeepRegs sqrClob t t' := fun k h => (Keeps.regs k).mono h
    exact (((((((K k₁ (by decide)).trans (K k₂ (by decide))).trans (K k₃ (by decide))).trans
      (K k₄ (by decide))).trans (K k₅ (by decide))).trans (K k₆ (by decide))).trans
      (k₇.mono (by decide))).trans (k₈.mono (by decide))
  · rw [O₈ x hx, O₇ x hx', M₆]
  · rw [e₈, e₇]; exact Nat.mod_lt _ hm0
  · rw [e₈, e₇, Nat.mod_mul_mod,
      show regsVal s₆ sqLow + 2 ^ (64 * 4) * (s₆.gpr .r8).toNat = R from hR, Nat.mul_comm, hRU.1,
      Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86_64
