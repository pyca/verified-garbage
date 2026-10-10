import VerifiedGarbage.Proof.Mont.X86_64.SqrS
import VerifiedGarbage.Proof.Mont.X86_64.Rounds

/-!
# Montgomery arithmetic on x86-64: the rounds of P-384's multiplication with BMI2 and ADX

`mulRounds M a b` (`Impl/Mont/X86_64.lean`) for P-384's `p` with BMI2 and
ADX: row 0 is one carry chain into the registers, with no accumulator to
clear or add to (`rowS0_ok` for any multiplier in `rdx`, `mulRow0_ok`), then its reduction (`redSX_ok`) and the
rounds `1 … 5` of `roundX` (`roundsX_ok`); with the other moduli, the
accumulator cleared and `rounds_ok`. Either way `mulRounds_ok` gives
`rounds_ok`'s postcondition for all `n` rounds.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono carryC_ok mulx_ok clear_ok movRdx_ok)

/-- `2^(64·5)` as a product of `2⁶⁴`, which `omega` evaluates. -/
theorem pow64x5 : (2 : Nat) ^ (64 * 5) = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64))) := by
  rw [pow_split 2 64 (64 * 4) (64 * 5) rfl, pow_split 2 64 (64 * 3) (64 * 4) rfl,
    pow_split 2 64 (64 * 2) (64 * 3) rfl, pow_split 2 64 64 (64 * 2) rfl]

theorem keeps_rowS0 {s s₁ s₂ s₃ s₄ s₅ : State} (k₁ : Keeps [.rbp] s s₁) (k₂ : Keeps [.r9, .r8] s₁ s₂)
    (k₃ : Keeps (.rax :: .r9 :: [.r10, .r11, .r12, .r13, .r14]) s₂ s₃) (k₄ : Keeps [.r14] s₃ s₄)
    (k₅ : Keeps [.r15] s₄ s₅) :
    Keeps [.rbp, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s₅ :=
  ((((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))).trans
    (k₄.mono (by sub_regs))).trans (k₅.mono (by sub_regs))

/-- `r8 … r15 = rdx · [b]` in one carry chain. -/
theorem rowS0_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {b : Nat}
    (hb : b + 48 ≤ size) :
    WP isa (.block (rowS0 b)) s fun s' => regsVal s' (wins 6 0) =
          (s.gpr .rdx).toNat * wordsVal s.mem base b 6 ∧
        Keeps [.rbp, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' := by
  rw [rowS0, show ([Impl.X25519.X86_64.clear, .mulx .r9 .r8 (.mem (sc b))] : List Instr) =
    [Impl.X25519.X86_64.clear] ++ [.mulx .r9 .r8 (.mem (sc b))] from rfl, List.append_assoc,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (clear_ok s) fun s₁ h₁ => ?_
  obtain ⟨z₁, cf₁, of₁, k₁⟩ := h₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s₁ (readSrc_sc hs₁ (d := b) (by omega)) (fun _ h => nomatch h) (by decide))
    fun s₂ h₂ => ?_
  obtain ⟨e₂, cf₂, of₂, k₂⟩ := h₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (accRowS_ok 5 .r9 [.r10, .r11, .r12, .r13, .r14] hs₂ (d := b + 8) (by omega) rfl
    ⟨by decide, by decide⟩ (cf₂.trans cf₁)) fun s₃ h₃ => ?_
  obtain ⟨c₃, cf₃, -, e₃, k₃⟩ := h₃
  have z₃ : s₃.gpr .rbp = 0 := by rw [k₃.1 _ (by decide), k₂.1 _ (by decide), z₁]
  rw [show ([.adcx .r14 (.reg .rbp), .mov32 .r15 (.imm 0)] : List Instr) =
    [.adcx .r14 (.reg .rbp)] ++ [.mov32 .r15 (.imm 0)] from rfl, WP.block_append_iff]
  refine WP.mono (carryC_ok s₃ cf₃ z₃) fun s₄ h₄ => ?_
  obtain ⟨c₄, -, -, e₄, k₄⟩ := h₄
  refine WP.mono (mov32zero_ok s₄ .r15) fun s₅ h₅ => ?_
  obtain ⟨z₅, -, k₅⟩ := h₅
  refine ⟨?_, keeps_rowS0 k₁ k₂ k₃ k₄ k₅⟩
  have r8 : s₅.gpr .r8 = s₂.gpr .r8 := by rw [k₅.1 _ (by decide), k₄.1 _ (by decide), k₃.1 _ (by decide)]
  have rdx : s₂.gpr .rdx = s.gpr .rdx := by rw [k₂.1 _ (by decide), k₁.1 _ (by decide)]
  rw [k₁.2.1, k₁.1 _ (by decide)] at e₂
  rw [k₂.2.1, k₁.2.1, rdx] at e₃
  rw [show wordsVal s.mem base b 6 = (word s.mem base b).toNat +
    2 ^ 64 * wordsVal s.mem base (b + 8) 5 from rfl]
  simp only [wins6, regsVal, Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e₃ ⊢
  rw [show win 6 0 0 = .r8 from rfl, show win 6 0 1 = .r9 from rfl, show win 6 0 2 = .r10 from rfl,
    show win 6 0 3 = .r11 from rfl, show win 6 0 4 = .r12 from rfl, show win 6 0 5 = .r13 from rfl,
    show win 6 0 6 = .r14 from rfl, show win 6 0 7 = .r15 from rfl, z₅, r8,
    k₅.1 .r9 (by decide), k₅.1 .r10 (by decide), k₅.1 .r11 (by decide), k₅.1 .r12 (by decide),
    k₅.1 .r13 (by decide), k₅.1 .r14 (by decide), k₄.1 .r9 (by decide), k₄.1 .r10 (by decide),
    k₄.1 .r11 (by decide), k₄.1 .r12 (by decide), k₄.1 .r13 (by decide)]
  have hv := (s.gpr .rdx).isLt
  have hW := wordsVal_lt s.mem base (b + 8) 5
  have key := mul_word_le hv hW
  rw [pow64x5] at e₃ hW key
  generalize (s.gpr .rdx).toNat = v at *
  generalize wordsVal s.mem base (b + 8) 5 = W at *
  generalize (word s.mem base b).toNat = w at *
  have := (s₄.gpr .r14).isLt
  rw [show v * (w + 2 ^ 64 * W) = v * w + 2 ^ 64 * (v * W) by rw [Nat.mul_add, Nat.mul_left_comm]]
  cases c₄ <;> simp only [Bool.toNat_false, Bool.toNat_true] at e₄ <;>
    simp only [show (0 : BitVec 64).toNat = 0 from rfl]
  · rw [e₄]
    generalize (2 : Nat) ^ 64 = B at e₂ e₃ ⊢
    grind only
  · omega_using [e₃, e₄, key, (s₂.gpr .r9).isLt, Bool.toNat_le c₃]

/-- Row 0: `r8 … r15 = a₀ [b]`. -/
theorem mulRow0_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a b : Nat}
    (ha : a + 8 ≤ size) (hb : b + 48 ≤ size) :
    WP isa (.block (mulRowS0 a b)) s fun s' => regsVal s' (wins 6 0) =
          (word s.mem base a).toNat * wordsVal s.mem base b 6 ∧
        Keeps [.rdx, .rbp, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' := by
  rw [mulRowS0, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_sc hs ha)) fun s₁ ⟨d₁, _, _, k₁⟩ => ?_
  refine WP.mono (rowS0_ok (hs.of_keeps k₁ (by decide)) hb) fun s₂ ⟨e₂, k₂⟩ =>
    ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  rw [e₂, d₁, k₁.2.1]

/-- The rounds `1 … k`, from the accumulator of round 1: as `rounds_ok`. -/
theorem rounds1_ok {M : Mod} (hn : M.n < 7) {a b m size : Nat}
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (hmo : M.mo + 8 * M.n ≤ size)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hok : M.ok m = true) :
    ∀ k, k + 1 ≤ M.n → ∀ {s : State} {base : Addr}, Scr s base size →
      MoVal M m s.mem base → wordsVal s.mem base b M.n < m →
      (∃ U, 2 ^ 64 * regsVal s (wins M.n 1) = wordsVal s.mem base a 1 * wordsVal s.mem base b M.n + U * m) →
      regsVal s (wins M.n 1) < 2 * m →
      WP isa (.block ((List.range k).flatMap (fun i => round M a b (i + 1)))) s fun s' =>
        (∃ U, 2 ^ (64 * (k + 1)) * regsVal s' (wins M.n (k + 1)) =
          wordsVal s.mem base a (k + 1) * wordsVal s.mem base b M.n + U * m) ∧
        regsVal s' (wins M.n (k + 1)) < 2 * m ∧
        Keeps (.rax :: .rcx :: .rdx :: .rbp :: acc M.n) s s'
  | 0, _, s, _, _, _, _, h1, hT1 => WP.block_nil ⟨by simpa using h1, hT1, fun _ _ => rfl, rfl, rfl, rfl⟩
  | k + 1, hk, s, base, hs, hm, hB, h1, hT1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (rounds1_ok hn ha hb hmo hinv hok k (by omega) hs hm hB h1 hT1)
      fun s₁ ⟨⟨U, eU⟩, hT, k₁⟩ => ?_
    have hmem : s₁.mem = s.mem := k₁.2.1
    have hs₁ := hs.of_keeps k₁ (by
      intro h
      simp only [List.mem_cons] at h
      rcases h with h | h | h | h | h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact (acc_regs_lt _ hn _ h).2.2.2.2 rfl)
    refine WP.mono (round_ok hs₁ hn (i := k + 1) (by omega) hb hmo (fun h => by rw [hmem]; exact hm h) hinv hok
      (by rw [hmem]; exact hB) hT) fun s₂ ⟨⟨u, eu⟩, hT₂, k₂⟩ => ?_
    rw [hmem] at eu
    refine ⟨⟨U + 2 ^ (64 * (k + 1)) * u, ?_⟩, hT₂, k₁.trans (k₂.mono fun q hq => ?_)⟩
    · calc 2 ^ (64 * (k + 1 + 1)) * regsVal s₂ (wins M.n (k + 1 + 1))
          = 2 ^ (64 * (k + 1)) * (2 ^ 64 * regsVal s₂ (wins M.n (k + 1 + 1))) := by
            rw [Nat.mul_succ, Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ (64 * (k + 1)) * regsVal s₁ (wins M.n (k + 1)) +
            2 ^ (64 * (k + 1)) * (word s.mem base (a + 8 * (k + 1))).toNat * wordsVal s.mem base b M.n +
            2 ^ (64 * (k + 1)) * u * m := by rw [eu]; simp only [Nat.mul_add, Nat.mul_assoc]
        _ = (wordsVal s.mem base a (k + 1) + 2 ^ (64 * (k + 1)) * (word s.mem base (a + 8 * (k + 1))).toNat) *
            wordsVal s.mem base b M.n + (U + 2 ^ (64 * (k + 1)) * u) * m := by
            rw [eU, Nat.add_mul, Nat.add_mul]; omega
        _ = _ := by rw [wordsVal_succ_top _ _ _ (k + 1)]
    · simp only [List.mem_cons] at hq ⊢
      rcases hq with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (wins_sub_acc hn (k + 1) q h))))

theorem keeps_mulS {s s₁ s₂ s₃ : State}
    (k₁ : Keeps [.rdx, .rbp, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s₁)
    (k₂ : Keeps (.rax :: .rcx :: .rdx :: .rbp :: wins 6 0) s₁ s₂)
    (k₃ : Keeps (.rax :: .rcx :: .rdx :: .rbp :: acc 6) s₂ s₃) :
    Keeps (.rax :: .rcx :: .rdx :: .rbp :: acc 6) s s₃ :=
  ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans k₃

/-- The rounds of the multiplication: `2^(64n) T = A B + U m`, `T < 2m`. -/
theorem mulRounds_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkR M size m s.mem base) {a b : Nat} (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mulRounds M a b)) s fun s' =>
      (∃ U, 2 ^ (64 * M.n) * regsVal s' (wins M.n M.n) =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n + U * m) ∧
      regsVal s' (wins M.n M.n) < 2 * m ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: acc M.n) s s' := by
  unfold mulRounds
  split
  · rename_i hc
    obtain ⟨-, hsp, h6⟩ := hc
    obtain ⟨-, hm6⟩ := Mod.ok_sparse hM.red hsp
    have hb6 : b + 48 ≤ size := by rw [h6] at hb; exact hb
    have hB6 : wordsVal s.mem base b 6 < m := by rw [h6] at hB; exact hB
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (mulRow0_ok hs (a := a) (b := b) (by rw [h6] at ha; omega) hb6) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by decide)
    have hA := (word s.mem base a).isLt
    have hAB : (word s.mem base a).toNat * wordsVal s.mem base b 6 ≤ (2 ^ 64 - 1) * m :=
      Nat.mul_le_mul (by omega) (by omega)
    refine WP.mono (redSX_ok (n := 6) (i := 0) rfl hm6 (by rw [e₁]; omega)) fun s₂ ⟨⟨u, hu, eu⟩, k₂⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    have hmem : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
    have hum : u * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    have h1 : wordsVal s.mem base a 1 = (word s.mem base a).toNat := by simp [wordsVal]
    have hT1 : regsVal s₂ (wins 6 1) < 2 * m := by
      refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ 64) ?_
      rw [eu, e₁]; omega
    have hU1 : 2 ^ 64 * regsVal s₂ (wins 6 1) =
        wordsVal s₂.mem base a 1 * wordsVal s₂.mem base b 6 + u * m := by
      rw [hmem, h1, ← e₁]; exact eu
    rw [← h6] at hT1 hU1
    refine WP.mono (rounds1_ok (M := M) hM.n7 ha hb hM.mo hM.inv hM.red 5 (by omega) hs₂
      (fun h => by rw [hmem]; exact hM.val h) (by rw [hmem]; exact hB) ⟨u, hU1⟩ hT1)
      fun s₃ ⟨⟨U, eU⟩, hT, k₃⟩ => ?_
    rw [hmem] at eU
    simp only [Nat.reduceAdd] at eU hT
    rw [h6] at eU hT k₃ ⊢
    exact ⟨⟨U, eU⟩, hT, keeps_mulS k₁ k₂ k₃⟩
  · rw [WP.block_append_iff]
    refine WP.mono (zeros_ok s (acc M.n)) fun s₁ ⟨z₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (fun h => (acc_regs_lt _ hM.n7 _ h).2.2.2.2 rfl)
    have h0 : regsVal s₁ (wins M.n 0) = 0 := regsVal_zero fun r hr => z₁ r (wins_sub_acc hM.n7 0 r hr)
    refine WP.mono (rounds_ok hM.n7 ha hb hM.mo hM.inv hM.red M.n (Nat.le_refl _) hs₁
      (fun h => by rw [k₁.2.1]; exact hM.val h) (by rw [k₁.2.1]; exact hB) h0) fun s₂ ⟨⟨U, eU⟩, hT, k₂⟩ => ?_
    rw [k₁.2.1] at eU
    exact ⟨⟨U, eU⟩, hT, (k₁.mono (by sub_regs)).trans k₂⟩

end VG.Proof.Mont.X86_64
