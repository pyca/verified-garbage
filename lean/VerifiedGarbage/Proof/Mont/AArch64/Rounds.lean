import VerifiedGarbage.Proof.Mont.AArch64.Round

/-!
# Montgomery arithmetic on AArch64: the rounds of the multiplication

The accumulator cleared (`zeros_ok`), then `k` rounds (`rounds_ok`):
`2^(64 k) T = [a]_k B + U m` for some `U`, with `T < 2m`.
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

theorem regsVal_zero {s : State} {rs : List Reg} (h : ∀ r ∈ rs, s.gpr r = 0) : regsVal s rs = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [regsVal, h r (List.mem_cons_self ..), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    rfl

theorem zeros_ok (s : State) : ∀ ts : List Reg,
    WP isa (.block (zeros ts)) s fun s' => (∀ t ∈ ts, s'.gpr t = 0) ∧ Keeps ts s s'
  | [] => WP.block_nil ⟨fun _ h => absurd h (List.not_mem_nil), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | t :: ts => by
    rw [zeros, List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (movz0_ok s t) fun s₁ ⟨z₁, k₁⟩ => ?_
    refine WP.mono (zeros_ok s₁ ts) fun s₂ ⟨z₂, k₂⟩ => ⟨fun q hq => ?_, (k₁.mono (by sub_regs)).trans
      (k₂.mono (by sub_regs))⟩
    by_cases hqt : q ∈ ts
    · exact z₂ q hqt
    · have : q = t := by simpa [hqt] using hq
      subst this; rw [k₂.gpr _ hqt, z₁]

theorem wins_sub_acc_lt : ∀ n < 7, ∀ i < n + 2, ∀ r ∈ wins n i, r ∈ acc n := by decide

theorem wins_sub_acc {n : Nat} (hn : n < 7) (i : Nat) : ∀ r ∈ wins n i, r ∈ acc n := by
  rw [wins_mod]; exact wins_sub_acc_lt n hn _ (Nat.mod_lt _ (by omega))

theorem acc_regs_lt : ∀ n < 7, ∀ r ∈ acc n,
    r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17] := by
  decide

/-- `k` rounds, from a cleared accumulator, with `x7 = 0`, `[b]`'s words in
`bRegs` and the reduction's constant in `x6`. -/
theorem rounds_ok {M : Mod} (hn : M.n < 7) {a b m size : Nat}
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (hmo : M.mo + 8 * M.n ≤ size)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hmo8 : M.mo % 8 = 0)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hred : M.red.ok M.n m = true) :
    ∀ k ≤ M.n, ∀ {s : State} {base : Addr}, Scr s base size → s.gpr .x7 = 0 →
      wordsVal s.mem base M.mo M.n = m → BRegs s base b M.n → ConstOk M s →
      wordsVal s.mem base b M.n < m → regsVal s (wins M.n 0) = 0 →
      WP isa (.block ((List.range k).flatMap (round M a b))) s fun s' =>
        (∃ U, 2 ^ (64 * k) * regsVal s' (wins M.n k) =
          wordsVal s.mem base a k * wordsVal s.mem base b M.n + U * m) ∧
        regsVal s' (wins M.n k) < 2 * m ∧
        Keeps (.x1 :: .x2 :: .x3 :: acc M.n) s s'
  | 0, _, s, _, _, _, _, _, _, hB, h0 => WP.block_nil ⟨⟨0, by simp [h0, wordsVal]⟩, by rw [h0]; omega,
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, hk, s, base, hs, hz, hm, hBR, h6, hB, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (rounds_ok hn ha hb hmo ha8 hb8 hmo8 hinv hred k (by omega) hs hz hm hBR h6 hB h0)
      fun s₁ ⟨⟨U, eU⟩, hT, k₁⟩ => ?_
    have hmem : s₁.mem = s.mem := k₁.mem
    have hacc := acc_regs_lt _ hn
    have nk : ∀ r ∈ [Reg.x0, .x4, .x5, .x6, .x7, .x16, .x17],
        r ∉ Reg.x1 :: Reg.x2 :: Reg.x3 :: acc M.n := by
      intro r hr h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
      rcases h with h | h | h | h
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd h (by decide)
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd h (by decide)
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd h (by decide)
      · have := hacc r h
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at this
    have hs₁ := hs.of_keeps k₁ (nk .x0 (by simp))
    have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr .x7 (nk .x7 (by simp)), hz]
    have hBR₁ : BRegs s₁ base b M.n := hBR.keep hmem fun r hr => k₁.gpr r (nk r (by
      rcases bRegs_regs r hr with rfl | rfl | rfl | rfl <;> simp))
    have h6₁ : ConstOk M s₁ := h6.keep (k₁.gpr .x6 (nk .x6 (by simp)))
    refine WP.mono (round_ok hs₁ hn (i := k) (by omega) hb hmo ha8 hb8 hmo8 hz₁ (by rw [hmem, hm])
      hinv hred hBR₁ h6₁ (by rw [hmem]; exact hB) hT) fun s₂ ⟨⟨u, eu⟩, hT₂, k₂⟩ => ?_
    rw [hmem] at eu
    refine ⟨⟨U + 2 ^ (64 * k) * u, ?_⟩, hT₂, k₁.trans (k₂.mono fun q hq => ?_)⟩
    · calc 2 ^ (64 * (k + 1)) * regsVal s₂ (wins M.n (k + 1))
          = 2 ^ (64 * k) * (2 ^ 64 * regsVal s₂ (wins M.n (k + 1))) := by
            rw [Nat.mul_succ, Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ (64 * k) * regsVal s₁ (wins M.n k) +
            2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat * wordsVal s.mem base b M.n +
            2 ^ (64 * k) * u * m := by rw [eu]; simp only [Nat.mul_add, Nat.mul_assoc]
        _ = (wordsVal s.mem base a k + 2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat) *
            wordsVal s.mem base b M.n + (U + 2 ^ (64 * k) * u) * m := by
            rw [eU, Nat.add_mul, Nat.add_mul]; omega
        _ = _ := by rw [wordsVal_succ_top]
    · simp only [List.mem_cons] at hq ⊢
      rcases hq with h | h | h | h
      any_goals simp only [h, true_or, or_true]
      exact Or.inr (Or.inr (Or.inr (wins_sub_acc hn k q h)))

end VG.Proof.Mont.AArch64
