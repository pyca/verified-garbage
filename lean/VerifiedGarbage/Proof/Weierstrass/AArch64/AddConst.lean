import VerifiedGarbage.Proof.Weierstrass.AArch64.Window

/-!
# The window method on AArch64: the recoded scalar

`addConst n src dst c` writes `c` to `dst`, loads the `n` words at `src` into
`low n` with `top n = 0`, adds `dst` by the carry chain and stores the `n + 1`
words back: `[dst] = [src] + c` when the sum fits (`addConst_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem fresh_low_top : ∀ n < 7, Fresh (low n ++ [top n]) := by unfold Fresh; decide

theorem low_top_clob : ∀ n < 7, ∀ t ∈ .x2 :: (low n ++ [top n]), t ∈ clob n := by
  unfold clob; decide

theorem x0_not_low_top : ∀ n < 7, Reg.x0 ∉ low n ++ [top n] := by decide

/-- `[dst] = [src] + c`, `n + 1` words from `n`. -/
theorem addConst_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n src dst c : Nat}
    (h0 : 0 < n) (h7 : n < 7) (hsrc : src + 8 * n ≤ size) (hdst : dst + 8 * (n + 1) ≤ size)
    (hs8 : src % 8 = 0) (hd8 : dst % 8 = 0) (hsep : src + 8 * n ≤ dst ∨ dst + 8 * (n + 1) ≤ src)
    (hc : c < 2 ^ (64 * (n + 1)))
    (hsum : wordsVal s.mem base src n + c < 2 ^ (64 * (n + 1))) :
    WP isa (.block (WinCfg.addConst n src dst c)) s fun t =>
      wordsVal t.mem base dst (n + 1) = wordsVal s.mem base src n + c ∧ KeepRegs (clob n) s t ∧
      Outside base dst (8 * (n + 1)) s.mem t.mem := by
  have hn := hs.nowrap
  have hf := fresh_low_top n h7
  have h10 : n < 10 := by omega
  have hft := fresh_top_low_lt n h10
  have hl := low_len_lt n h10
  have hcl := low_top_clob n h7
  have hL : (low n ++ [top n]).length = n + 1 := by rw [List.length_append, hl]; rfl
  obtain ⟨t, ts, hts⟩ := low_ne_nil h10 h0
  rw [WinCfg.addConst]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs (n := n + 1) (o := dst) (x := c) hdst hd8 hc) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have vs₁ : wordsVal s₁.mem base src n = wordsVal s.mem base src n :=
    O₁.wordsVal (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (low n) hs₁ (a := src) (by omega) hs8 hft.tail) fun s₂ ⟨e₂, k₂, _⟩ => ?_
  have nx0 : Reg.x0 ∉ low n := fun h => x0_not_low_top n h7 (List.mem_append_left _ h)
  have hs₂ := hs₁.of_keeps k₂ nx0
  rw [WP.block_append_iff]
  refine WP.mono (movz0_ok s₂ (top n)) fun s₃ ⟨z₃, k₃⟩ => ?_
  have ntop : Reg.x0 ∉ [top n] := fun h => x0_not_low_top n h7 (List.mem_append_right _ h)
  have hs₃ := hs₂.of_keeps k₃ ntop
  have htl : top n ∉ low n := (List.nodup_cons.mp hft.1).1
  have r₃ : regsVal s₃ (low n ++ [top n]) = wordsVal s.mem base src n := by
    rw [regsVal_append, regsVal_congr (s := s₂) fun q hq => k₃.gpr q (by
      simp only [List.mem_singleton]; exact fun h => htl (h ▸ hq)), e₂, hl, vs₁]
    simp [regsVal, z₃]
  have d₃ : wordsVal s₃.mem base dst (n + 1) = c := by rw [k₃.mem, k₂.mem, e₁]
  rw [WP.block_append_iff]
  have hL' : low n ++ [top n] = t :: (ts ++ [top n]) := by rw [hts]; rfl
  rw [hL']
  refine WP.mono (chainAdds_ok hs₃ (b := dst) (by rw [← hL', hL]; omega) hd8 (hL' ▸ hf))
    fun s₄ ⟨e₄, k₄⟩ => ?_
  rw [← hL'] at e₄ k₄ ⊢
  rw [hL, r₃, d₃] at e₄
  have hs₄ := hs₃.of_keeps k₄ (by
    intro h; rcases List.mem_cons.mp h with h | h
    · exact absurd h (by decide)
    · exact x0_not_low_top n h7 h)
  have r₄ : regsVal s₄ (low n ++ [top n]) = wordsVal s.mem base src n + c := by
    have := regsVal_lt s₄ (low n ++ [top n])
    rw [hL] at this
    cases hc₄ : s₄.c <;> simp only [hc₄, Bool.toNat_false, Bool.toNat_true] at e₄ <;> omega
  refine WP.mono (stores_ok (low n ++ [top n]) hs₄ (o := dst) (by rw [hL]; omega) hd8 hf.1)
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  rw [hL] at e₅ O₅
  refine ⟨by rw [e₅, r₄], ?_, fun x hx => ?_⟩
  · have c1 : ∀ r ∈ [Reg.x1], r ∈ clob n := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [clob]
    exact ((((k₁.mono c1).trans ((Keeps.regs k₂).mono fun r hr =>
      hcl r (List.mem_cons_of_mem _ (List.mem_append_left _ hr)))).trans
      ((Keeps.regs k₃).mono fun r hr => hcl r (List.mem_cons_of_mem _ (List.mem_append_right _ hr)))).trans
      ((Keeps.regs k₄).mono hcl)).trans (k₅.mono (by simp))
  · rw [O₅ x hx, k₄.mem, k₃.mem, k₂.mem, O₁ x hx]

end VG.Proof.Weierstrass.AArch64
