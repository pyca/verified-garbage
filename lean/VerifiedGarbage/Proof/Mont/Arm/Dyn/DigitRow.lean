module
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Arm.Words

import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
import VerifiedGarbage.Proof.Mont.Arm.Loop
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: a digit's rows

`digitRowD M inv b h` takes the window `T < 2m` of `D + 2` digits at `r0`
(the digit above it zero) to `(T + u B + q m) / 2¹⁶` one digit up
(`digitRowD_ok`), for digit `h` (`u`) of the word of `[a]` at `r1`, `B = [b]`
and `q = t₀ m' mod 2¹⁶`, with `m'` at `[inv]`.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_mul wp_movw op2_imm op2_reg op2_lsr
  dpVal toNat_add_lt toNat_shr)

/-- What a digit's rows need of the layout: `[b]`, the modulus and `m'`
apart from the window at `w` and the digit above it. -/
structure RowLayD (M : Mod) (size w b inv : Nat) : Prop where
  b_le : b + 4 * words M ≤ size
  mo_le : M.mo + 4 * words M ≤ size
  w_le : w + 4 * (digits M + 3) ≤ size
  inv_le : inv + 4 ≤ size
  b16 : b + 4 * words M < 2 ^ 16
  mo16 : M.mo + 4 * words M < 2 ^ 16
  inv16 : inv < 4096
  sb : b + 4 * words M ≤ w ∨ w + 4 * (digits M + 3) ≤ b
  smo : M.mo + 4 * words M ≤ w ∨ w + 4 * (digits M + 3) ≤ M.mo
  sinv : inv + 4 ≤ w ∨ w + 4 * (digits M + 3) ≤ inv

theorem digitRowD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {inv b h w m : Nat}
    (hn : 0 < M.n) (hL : RowLayD M size w b inv) (hh : h < 2) (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (h0 : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 w) {Pa : Nat} (h1 : s.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 Pa)
    (hPa : Pa + 4 ≤ size)
    (hm : val32 s.mem base M.mo (words M) = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b (words M) < m) (hd : Digs s.mem base w (digits M + 2))
    (hT : dval s.mem base w (digits M + 2) < 2 * m) (htop : w32 s.mem base (w + 4 * (digits M + 2)) = 0) :
    WP isa (digitRowD M inv b h) s fun u => Ws u base size ∧
      u.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 4 ∧
      Outside base w (4 * digits M + 8) s.mem u.mem ∧ Digs u.mem base (w + 4) (digits M + 2) ∧
      (∃ q, q < 2 ^ 16 ∧ 2 ^ 16 * dval u.mem base (w + 4) (digits M + 2) =
        dval s.mem base w (digits M + 2) + hdig (w32 s.mem base Pa) h * val32 s.mem base b (words M) + q * m) ∧
      Rest [.r0, .r2, .r3, .r4, .r5, .r7, .r8, .r9, .r10] s u := by
  have hnw := hs.nowrap
  obtain ⟨hb_le, hmo_le, hw_le, hinv_le, hb16, hmo16, hinv16, hsb, hsmo, hsinv⟩ := hL
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega_arith
  rw [hD] at hw_le hsb hsmo hsinv hd hT htop ⊢
  rw [hW] at hb_le hmo_le hb16 hmo16 hsb hsmo hm hB ⊢
  have hm0 : m < 2 ^ (16 * (2 * W)) := by
    rw [← hm, show 16 * (2 * W) = 32 * W by omega_arith]; exact val32_lt _ _ _ _
  unfold digitRowD
  -- u
  refine WP.seq (wp_ldr (by decide) (hs.ea (d := 0) h1 (by omega_arith)) (hs.read (d := Pa + 0) (n := 4) (by omega_arith))
    fun s₁ u₁ => wp_half hh (by rw [u₁.other .r6 (by decide)]; exact h6) fun s₂ u₂ => WP.block_nil ?_)
  have hU := hdig_lt (w32 s.mem base Pa) h
  have K₂ : Rest [.r0, .r2, .r3, .r4, .r5, .r7, .r8, .r9, .r10] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  have w₂ := hs.of_rest K₂ (by decide)
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have r2₂ : (s₂.gpr .r2).toNat = hdig (w32 s.mem base Pa) h := by
    rw [u₂.gpr, u₁.gpr, Nat.add_zero, toNat_ofNat_dig]
  have hBp : pval s.mem base b (2 * W) = val32 s.mem base b W := pval_words _ _ _ _
  have hlt₁ : dval s₂.mem base w (2 * W + 2) + (s₂.gpr .r2).toNat * pval s₂.mem base b (2 * W) <
      2 ^ (16 * (2 * W + 2)) := by
    rw [m₂, hBp, r2₂, show 16 * (2 * W + 2) = 16 * (2 * W) + 32 by omega_arith, Nat.pow_add]
    have : hdig (w32 s.mem base Pa) h * val32 s.mem base b W ≤ (2 ^ 16 - 1) * m :=
      Nat.mul_le_mul (by omega_arith) (by omega_arith)
    have : (2 ^ 16 + 1) * m < (2 ^ 16 + 1) * 2 ^ (16 * (2 * W)) := Nat.mul_lt_mul_of_pos_left hm0 (by omega_arith)
    omega_arith
  refine WP.seq (WP.mono (mulRowD_ok w₂ (M := M) (src := b) (w := w) hn
    (by simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h0) (by rw [K₂.gpr _ (by decide)]; exact h6)
    (by rw [r2₂]; exact hU) (by rw [hW]; exact hb_le) (by rw [hW]; exact hb16) (by rw [hD]; omega_arith)
    (by rw [hW, hD]; omega_arith) (by rw [hD, m₂]; exact hd) (by rw [hD]; exact hlt₁)) fun s₃ ⟨w₃, O₃, V₃, D₃, R₃⟩ => ?_)
  rw [hD, m₂, hBp, r2₂] at V₃
  rw [hD] at O₃ D₃
  rw [m₂] at O₃
  -- q
  have K₃ := K₂.trans (R₃.mono (by decide))
  have e0 : s₃.gpr .r0 = s₃.gpr .r12 + BitVec.ofNat 32 w := by
    rw [R₃.gpr .r0 (by decide), R₃.gpr .r12 (by decide)]
    simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h0
  refine WP.seq (wp_ldr (by decide) (w₃.ea (d := 0) e0 (by omega_arith)) (w₃.read (d := w + 0) (n := 4) (by omega_arith))
    fun s₄ u₄ => ?_)
  have w₄ := w₃.of_upd u₄ (by decide)
  refine wp_ldr hinv16 (w₄.ea12 (by omega_arith)) (w₄.read (d := inv) (n := 4) hinv_le)
    fun s₅ u₅ => wp_mul fun s₆ u₆ => wp_dp (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have w₇ := (((w₄.of_upd u₅ (by decide)).of_upd u₆ (by decide))).of_upd u₇ (by decide)
  have m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have mi : w32 s₃.mem base inv = w32 s.mem base inv := O₃.w32 (by omega_arith) (by omega_arith)
  have ht0 : w32 s₃.mem base w = (dval s.mem base w (2 * W + 2) + hdig (w32 s.mem base Pa) h * val32 s.mem base b W) %
      2 ^ 16 := by rw [← V₃, dval_low D₃]
  have g6₃ : s₃.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₃.gpr _ (by decide)]; exact h6
  have hq : (s₇.gpr .r2).toNat = w32 s₃.mem base w * w32 s.mem base inv % 2 ^ 16 := by
    simp only [u₇.get, u₆.get, u₅.get, u₄.get, reduceCtorEq, ↓reduceIte, dpVal]
    rw [toNat_and_r6 g6₃, BitVec.toNat_mul, Nat.add_zero, u₄.mem, ← mi,
      Nat.mod_mod_of_dvd _ (show 2 ^ 16 ∣ 2 ^ 32 from ⟨2 ^ 16, by decide⟩)]
  have hq16 : (s₇.gpr .r2).toNat < 2 ^ 16 := by rw [hq]; exact Nat.mod_lt _ (by decide)
  have hmo₃ : val32 s₃.mem base M.mo W = m := by rw [O₃.val32 (by omega_arith) (by omega_arith)]; exact hm
  have hMp : pval s₇.mem base M.mo (2 * W) = m := by rw [m₇, pval_words, hmo₃]
  have hlt₂ : dval s₇.mem base w (2 * W + 2) + (s₇.gpr .r2).toNat * pval s₇.mem base M.mo (2 * W) <
      2 ^ (16 * (2 * W + 2)) := by
    rw [hMp, m₇, V₃, show 16 * (2 * W + 2) = 16 * (2 * W) + 32 by omega_arith, Nat.pow_add]
    have := row_lt hT hU hB hq16
    have : 2 * 2 ^ 16 * m < 2 * 2 ^ 16 * 2 ^ (16 * (2 * W)) := Nat.mul_lt_mul_of_pos_left hm0 (by omega_arith)
    omega_arith
  have e0₇ : s₇.gpr .r0 = s₇.gpr .r12 + BitVec.ofNat 32 w := by
    simp only [u₇.get, u₆.get, u₅.get, u₄.get, reduceCtorEq, ↓reduceIte]; exact e0
  refine WP.seq (WP.mono (mulRowD_ok w₇ (M := M) (src := M.mo) (w := w) hn e0₇
    (by simp only [u₇.get, u₆.get, u₅.get, u₄.get, reduceCtorEq, ↓reduceIte]; exact g6₃)
    hq16 (by rw [hW]; exact hmo_le) (by rw [hW]; exact hmo16) (by rw [hD]; omega_arith)
    (by rw [hW, hD]; omega_arith) (by rw [hD, m₇]; exact D₃) (by rw [hD]; exact hlt₂)) fun s₈ ⟨w₈, O₈, V₈, D₈, R₈⟩ => ?_)
  rw [hD, m₇, pval_words, hmo₃] at V₈
  rw [hD] at O₈ D₈
  rw [m₇] at O₈
  refine wp_bump (by decide) fun s₉ v₉ => WP.block_nil ?_
  generalize hT1 : dval s.mem base w (2 * W + 2) + hdig (w32 s.mem base Pa) h * val32 s.mem base b W = T1 at *
  generalize hqv : (s₇.gpr .r2).toNat = q at *
  have hz : w32 s₈.mem base w = 0 := by
    rw [← dval_low D₈, V₈, V₃, show (T1 + q * m) % 2 ^ 16 = (T1 % 2 ^ 16 + q * m) % 2 ^ 16 by omega_arith, hq, ← ht0]
    rw [← mi]
    have := hinv; rw [← mi] at this
    exact mont_low16 _ _ _ this
  have htop' : w32 s₈.mem base (w + 4 * (2 * W + 2)) = 0 := by
    rw [O₈.w32 (by omega_arith) (by omega_arith), O₃.w32 (by omega_arith) (by omega_arith)]; exact htop
  have hsh := dval_shift hz htop'
  have m₉ : s₉.mem = s₈.mem := v₉.mem
  refine ⟨w₈.of_upd v₉ (by decide), ?_, ?_, ?_, ⟨q, hq16, ?_⟩, ?_⟩
  · rw [v₉.gpr, R₈.gpr .r0 (by decide), e0₇, h0]
    simp only [u₇.get, u₆.get, u₅.get, u₄.get, reduceCtorEq, ↓reduceIte, R₃.gpr .r12 (by decide), u₂.get, u₁.get]
  · rw [m₉]
    exact (O₃.mono (Nat.le_refl _) (by omega_arith)).trans (O₈.mono (Nat.le_refl _) (by omega_arith))
  · intro j hj
    rw [m₉]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [show w + 4 + 4 * j = w + 4 * (j + 1) by omega_arith]; exact D₈ (j + 1) (by omega_arith)
    · rw [show w + 4 + 4 * (2 * W + 1) = w + 4 * (2 * W + 2) by omega_arith, htop']; decide
  · rw [m₉, hsh, V₈, V₃]
  · exact ((K₃.trans ((((u₄.rest (by decide)).trans (u₅.rest (by decide))).trans ((u₆.rest (by decide)).trans
      (u₇.rest (by decide)))))).trans (R₈.mono (by decide))).trans (v₉.rest (by decide))

end VG.Proof.Mont.Arm.Dyn
