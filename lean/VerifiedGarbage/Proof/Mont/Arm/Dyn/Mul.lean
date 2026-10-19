module
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Add

import VerifiedGarbage.Proof.Mont.Arm.Dyn.DigitRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
import VerifiedGarbage.Proof.Mont.Arm.Loop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the multiplication

`mul M inv acc o a b` writes `[o] = [a] [b] R⁻¹ mod m` (`mul_ok`): the
accumulator is cleared, each word of `[a]` takes the window two digits up
(`rowD_ok`, by the invariant `MulInv`), and the window, below `2m`, is
reduced into `[o]`.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_mul wp_movw wp_cmp op2_imm op2_reg
  op2_lsr dpVal toNat_add_lt toNat_shr)

/-- The accumulator's length: `2D + 2` digits. -/
def accLen (M : Mod) : Nat := 4 * (2 * digits M + 2)

/-- Where a multiplication's numbers are: in the working space below `2¹⁶`
(`m'` within an immediate offset), and the accumulator apart from `[a]`,
`[b]`, the modulus and `m'`; `[o]` and the temporary area apart from the
accumulator, and from each other, and the temporary area from the modulus. -/
structure MulLayD (M : Mod) (size inv acc o a b : Nat) : Prop where
  acc_le : acc + accLen M ≤ size
  a_le : a + 4 * words M ≤ size
  b_le : b + 4 * words M ≤ size
  mo_le : M.mo + 4 * words M ≤ size
  tmp_le : M.tmp + 4 * words M ≤ size
  o_le : o + 4 * words M ≤ size
  inv_le : inv + 4 ≤ size
  acc16 : acc + accLen M < 2 ^ 16
  a16 : a + 4 * words M < 2 ^ 16
  b16 : b + 4 * words M < 2 ^ 16
  mo16 : M.mo + 4 * words M < 2 ^ 16
  tmp16 : M.tmp + 4 * words M < 2 ^ 16
  o16 : o < 2 ^ 16
  inv16 : inv < 4096
  sa : a + 4 * words M ≤ acc ∨ acc + accLen M ≤ a
  sb : b + 4 * words M ≤ acc ∨ acc + accLen M ≤ b
  smo : M.mo + 4 * words M ≤ acc ∨ acc + accLen M ≤ M.mo
  sinv : inv + 4 ≤ acc ∨ acc + accLen M ≤ inv
  stmp : M.tmp + 4 * words M ≤ acc ∨ acc + accLen M ≤ M.tmp
  so : o + 4 * words M ≤ acc ∨ acc + accLen M ≤ o
  tmo : M.tmp + 4 * words M ≤ M.mo ∨ M.mo + 4 * words M ≤ M.tmp
  ot : o + 4 * words M ≤ M.tmp ∨ M.tmp + 4 * words M ≤ o

/-- The invariant of the multiplication before word `k` of `[a]`: the window
of `D + 2` digits at `acc + 8k` holds `T < 2m` with `2^(32k) T ≡ A B` for the
low `2k` digits `A` of `[a]`, and the digits above it are zero. -/
structure MulInv (s : State) (base : Addr) (size acc a b m W : Nat) (k : Nat) (t : State) : Prop where
  ws : Ws t base size
  rest : Rest dclob s t
  r0 : t.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (acc + 8 * k)
  r1 : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k)
  r6 : t.gpr .r6 = VG.Proof.X25519.Arm.mask16
  out : Outside base acc (4 * (4 * W + 2)) s.mem t.mem
  digs : Digs t.mem base (acc + 8 * k) (2 * W + 2)
  zeros : ∀ l, 2 * k + 2 * W + 2 ≤ l → l < 4 * W + 2 → w32 t.mem base (acc + 4 * l) = 0
  lt : dval t.mem base (acc + 8 * k) (2 * W + 2) < 2 * m
  cong : ∃ U, 2 ^ (32 * k) * dval t.mem base (acc + 8 * k) (2 * W + 2) =
    pval s.mem base a (2 * k) * val32 s.mem base b W + U * m

/-- The congruence two digits on, with the digits of a word. -/
theorem mul_cong {P T T' T'' A B m U u0 u1 q0 q1 : Nat} (h0 : P * T = A * B + U * m)
    (h1 : 2 ^ 16 * T' = T + u0 * B + q0 * m) (h2 : 2 ^ 16 * T'' = T' + u1 * B + q1 * m) :
    2 ^ 32 * P * T'' = (A + u0 * P + u1 * (2 ^ 16 * P)) * B + (U + q0 * P + q1 * (P * 2 ^ 16)) * m := by
  have := cong_step h0 h1 h2
  rw [Nat.mul_comm (2 ^ 32) P, this, Nat.mul_comm (2 ^ 16) P]

/-- An iteration: the rows of the two digits of word `k` of `[a]`, and the
comparison that ends the loop after the last. -/
theorem rowD_ok {s : State} {base : Addr} {size : Nat} {M : Mod} {inv acc o a b m W : Nat}
    (hn : 0 < M.n) (hW : words M = W) (hL : MulLayD M size inv acc o a b)
    (hm : val32 s.mem base M.mo W = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b W < m) {k : Nat} (hk : k < W) {t : State} (I : MulInv s base size acc a b m W k t) :
    WP isa (rowD M inv a b) t fun u => MulInv s base size acc a b m W (k + 1) u ∧ u.z = decide (k + 1 = W) := by
  have hnw := I.ws.nowrap
  have hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega
  obtain ⟨acc_le, a_le, b_le, mo_le, tmp_le, o_le, inv_le, acc16, a16, b16, mo16, tmp16, o16, inv16, sa, sb, smo,
    sinv, stmp, so, tmo, ot⟩ := hL
  simp only [accLen, hD, hW] at acc_le a_le b_le mo_le tmp_le o_le acc16 a16 b16 mo16 tmp16 sa sb smo sinv stmp so tmo ot
  have e12 : t.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
  have hmt : val32 t.mem base M.mo W = m := by rw [I.out.val32 (by omega_using [smo]) (by omega_using [mo_le, hnw])]; exact hm
  have hit : w32 t.mem base inv = w32 s.mem base inv := I.out.w32 (by omega_using [sinv]) (by omega_using [inv_le, hnw])
  have hbt : val32 t.mem base b W = val32 s.mem base b W := I.out.val32 (by omega_using [sb]) (by omega_using [b_le, hnw])
  have hat : w32 t.mem base (a + 4 * k) = w32 s.mem base (a + 4 * k) := I.out.w32 (by omega_using [sa, hk]) (by omega_using [a_le, hk, hnw])
  have L0 : RowLayD M size (acc + 8 * k) b inv :=
    ⟨by rw [hW]; omega_using [b_le], by rw [hW]; omega_using [mo_le], by rw [hD]; omega_using [acc_le, hk], inv_le, by rw [hW]; omega_using [b16], by rw [hW]; omega_using [mo16], inv16,
      by rw [hW, hD]; omega_using [sb, hk], by rw [hW, hD]; omega_using [smo, hk], by rw [hD]; omega_using [sinv, hk]⟩
  have top0 : w32 t.mem base (acc + 8 * k + 4 * (2 * W + 2)) = 0 := by
    have := I.zeros (2 * k + 2 * W + 2) (by omega_using [hk]) (by omega_using [hk])
    rwa [show acc + 4 * (2 * k + 2 * W + 2) = acc + 8 * k + 4 * (2 * W + 2) by omega_using []] at this
  unfold rowD
  refine WP.seq (WP.mono (digitRowD_ok I.ws (m := m) (h := 0) hn L0 (by decide) I.r6 (at_ptr' I.r0 e12) (at_ptr' I.r1 e12)
    (by omega_using [a_le, hk]) (by rw [hW]; exact hmt) (by rw [hit]; exact hinv) (by rw [hW, hbt]; exact hB) (by rw [hD]; exact I.digs)
    (by rw [hD]; exact I.lt) (by rw [hD]; exact top0)) fun t₁ ⟨w₁, p0₁, O₁, D₁, ⟨q₀, hq₀, V₁⟩, R₁⟩ => ?_)
  simp only [hD, hW] at V₁ O₁ D₁
  rw [hat, hbt] at V₁
  have hU0 := hdig_lt (w32 s.mem base (a + 4 * k)) 0
  have hU1 := hdig_lt (w32 s.mem base (a + 4 * k)) 1
  have lt₁ : dval t₁.mem base (acc + 8 * k + 4) (2 * W + 2) < 2 * m := by
    have := row_lt I.lt hU0 hB hq₀; omega_using [V₁, this]
  have e12₁ : t₁.gpr .r12 = s.gpr .r12 := by rw [R₁.gpr _ (by decide)]; exact e12
  have L1 : RowLayD M size (acc + 8 * k + 4) b inv :=
    ⟨by rw [hW]; omega_using [b_le], by rw [hW]; omega_using [mo_le], by rw [hD]; omega_using [acc_le, hk], inv_le, by rw [hW]; omega_using [b16], by rw [hW]; omega_using [mo16], inv16,
      by rw [hW, hD]; omega_using [sb, hk], by rw [hW, hD]; omega_using [smo, hk], by rw [hD]; omega_using [sinv, hk]⟩
  have top1 : w32 t₁.mem base (acc + 8 * k + 4 + 4 * (2 * W + 2)) = 0 := by
    rw [O₁.w32 (by omega_using []) (by omega_using [acc_le, hk, hnw])]
    have := I.zeros (2 * k + 2 * W + 3) (by omega_using [hk]) (by omega_using [hk])
    rwa [show acc + 4 * (2 * k + 2 * W + 3) = acc + 8 * k + 4 + 4 * (2 * W + 2) by omega_using []] at this
  have hm₁ : val32 t₁.mem base M.mo W = m := by rw [O₁.val32 (by omega_using [smo, hk]) (by omega_using [mo_le, hnw])]; exact hmt
  have hi₁ : w32 t₁.mem base inv = w32 s.mem base inv := by rw [O₁.w32 (by omega_using [sinv, hk]) (by omega_using [inv_le, hnw])]; exact hit
  have hb₁ : val32 t₁.mem base b W = val32 s.mem base b W := by rw [O₁.val32 (by omega_using [sb, hk]) (by omega_using [b_le, hnw])]; exact hbt
  have ha₁ : w32 t₁.mem base (a + 4 * k) = w32 s.mem base (a + 4 * k) :=
    (O₁.w32 (d := a + 4 * k) (by omega_using [sa, hk]) (by omega_using [a_le, hk, hnw])).trans hat
  refine WP.seq (WP.mono (digitRowD_ok w₁ (m := m) (h := 1) hn L1 (by decide)
    (by rw [R₁.gpr _ (by decide)]; exact I.r6)
    (by rw [p0₁, e12₁, I.r0, Offset.add_add, Nat.add_assoc]) (Pa := a + 4 * k)
    (by rw [R₁.gpr _ (by decide), e12₁]; exact I.r1)
    (by omega_using [a_le, hk]) (by rw [hW]; exact hm₁) (by rw [hi₁]; exact hinv) (by rw [hW, hb₁]; exact hB) (by rw [hD]; exact D₁)
    (by rw [hD]; exact lt₁) (by rw [hD]; exact top1)) fun t₂ ⟨w₂, p0₂, O₂, D₂, ⟨q₁, hq₁, V₂⟩, R₂⟩ => ?_)
  simp only [hD, hW] at V₂ O₂ D₂
  rw [ha₁, hb₁] at V₂
  have lt₂ : dval t₂.mem base (acc + 8 * k + 4 + 4) (2 * W + 2) < 2 * m := by
    have := row_lt lt₁ hU1 hB hq₁; omega_using [V₂, this]
  have e12₂ : t₂.gpr .r12 = s.gpr .r12 := by rw [R₂.gpr _ (by decide)]; exact e12₁
  refine wp_bump (by decide) fun t₃ v₃ => wp_ptr (d := .r9) (by decide) (by rw [hW]; omega_using [a16]) fun t₄ v₄ =>
    wp_cmp (op2_reg _ _) fun t₅ f₅ z₅ => WP.block_nil ?_
  have r1₄ : t₄.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) + BitVec.ofNat 32 4 := by
    rw [v₄.other .r1 (by decide), v₃.gpr, R₂.gpr .r1 (by decide), R₁.gpr .r1 (by decide), I.r1]
  have r9₄ : t₄.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) + BitVec.ofNat 32 (4 * W - 4 * k) := by
    rw [v₄.gpr, v₃.other .r12 (by decide), e12₂, hW, Offset.add_add]
    rw [show a + 4 * k + (4 * W - 4 * k) = a + 4 * W by omega_using [hk]]
  have m₅ : t₅.mem = t₂.mem := by rw [f₅.mem, v₄.mem, v₃.mem]
  have R₅ : Rest dclob s t₅ := ((I.rest.trans (R₁.mono (by decide))).trans (R₂.mono (by decide))).trans
    (((v₃.rest (by decide)).trans (v₄.rest (by decide))).trans (f₅.rest _))
  refine ⟨⟨((w₂.of_upd v₃ (by decide)).of_upd v₄ (by decide)).of_fupd f₅, R₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₅.gpr, v₄.other .r0 (by decide), v₃.other .r0 (by decide), p0₂, p0₁, I.r0, Offset.add_add,
      Offset.add_add]
    rw [show acc + 8 * k + (4 + 4) = acc + 8 * (k + 1) by omega_using []]
  · rw [f₅.gpr, r1₄, Offset.add_add, show a + 4 * k + 4 = a + 4 * (k + 1) by omega_using []]
  · rw [f₅.gpr, v₄.other .r6 (by decide), v₃.other .r6 (by decide), R₂.gpr _ (by decide), R₁.gpr _ (by decide)]
    exact I.r6
  · rw [m₅]
    exact (I.out.trans (O₁.mono (by omega_using []) (by omega_using [hk]))).trans (O₂.mono (by omega_using []) (by omega_using [hk]))
  · rw [m₅, show acc + 8 * (k + 1) = acc + 8 * k + 4 + 4 by omega_using []]; exact D₂
  · intro l hl hl'
    rw [m₅, O₂.w32 (by omega_using [hl]) (by omega_using [hl', acc_le, hnw]), O₁.w32 (by omega_using [hl]) (by omega_using [hl', acc_le, hnw])]
    exact I.zeros l (by omega_using [hl]) hl'
  · rw [m₅, show acc + 8 * (k + 1) = acc + 8 * k + 4 + 4 by omega_using []]; exact lt₂
  · obtain ⟨U, hU⟩ := I.cong
    refine ⟨U + q₀ * 2 ^ (32 * k) + q₁ * (2 ^ (32 * k) * 2 ^ 16), ?_⟩
    rw [m₅, show acc + 8 * (k + 1) = acc + 8 * k + 4 + 4 by omega_using [], show 32 * (k + 1) = 32 + 32 * k by omega_using [],
      Nat.pow_add, mul_cong hU V₁ V₂, show 2 * (k + 1) = 2 * k + 2 by omega_using [], pval_two]
  · rw [z₅, r1₄, r9₄, sub_add_add, cmp_ofNat (by omega_using []) (by omega_using [a16])]
    simp only [decide_eq_decide]
    omega_using []

theorem dval_zeros {m : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m base (d + 4 * j) = 0) → dval m base d k = 0
  | 0, _ => rfl
  | k + 1, h => by rw [dval, dval_zeros fun j hj => h j (by omega), h k (by omega), Nat.zero_mul]

/-- The modulus is odd when `m m' ≡ -1 (mod 2¹⁶)`. -/
theorem m_pos_of_inv16 {m x : Nat} (h : (m * x + 1) % 2 ^ 16 = 0) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | h'
  · simp at h
  · exact h'

/-- The loop of `mul`, from the invariant at word 0 to the invariant at `W`. -/
theorem mulLoop_ok {s : State} {base : Addr} {size : Nat} {M : Mod} {inv acc o a b m W : Nat}
    (hn : 0 < M.n) (hW : words M = W) (hL : MulLayD M size inv acc o a b)
    (hm : val32 s.mem base M.mo W = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b W < m) {t : State} (h0 : MulInv s base size acc a b m W 0 t) :
    WP isa (.loop (rowD M inv a b) .ne) t fun u => MulInv s base size acc a b m W W u := by
  have hW0 : 0 < W := by rw [← hW]; simp only [Impl.Mont.Arm.words]; omega
  refine WP.loop (M := isa)
    (fun n t' => ∃ k, n = W - k ∧ k < W ∧ MulInv s base size acc a b m W k t') ?_ W t ⟨0, rfl, hW0, h0⟩
  rintro n t' ⟨k, rfl, hk, I⟩
  refine WP.mono (rowD_ok hn hW hL hm hinv hB hk I) fun u ⟨I', hz⟩ => ?_
  by_cases hk1 : k + 1 = W
  · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hk1]; rfl, hk1 ▸ I'⟩
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hk1]; rfl, W - (k + 1), by omega,
      k + 1, rfl, by omega, I'⟩

/-- `[o] = [a] [b] R⁻¹ mod m` (`R = 2^(32W)`), with `m'` at `[inv]`, through
the accumulator at `[acc]` and the temporary area. `[o]` may be `[a]` or `[b]`. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {inv acc o a b m : Nat}
    (hn : 0 < M.n) (hL : MulLayD M size inv acc o a b)
    (hm : val32 s.mem base M.mo (words M) = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b (words M) < m) :
    WP isa (Dynamic.mul M inv acc o a b) s fun t => Ws t base size ∧
      val32 t.mem base o (words M) < m ∧
      val32 t.mem base o (words M) * 2 ^ (32 * words M) % m =
        val32 s.mem base a (words M) * val32 s.mem base b (words M) % m ∧
      Outs base [(o, 4 * words M), (M.tmp, 4 * words M), (acc, 4 * (4 * words M + 2))] s.mem t.mem ∧
      Rest dclob s t := by
  have hnw := hs.nowrap
  have hm0 := m_pos_of_inv16 hinv
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega
  have hW0 : 0 < W := by rw [← hW]; simp only [Impl.Mont.Arm.words]; omega
  have hL' := hL
  obtain ⟨acc_le, a_le, b_le, mo_le, tmp_le, o_le, inv_le, acc16, a16, b16, mo16, tmp16, o16, inv16, sa, sb, smo,
    sinv, stmp, so, tmo, ot⟩ := hL'
  simp only [accLen, hD, hW] at acc_le a_le b_le mo_le tmp_le o_le acc16 a16 b16 mo16 tmp16 sa sb smo sinv stmp so tmo ot
  rw [hW] at hm hB ⊢
  unfold Dynamic.mul
  rw [hD]
  refine WP.seq (WP.mono (zeros_ok hs (o := acc) (k := 2 * (2 * W) + 2) (by omega_using [])
    (by omega_using [acc_le]) (by omega_using [acc16])) fun t₀ ⟨w₀, Z₀, O₀, R₀⟩ => ?_)
  refine WP.seq (wp_movw fun t₁ u₁ => wp_ptr (d := .r0) (by decide) (by omega_using [acc16]) fun t₂ u₂ =>
    wp_ptr (d := .r1) (by decide) (by omega_using [a16]) fun t₃ u₃ => WP.block_nil ?_)
  have e12 : t₀.gpr .r12 = s.gpr .r12 := R₀.gpr _ (by decide)
  have I0 : MulInv s base size acc a b m W 0 t₃ := by
    refine ⟨((w₀.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide),
      (R₀.mono (by decide)).trans (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨0, ?_⟩⟩
    · simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12, Nat.mul_zero, Nat.add_zero]
    · simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12, Nat.mul_zero, Nat.add_zero]
    · simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
    · rw [u₃.mem, u₂.mem, u₁.mem]; exact O₀.mono (by omega_using []) (by omega_using [])
    · intro j hj
      rw [u₃.mem, u₂.mem, u₁.mem, Nat.mul_zero, Nat.add_zero, Z₀ j (by omega_using [hj])]; decide
    · intro l _ hl'
      rw [u₃.mem, u₂.mem, u₁.mem, Z₀ l (by omega_using [hl'])]
    · rw [u₃.mem, u₂.mem, u₁.mem, Nat.mul_zero, Nat.add_zero,
        dval_zeros fun j hj => Z₀ j (by omega_using [hj])]; omega_using [hm0]
    · rw [u₃.mem, u₂.mem, u₁.mem, Nat.mul_zero, Nat.add_zero, dval_zeros fun j hj => Z₀ j (by omega_using [hj])]
      simp [pval]
  clear u₁ u₂ u₃
  refine WP.seq (WP.mono (mulLoop_ok hn hW hL hm hinv hB I0) fun u I => ?_)
  have hmu : val32 u.mem base M.mo W = m := by
    rw [I.out.val32 (by omega_using [smo]) (by omega_using [mo_le, hnw])]; exact hm
  have hmP : m < 2 ^ (32 * W) := by rw [← hm]; exact val32_lt _ _ _ _
  have hsplit : dval u.mem base (acc + 8 * W) (2 * W + 2) = dval u.mem base (acc + 8 * W) (2 * W + 1) +
      w32 u.mem base (acc + 8 * W + 4 * (2 * W + 1)) * 2 ^ (16 * (2 * W + 1)) := by rw [dval]
  have htop : w32 u.mem base (acc + 8 * W + 4 * (2 * W + 1)) = 0 := by
    have hl := I.lt
    rw [hsplit, show 16 * (2 * W + 1) = 32 * W + 16 by omega_using [], Nat.pow_add] at hl
    rcases Nat.eq_zero_or_pos (w32 u.mem base (acc + 8 * W + 4 * (2 * W + 1))) with h | h
    · exact h
    · have : 2 ^ (32 * W) * 2 ^ 16 ≤ w32 u.mem base (acc + 8 * W + 4 * (2 * W + 1)) * (2 ^ (32 * W) * 2 ^ 16) :=
        Nat.le_mul_of_pos_left _ h
      omega_using [hl, hmP, this]
  have hT : dval u.mem base (acc + 8 * W) (2 * W + 1) = dval u.mem base (acc + 8 * W) (2 * W + 2) := by
    rw [hsplit, htop, Nat.zero_mul]; exact (Nat.add_zero _).symm
  refine WP.mono (csubD_ok I.ws (M := M) (src := acc + 4 * (2 * W)) (o := o) (m := m) hn
    (by rw [hD]; omega_using [acc_le]) (by rw [hW]; exact o_le) (by rw [hW]; exact tmp_le) (by rw [hW]; exact mo_le)
    (by rw [hD]; omega_using [acc16]) o16 (by rw [hW]; exact tmp16) (by rw [hW]; exact mo16)
    (by rw [hD, hW]; omega_using [stmp]) (by rw [hW]; exact tmo) (by rw [hD, hW]; omega_using [so]) (by rw [hW]; exact ot)
    (by rw [hW]; exact hmu) hm0
    (by rw [hD, show acc + 4 * (2 * W) = acc + 8 * W by omega_using []]; exact I.digs.mono (by omega_using []))
    (by rw [hD, show acc + 4 * (2 * W) = acc + 8 * W by omega_using [], hT]; exact I.lt))
    fun t ⟨wt, V, O, R⟩ => ⟨wt, ?_, ?_, ?_, I.rest.trans R⟩
  · rw [hW] at V; rw [V]; exact Nat.mod_lt _ hm0
  · rw [hW] at V
    obtain ⟨U, hU⟩ := I.cong
    rw [V, hD, show acc + 4 * (2 * W) = acc + 8 * W by omega_using [], hT, Nat.mod_mul_mod,
      Nat.mul_comm, hU, pval_words, Nat.add_mul_mod_self_right]
  · rw [hW] at O
    refine (Outs.of_outside I.out (by simp)).trans (O.mono (by simp))

end VG.Proof.Mont.Arm.Dyn
