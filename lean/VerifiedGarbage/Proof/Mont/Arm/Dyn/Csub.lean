module

public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Add
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the conditional subtraction

`csubD M src o` reduces the number at `[src]` (`D` digits and a top digit),
below `2m`, modulo `m` into `[o]` (`csubD_ok`): the difference with `m` is
packed into `[M.tmp]` a word an iteration (`diffDigitD_ok`), and then each
word of `[o]` is that difference's, or the packed digits of `[src]`, under a
mask of the carry and the top digit.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg op2_lsr op2_lsl
  dpVal toNat_add_lt toNat_shr)

/-- Digit `h` of `[src] - m`: `r5 = x + (2¹⁶ - 1 - m_h) + c` for the digit `x` at
`[r10 + 4h]` and `m`'s word in `r7`, its carry to `r3`. -/
theorem diffDigitD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {K h : Nat} (hh : h < 2)
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (h10 : s.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 K)
    (hK : K + 4 * h + 4 ≤ size) (hx : w32 s.mem base (K + 4 * h) < 2 ^ 16) (hc : (s.gpr .r3).toNat ≤ 1) :
    WP isa (.block (diffDigitD h)) s fun u =>
      (u.gpr .r5).toNat = w32 s.mem base (K + 4 * h) + (2 ^ 16 - 1 - hdig (s.gpr .r7).toNat h) + (s.gpr .r3).toNat ∧
      (u.gpr .r3).toNat = (u.gpr .r5).toNat / 2 ^ 16 ∧ u.mem = s.mem ∧ Rest [.r3, .r4, .r5] s u := by
  have hd := hdig_lt (s.gpr .r7).toNat h
  simp only [diffDigitD]
  refine wp_ldr (by omega_arith) (hs.ea h10 (by omega_arith)) (hs.read hK) fun s₁ u₁ => ?_
  refine wp_half hh (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have r6 : (VG.Proof.X25519.Arm.mask16).toNat = 2 ^ 16 - 1 := rfl
  have hx' : (s.mem.readW (off base (K + 4 * h)) 32).toNat < 2 ^ 16 := hx
  have ew : w32 s.mem base (K + 4 * h) = (s.mem.readW (off base (K + 4 * h)) 32).toNat := rfl
  have v5 : (s₅.gpr .r5).toNat = w32 s.mem base (K + 4 * h) + (2 ^ 16 - 1 - hdig (s.gpr .r7).toNat h) +
      (s.gpr .r3).toNat := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, dpVal, h6]
    refine (toNat_add_eq (toNat_sub_eq (toNat_add_eq rfl r6 ?_) (toNat_ofNat_dig _ _) ?_) rfl ?_).trans ?_
    · exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hx _) (by decide)
    · omega_arith
    · omega_arith
    · omega_arith
  refine ⟨by rw [u₆.other .r5 (by decide), v5], by rw [u₆.gpr, toNat_shr, u₆.other .r5 (by decide)],
    by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_⟩
  exact (((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))).trans
    ((u₅.rest (by simp)).trans (u₆.rest (by simp)))

/-- A word of the difference, as numbers. -/
theorem diff_word {x0 x1 m0 m1 c Mw : Nat} (hm : Mw = m0 + m1 * 2 ^ 16) (hm0 : m0 < 2 ^ 16) (hm1 : m1 < 2 ^ 16)
    (hx0 : x0 < 2 ^ 16) (hc : c ≤ 1) :
    ((x0 + (2 ^ 16 - 1 - m0) + c) % 2 ^ 16 +
      (x1 + (2 ^ 16 - 1 - m1) + (x0 + (2 ^ 16 - 1 - m0) + c) / 2 ^ 16) % 2 ^ 16 * 2 ^ 16) +
      2 ^ 32 * ((x1 + (2 ^ 16 - 1 - m1) + (x0 + (2 ^ 16 - 1 - m0) + c) / 2 ^ 16) / 2 ^ 16) + Mw =
    x0 + 2 ^ 16 * x1 + (2 ^ 32 - 1) + c := by
  subst hm
  have h0 : (x0 + (2 ^ 16 - 1 - m0) + c) / 2 ^ 16 ≤ 1 := by omega_arith
  generalize hq : (x0 + (2 ^ 16 - 1 - m0) + c) / 2 ^ 16 = q at *
  have e0 := Nat.mod_add_div (x0 + (2 ^ 16 - 1 - m0) + c) (2 ^ 16)
  have e1 := Nat.mod_add_div (x1 + (2 ^ 16 - 1 - m1) + q) (2 ^ 16)
  rw [hq] at e0
  generalize (x0 + (2 ^ 16 - 1 - m0) + c) % 2 ^ 16 = a0 at *
  generalize (x1 + (2 ^ 16 - 1 - m1) + q) % 2 ^ 16 = a1 at *
  generalize (x1 + (2 ^ 16 - 1 - m1) + q) / 2 ^ 16 = q1 at *
  omega_arith

/-- An iteration of the difference, as numbers. -/
theorem diff_step {T c P M D w c' Mw x0 x1 : Nat} (h : T + c * P + M = D + P)
    (hw : w + 2 ^ 32 * c' + Mw = x0 + 2 ^ 16 * x1 + (2 ^ 32 - 1) + c) :
    T + P * w + c' * (2 ^ 32 * P) + (M + P * Mw) = D + x0 * P + x1 * (2 ^ 16 * P) + 2 ^ 32 * P := by
  have hw' : w + 2 ^ 32 * c' + Mw + 1 = x0 + 2 ^ 16 * x1 + 2 ^ 32 + c := by omega_arith
  have e : P * (w + 2 ^ 32 * c' + Mw + 1) = P * (x0 + 2 ^ 16 * x1 + 2 ^ 32 + c) := by rw [hw']
  grind

/-- The body of the difference's loop: word `j` of `[src] - m` (digits at
`[r10]`, `m`'s word at `[r1]`) packed into `[r8]`, from the carry `r3`. -/
theorem diffBody_ok {u : State} {base : Addr} {size : Nat} (hs : Ws u base size) {S Mo Tp : Nat}
    (h6 : u.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hc : (u.gpr .r3).toNat ≤ 1)
    (h10 : u.gpr .r10 = u.gpr .r12 + BitVec.ofNat 32 S) (h1 : u.gpr .r1 = u.gpr .r12 + BitVec.ofNat 32 Mo)
    (h8 : u.gpr .r8 = u.gpr .r12 + BitVec.ofNat 32 Tp)
    (hS : S + 8 ≤ size) (hM : Mo + 4 ≤ size) (hT : Tp + 4 ≤ size)
    (hx0 : w32 u.mem base S < 2 ^ 16) (hx1 : w32 u.mem base (S + 4) < 2 ^ 16) :
    WP isa (.block (([.ldr .r7 .r1 0] : List Instr) ++ diffDigitD 0 ++ ([.dp .and .r2 .r5 (.reg .r6)] : List Instr) ++
      diffDigitD 1 ++ ([.dp .orr .r2 .r2 (.shifted .r5 .lsl 16), .str .r2 .r8 0, bump .r10 8, bump .r1 4,
        bump .r8 4] : List Instr))) u fun v =>
      ∃ w : BitVec 32, v.mem = u.mem.writeW (off base Tp) w ∧ (v.gpr .r3).toNat ≤ 1 ∧
        w.toNat + 2 ^ 32 * (v.gpr .r3).toNat + w32 u.mem base Mo =
          w32 u.mem base S + 2 ^ 16 * w32 u.mem base (S + 4) + (2 ^ 32 - 1) + (u.gpr .r3).toNat ∧
        v.gpr .r10 = u.gpr .r10 + BitVec.ofNat 32 8 ∧ v.gpr .r1 = u.gpr .r1 + BitVec.ofNat 32 4 ∧
        v.gpr .r8 = u.gpr .r8 + BitVec.ofNat 32 4 ∧ v.gpr .r6 = u.gpr .r6 ∧
        Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r8, .r10] u v ∧ Ws v base size := by
  have hnw := hs.nowrap
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  refine wp_ldr (by decide) (hs.ea (K := Mo) (d := 0) h1 (by omega_arith)) (hs.read (d := Mo + 0) (n := 4) (by omega_arith))
    fun u₁ v₁ => ?_
  have w₁ := hs.of_upd v₁ (by decide)
  have e10 : u₁.gpr .r10 = u₁.gpr .r12 + BitVec.ofNat 32 S := by
    rw [v₁.other .r10 (by decide), v₁.other .r12 (by decide)]; exact h10
  refine VG.Proof.X25519.Arm.WP.append (diffDigitD_ok w₁ (h := 0) (by decide)
    (by rw [v₁.other .r6 (by decide)]; exact h6) e10 (by omega_arith) (by rw [v₁.mem, Nat.mul_zero, Nat.add_zero]; exact hx0)
    (by rw [v₁.other .r3 (by decide)]; exact hc)) fun u₂ ⟨E₂, C₂, M₂, R₂⟩ => ?_
  refine wp_dp (op2_reg _ _) fun u₃ v₃ => ?_
  have w₃ := (w₁.of_rest R₂ (by decide)).of_upd v₃ (by decide)
  rw [v₁.mem, v₁.other .r3 (by decide), Nat.mul_zero, Nat.add_zero] at E₂
  have hd0 := hdig_lt (u₁.gpr .r7).toNat 0
  have hd1 := hdig_lt (u₁.gpr .r7).toNat 1
  have b₂ : (u₂.gpr .r5).toNat < 2 ^ 17 := by rw [E₂]; omega_arith
  refine VG.Proof.X25519.Arm.WP.append (diffDigitD_ok w₃ (K := S) (h := 1) (by decide)
    (by rw [v₃.other .r6 (by decide), R₂.gpr _ (by decide), v₁.other .r6 (by decide)]; exact h6)
    (by rw [v₃.other .r10 (by decide), v₃.other .r12 (by decide), R₂.gpr _ (by decide), R₂.gpr _ (by decide)]; exact e10)
    (by omega_arith) (by rw [v₃.mem, M₂, v₁.mem, Nat.mul_one]; exact hx1)
    (by rw [v₃.other .r3 (by decide), C₂]; omega_arith)) fun u₄ ⟨E₄, C₄, M₄, R₄⟩ => ?_
  refine wp_dp (op2_lsl (by decide)) fun u₅ v₅ => ?_
  have w₅ := (w₃.of_rest R₄ (by decide)).of_upd v₅ (by decide)
  have e8 : u₅.gpr .r8 = u₅.gpr .r12 + BitVec.ofNat 32 Tp := by
    simp only [v₅.get, v₃.get, v₁.get, R₄.gpr .r8 (by decide), R₄.gpr .r12 (by decide), R₂.gpr .r8 (by decide),
      R₂.gpr .r12 (by decide), reduceCtorEq, ↓reduceIte]; exact h8
  refine wp_str (by decide) (w₅.ea (d := 0) e8 (by omega_arith)) (w₅.write (d := Tp + 0) (n := 4) (by omega_arith))
    fun u₆ m₆ => wp_bump (by decide) fun u₇ v₇ => wp_bump (by decide) fun u₈ v₈ => wp_bump (by decide) fun u₉ v₉ =>
      WP.block_nil ?_
  rw [v₃.mem, M₂, v₁.mem, v₃.other .r3 (by decide), C₂, Nat.mul_one] at E₄
  rw [v₃.other .r7 (by decide), R₂.gpr .r7 (by decide)] at E₄
  have r2₄ : (u₄.gpr .r2).toNat = (u₂.gpr .r5).toNat % 2 ^ 16 := by
    rw [R₄.gpr _ (by decide), v₃.gpr, dpVal, toNat_and_r6 (by rw [R₂.gpr _ (by decide), v₁.other .r6 (by decide)]; exact h6)]
  have pk : (u₅.gpr .r2).toNat = (u₂.gpr .r5).toNat % 2 ^ 16 + (u₄.gpr .r5).toNat % 2 ^ 16 * 2 ^ 16 := by
    rw [v₅.gpr, dpVal, pack_toNat _ _ (by rw [r2₄]; omega_arith), r2₄]
  have r7₁ : (u₁.gpr .r7).toNat = w32 u.mem base Mo := by rw [v₁.gpr, Nat.add_zero]
  have hm := word_digits (w32 u.mem base Mo) (BitVec.isLt _)
  rw [r7₁] at E₂ E₄ hd0 hd1
  have c₉ : u₉.gpr .r3 = u₄.gpr .r3 := by
    simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, reduceCtorEq, ↓reduceIte]
  refine ⟨u₅.gpr .r2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₉.mem, v₈.mem, v₇.mem, m₆.mem, v₅.mem, M₄, v₃.mem, M₂, v₁.mem, Nat.add_zero]
  · rw [c₉, C₄, E₄, E₂]; omega_arith
  · rw [c₉, C₄, pk, E₄, E₂]
    exact diff_word hm hd0 hd1 hx0 hc
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₃.get, v₁.get, R₄.gpr .r10 (by decide),
      R₂.gpr .r10 (by decide), reduceCtorEq, ↓reduceIte]
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₃.get, v₁.get, R₄.gpr .r1 (by decide),
      R₂.gpr .r1 (by decide), reduceCtorEq, ↓reduceIte]
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₃.get, v₁.get, R₄.gpr .r8 (by decide),
      R₂.gpr .r8 (by decide), reduceCtorEq, ↓reduceIte]
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₃.get, v₁.get, R₄.gpr .r6 (by decide),
      R₂.gpr .r6 (by decide), reduceCtorEq, ↓reduceIte]
  · exact ((((v₁.rest (by decide)).trans (R₂.mono (by decide))).trans ((v₃.rest (by decide)).trans
      (R₄.mono (by decide)))).trans ((v₅.rest (by decide)).trans (m₆.rest _))).trans
      (((v₇.rest (by decide)).trans (v₈.rest (by decide))).trans (v₉.rest (by decide)))
  · exact (((w₅.of_mupd m₆).of_upd v₇ (by decide)).of_upd v₈ (by decide)).of_upd v₉ (by decide)

/-- The body of the selection's loop: word `j` of `[o]` (at `[r1]`) is the
difference's (at `[r8]`) under the mask `r3`, else the packed digits at `[r10]`. -/
theorem selBody_ok {u : State} {base : Addr} {size : Nat} (hs : Ws u base size) {S Tp O : Nat} (b : Bool)
    (h3 : u.gpr .r3 = if b then BitVec.allOnes 32 else 0)
    (h10 : u.gpr .r10 = u.gpr .r12 + BitVec.ofNat 32 S) (h8 : u.gpr .r8 = u.gpr .r12 + BitVec.ofNat 32 Tp)
    (h1 : u.gpr .r1 = u.gpr .r12 + BitVec.ofNat 32 O)
    (hS : S + 8 ≤ size) (hT : Tp + 4 ≤ size) (hO : O + 4 ≤ size)
    (hx0 : w32 u.mem base S < 2 ^ 16) (hx1 : w32 u.mem base (S + 4) < 2 ^ 16) :
    WP isa (.block [.ldr .r5 .r10 0, .ldr .r7 .r10 4, .dp .orr .r5 .r5 (.shifted .r7 .lsl 16),
      .ldr .r7 .r8 0, .dp .eor .r7 .r7 (.reg .r5), .dp .and .r7 .r7 (.reg .r3),
      .dp .eor .r5 .r5 (.reg .r7), .str .r5 .r1 0, bump .r10 8, bump .r8 4, bump .r1 4]) u fun v =>
      ∃ w : BitVec 32, v.mem = u.mem.writeW (off base O) w ∧
        w.toNat = (if b then w32 u.mem base Tp else w32 u.mem base S + w32 u.mem base (S + 4) * 2 ^ 16) ∧
        v.gpr .r10 = u.gpr .r10 + BitVec.ofNat 32 8 ∧ v.gpr .r8 = u.gpr .r8 + BitVec.ofNat 32 4 ∧
        v.gpr .r1 = u.gpr .r1 + BitVec.ofNat 32 4 ∧ v.gpr .r3 = u.gpr .r3 ∧ Rest [.r1, .r5, .r7, .r8, .r10] u v ∧
        Ws v base size := by
  have hnw := hs.nowrap
  refine wp_ldr (by decide) (hs.ea (d := 0) h10 (by omega_arith)) (hs.read (d := S + 0) (n := 4) (by omega_arith)) fun u₁ v₁ => ?_
  have w₁ := hs.of_upd v₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (d := 4) (by rw [v₁.other .r10 (by decide), v₁.other .r12 (by decide)]; exact h10)
    (by omega_arith)) (w₁.read (d := S + 4) (n := 4) (by omega_arith)) fun u₂ v₂ => ?_
  have w₂ := w₁.of_upd v₂ (by decide)
  refine wp_dp (op2_lsl (by decide)) fun u₃ v₃ => ?_
  have w₃ := w₂.of_upd v₃ (by decide)
  refine wp_ldr (by decide) (w₃.ea (d := 0) (K := Tp) (by simp only [v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact h8)
    (by omega_arith)) (w₃.read (d := Tp + 0) (n := 4) (by omega_arith)) fun u₄ v₄ => ?_
  refine wp_dp (op2_reg _ _) fun u₅ v₅ => wp_dp (op2_reg _ _) fun u₆ v₆ => wp_dp (op2_reg _ _) fun u₇ v₇ => ?_
  have w₇ := (((w₃.of_upd v₄ (by decide)).of_upd v₅ (by decide)).of_upd v₆ (by decide)).of_upd v₇ (by decide)
  refine wp_str (by decide) (w₇.ea (d := 0) (K := O)
    (by simp only [v₇.get, v₆.get, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact h1)
    (by omega_arith)) (w₇.write (d := O + 0) (n := 4) (by omega_arith))
    fun u₈ m₈ => wp_bump (by decide) fun u₉ v₉ => wp_bump (by decide) fun u₁₀ v₁₀ => wp_bump (by decide) fun u₁₁ v₁₁ =>
      WP.block_nil ?_
  have m₇ : u₇.mem = u.mem := by rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  have r5₃ : (u₃.gpr .r5).toNat = w32 u.mem base S + w32 u.mem base (S + 4) * 2 ^ 16 := by
    rw [v₃.gpr, dpVal, v₂.other .r5 (by decide), pack_toNat _ _ (by rw [v₁.gpr, Nat.add_zero]; exact hx0), v₁.gpr,
      v₂.gpr, v₁.mem, Nat.add_zero, Nat.mod_eq_of_lt hx1]
  have val : u₇.gpr .r5 = if b then u.mem.readW (off base Tp) 32 else u₃.gpr .r5 := by
    simp only [v₇.get, v₆.get, v₅.get, v₄.get, reduceCtorEq, ↓reduceIte, dpVal, v₃.get, v₂.get, v₁.get, h3]
    rw [v₃.mem, v₂.mem, v₁.mem, Nat.add_zero, select_val]
    rfl
  refine ⟨u₇.gpr .r5, by rw [v₁₁.mem, v₁₀.mem, v₉.mem, m₈.mem, m₇, Nat.add_zero], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [val]; cases b
    · exact r5₃
    · rfl
  · simp only [v₁₁.get, v₁₀.get, v₉.get, m₈.gpr, v₇.get, v₆.get, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get,
      reduceCtorEq, ↓reduceIte]
  · simp only [v₁₁.get, v₁₀.get, v₉.get, m₈.gpr, v₇.get, v₆.get, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get,
      reduceCtorEq, ↓reduceIte]
  · simp only [v₁₁.get, v₁₀.get, v₉.get, m₈.gpr, v₇.get, v₆.get, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get,
      reduceCtorEq, ↓reduceIte]
  · simp only [v₁₁.get, v₁₀.get, v₉.get, m₈.gpr, v₇.get, v₆.get, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get,
      reduceCtorEq, ↓reduceIte]
  · exact (((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans ((v₃.rest (by decide)).trans
      (v₄.rest (by decide)))).trans (((v₅.rest (by decide)).trans (v₆.rest (by decide))).trans
      (v₇.rest (by decide)))).trans (m₈.rest _)).trans
      (((v₉.rest (by decide)).trans (v₁₀.rest (by decide))).trans (v₁₁.rest (by decide)))
  · exact (((w₇.of_mupd m₈).of_upd v₉ (by decide)).of_upd v₁₀ (by decide)).of_upd v₁₁ (by decide)

/-- Words packing pairs of digits are the digits' number. -/
theorem val32_pack {m m' : Mem} {base : Addr} {o src : Nat} :
    ∀ {W : Nat}, (∀ i < W, w32 m' base (o + 4 * i) = w32 m base (src + 8 * i) + w32 m base (src + 8 * i + 4) * 2 ^ 16) →
      val32 m' base o W = dval m base src (2 * W)
  | 0, _ => rfl
  | W + 1, h => by
    rw [val32_succ, show 2 * (W + 1) = 2 * W + 2 by omega_arith, dval_two, val32_pack fun i hi => h i (by omega_arith),
      h W (by omega_arith)]
    grind

/-- Numbers whose words agree, at other offsets. -/
theorem val32_move {m m' : Mem} {base : Addr} {o d : Nat} :
    ∀ {k : Nat}, (∀ i < k, w32 m' base (o + 4 * i) = w32 m base (d + 4 * i)) → val32 m' base o k = val32 m base d k
  | 0, _ => rfl
  | k + 1, h => by rw [val32_succ, val32_succ, val32_move fun i hi => h i (by omega_arith), h k (by omega_arith)]

/-- The invariant of the difference's loop after `j` words. -/
structure DiffInv (s : State) (base : Addr) (size src tmp mo : Nat) (j : Nat) (u : State) : Prop where
  ws : Ws u base size
  rest : Rest dclob s u
  r6 : u.gpr .r6 = VG.Proof.X25519.Arm.mask16
  r3 : (u.gpr .r3).toNat ≤ 1
  r10 : u.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 src + BitVec.ofNat 32 (8 * j)
  r8 : u.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 tmp + BitVec.ofNat 32 (4 * j)
  val : val32 u.mem base tmp j + (u.gpr .r3).toNat * 2 ^ (32 * j) + val32 s.mem base mo j =
    dval s.mem base src (2 * j) + 2 ^ (32 * j)
  out : Outside base tmp (4 * j) s.mem u.mem

theorem DiffInv.fupd {s : State} {base : Addr} {size src tmp mo j : Nat} {u u' : State}
    (h : DiffInv s base size src tmp mo j u) (f : Fupd u u') : DiffInv s base size src tmp mo j u' :=
  ⟨h.ws.of_fupd f, h.rest.trans (f.rest _), by rw [f.gpr]; exact h.r6, by rw [f.gpr]; exact h.r3,
    by rw [f.gpr]; exact h.r10, by rw [f.gpr]; exact h.r8, by rw [f.gpr, f.mem]; exact h.val,
    by rw [f.mem]; exact h.out⟩

/-- The invariant of the selection's loop after `j` words. -/
structure SelInv (s : State) (base : Addr) (size src tmp o : Nat) (b : Bool) (m₁ : Mem) (j : Nat) (u : State) :
    Prop where
  ws : Ws u base size
  rest : Rest dclob s u
  r3 : u.gpr .r3 = if b then BitVec.allOnes 32 else 0
  r10 : u.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 src + BitVec.ofNat 32 (8 * j)
  r1 : u.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 o + BitVec.ofNat 32 (4 * j)
  words : ∀ i < j, w32 u.mem base (o + 4 * i) =
    if b then w32 m₁ base (tmp + 4 * i) else w32 s.mem base (src + 8 * i) + w32 s.mem base (src + 8 * i + 4) * 2 ^ 16
  out : Outside base o (4 * j) m₁ u.mem

theorem SelInv.fupd {s : State} {base : Addr} {size src tmp o : Nat} {b : Bool} {m₁ : Mem} {j : Nat} {u u' : State}
    (h : SelInv s base size src tmp o b m₁ j u) (f : Fupd u u') : SelInv s base size src tmp o b m₁ j u' :=
  ⟨h.ws.of_fupd f, h.rest.trans (f.rest _), by rw [f.gpr]; exact h.r3, by rw [f.gpr]; exact h.r10,
    by rw [f.gpr]; exact h.r1, by rw [f.mem]; exact h.words, by rw [f.mem]; exact h.out⟩

/-- The separations of `csubD`'s slots, out of `omega`'s sight: it
case-splits on every disjunction (and conjunction) among the hypotheses, so
each side condition adds the ones it needs. -/
structure CsubSep (W src o tmp mo : Nat) : Prop where
  ts : tmp + 4 * W ≤ src ∨ src + 4 * (2 * W + 1) ≤ tmp
  tm : tmp + 4 * W ≤ mo ∨ mo + 4 * W ≤ tmp
  os : o + 4 * W ≤ src ∨ src + 4 * (2 * W + 1) ≤ o
  ot : o + 4 * W ≤ tmp ∨ tmp + 4 * W ≤ o

/-- `[o] = [src] mod m` for the number `[src] < 2m` (`D` digits and a top digit),
through `[M.tmp]`. -/
theorem csubD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {src o m : Nat}
    (hn : 0 < M.n) (hsrc : src + 4 * (digits M + 1) ≤ size) (ho : o + 4 * words M ≤ size)
    (htmp : M.tmp + 4 * words M ≤ size) (hmo : M.mo + 4 * words M ≤ size)
    (h16 : src + 4 * (digits M + 1) < 2 ^ 16) (h16o : o < 2 ^ 16) (h16t : M.tmp + 4 * words M < 2 ^ 16)
    (h16m : M.mo + 4 * words M < 2 ^ 16)
    (hts : M.tmp + 4 * words M ≤ src ∨ src + 4 * (digits M + 1) ≤ M.tmp)
    (htm : M.tmp + 4 * words M ≤ M.mo ∨ M.mo + 4 * words M ≤ M.tmp)
    (hos : o + 4 * words M ≤ src ∨ src + 4 * (digits M + 1) ≤ o)
    (hot : o + 4 * words M ≤ M.tmp ∨ M.tmp + 4 * words M ≤ o)
    (hm : val32 s.mem base M.mo (words M) = m) (hm0 : 0 < m) (hd : Digs s.mem base src (digits M + 1))
    (hV : dval s.mem base src (digits M + 1) < 2 * m) :
    WP isa (csubD M src o) s fun t => Ws t base size ∧
      val32 t.mem base o (words M) = dval s.mem base src (digits M + 1) % m ∧
      Outs base [(M.tmp, 4 * words M), (o, 4 * words M)] s.mem t.mem ∧ Rest dclob s t := by
  have hnw := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega_arith
  rw [hD] at hsrc h16 hts hos hd hV ⊢
  rw [hW] at ho htmp hmo h16t h16m hts htm hos hot hm ⊢
  have hW0 : 0 < W := by rw [← hW]; simp only [Impl.Mont.Arm.words]; omega_arith
  have hsep : CsubSep W src o M.tmp M.mo := ⟨hts, htm, hos, hot⟩
  clear hts htm hos hot
  unfold csubD
  rw [hW]
  refine WP.seq (wp_movw fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r1) (by decide) (by omega_arith) fun s₄ u₄ =>
    wp_ptr (d := .r8) (by decide) (by omega_arith) fun s₅ u₅ => wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₆ =>
    WP.block_nil ?_)
  have R : Rest dclob s t := ((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
    ((u₃.rest (by decide)).trans (u₄.rest (by decide)))).trans (u₅.rest (by decide))).trans (u₆.rest (by decide))
  have mt : t.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have I0 : DiffInv s base size src M.tmp M.mo 0 t := by
    refine ⟨hs.of_rest R (by decide), R, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]; decide
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
      exact (BitVec.add_zero _).symm
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
      exact (BitVec.add_zero _).symm
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]; rfl
    · rw [mt]; exact Outside.refl _ _ _ _
  have p1 : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 M.mo := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  have p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 M.mo + BitVec.ofNat 32 (4 * W) := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, Offset.add_add]
  clear u₁ u₂ u₃ u₄ u₅ u₆ mt R
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 M.mo) (step := 4) (k := W)
    (DiffInv s base size src M.tmp M.mo) (by decide) hW0 (by omega_arith) (fun _ _ _ h f => h.fupd f) I0 p1 p9 ?_
    fun u I _ => ?_)
  · -- The difference.
    intro j hj u I pu p9u
    have e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
    have x0 : w32 u.mem base (src + 8 * j) = w32 s.mem base (src + 8 * j) :=
      I.out.w32 (by have := hsep.ts; omega_arith) (by omega_arith)
    have x1 : w32 u.mem base (src + 8 * j + 4) = w32 s.mem base (src + 8 * j + 4) :=
      I.out.w32 (by have := hsep.ts; omega_arith) (by omega_arith)
    have xm : w32 u.mem base (M.mo + 4 * j) = w32 s.mem base (M.mo + 4 * j) :=
      I.out.w32 (by have := hsep.tm; omega_arith) (by omega_arith)
    have d0 : w32 s.mem base (src + 8 * j) < 2 ^ 16 := by
      have := hd (2 * j) (by omega_arith); rwa [show src + 4 * (2 * j) = src + 8 * j by omega_arith] at this
    have d1 : w32 s.mem base (src + 8 * j + 4) < 2 ^ 16 := by
      have := hd (2 * j + 1) (by omega_arith); rwa [show src + 4 * (2 * j + 1) = src + 8 * j + 4 by omega_arith] at this
    refine WP.mono (diffBody_ok I.ws I.r6 I.r3 (at_ptr I.r10 e12) (at_ptr pu e12) (at_ptr I.r8 e12)
      (by omega_arith) (by omega_arith) (by omega_arith) (by rw [x0]; exact d0) (by rw [x1]; exact d1))
      fun v ⟨w, mv, cv, ev, p10, p1v, p8, p6, Rv, wv⟩ => ?_
    have ev' := ev
    rw [x0, x1, xm] at ev'
    have O' : Outside base (M.tmp + 4 * j) 4 u.mem v.mem := by
      rw [mv]; exact writeW32_outside _ _ _ (by omega_arith)
    refine ⟨⟨wv, I.rest.trans (Rv.mono (by decide)), by rw [p6]; exact I.r6, cv, by rw [p10]; exact ptr_step I.r10,
      by rw [p8]; exact ptr_step I.r8, ?_, ?_⟩, by rw [p1v]; exact ptr_step pu, by rw [Rv.gpr _ (by decide)]; exact p9u⟩
    · rw [val32_succ, val32_succ, show 2 * (j + 1) = 2 * j + 2 by omega_arith, dval_two,
        O'.val32 (by omega_arith) (by omega_arith), mv, w32_write_self, show 32 * (j + 1) = 32 + 32 * j by omega_arith, Nat.pow_add]
      exact diff_step I.val ev'
    · rw [mv]
      exact (I.out.mono (by omega_arith) (by omega_arith)).trans ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  -- The mask, then the selection.
  have e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
  have xt : w32 u.mem base (src + 8 * W) = w32 s.mem base (src + 8 * W) :=
    I.out.w32 (by have := hsep.ts; omega_arith) (by omega_arith)
  have hX : dval s.mem base src (2 * W) < 2 ^ (32 * W) := by
    rw [show 32 * W = 16 * (2 * W) by omega_arith]; exact dval_lt (hd.mono (by omega_arith))
  have hsplit : dval s.mem base src (2 * W + 1) = dval s.mem base src (2 * W) +
      w32 s.mem base (src + 8 * W) * 2 ^ (32 * W) := by
    rw [dval, show 16 * (2 * W) = 32 * W by omega_arith, show src + 4 * (2 * W) = src + 8 * W by omega_arith]
  have hmP : m < 2 ^ (32 * W) := by rw [← hm]; exact val32_lt _ _ _ _
  have ht1 : w32 s.mem base (src + 8 * W) ≤ 1 := by
    rcases Nat.lt_or_ge (w32 s.mem base (src + 8 * W)) 2 with h | h
    · omega_arith
    · have := Nat.mul_le_mul_right (2 ^ (32 * W)) h; omega_arith
  obtain ⟨hct, hres⟩ := csub_arith (X := dval s.mem base src (2 * W)) (t := w32 s.mem base (src + 8 * W))
    (T := val32 u.mem base M.tmp W) (c := (u.gpr .r3).toNat) hmP hm0
    (by rw [hsplit, Nat.mul_comm (w32 _ _ _)] at hV; exact hV) ht1 I.r3 (val32_lt _ _ _ _)
    (by have := I.val; rw [hm, Nat.mul_comm (u.gpr .r3).toNat] at this; exact this)
  refine WP.seq (wp_ldr (by decide) (I.ws.ea (d := 0) (at_ptr I.r10 e12) (by omega_arith))
    (I.ws.read (d := src + 8 * W + 0) (n := 4) (by omega_arith)) fun u₁ v₁ =>
    wp_dp (op2_reg _ _) fun u₂ v₂ => wp_mov (op2_imm (by decide)) fun u₃ v₃ => wp_dp (op2_reg _ _) fun u₄ v₄ =>
    WP.block_nil ?_)
  have b4 : u₄.gpr .r3 = if decide ((u.gpr .r3).toNat + w32 s.mem base (src + 8 * W) = 1) = true then
      BitVec.allOnes 32 else 0 := by
    simp only [v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte, dpVal, Nat.add_zero, decide_eq_true_eq]
    have hsum : (u.gpr .r3 + u.mem.readW (off base (src + 8 * W)) 32).toNat =
        (u.gpr .r3).toNat + w32 s.mem base (src + 8 * W) := by
      have ew : (u.mem.readW (off base (src + 8 * W)) 32).toNat = w32 s.mem base (src + 8 * W) := xt
      rw [toNat_add_lt (by rw [ew]; omega_arith), ew]
    rcases (by omega_arith : (u.gpr .r3).toNat + w32 s.mem base (src + 8 * W) = 0 ∨
        (u.gpr .r3).toNat + w32 s.mem base (src + 8 * W) = 1) with h | h
    · rw [ite_eq_right (by omega_arith)]
      have : u.gpr .r3 + u.mem.readW (off base (src + 8 * W)) 32 = 0 :=
        BitVec.eq_of_toNat_eq (by rw [hsum, h]; rfl)
      rw [this]; rfl
    · rw [ite_eq_left h]
      have : u.gpr .r3 + u.mem.readW (off base (src + 8 * W)) 32 = 1 :=
        BitVec.eq_of_toNat_eq (by rw [hsum, h]; rfl)
      rw [this]; rfl
  have w₄ : Ws u₄ base size := (((I.ws.of_upd v₁ (by decide)).of_upd v₂ (by decide)).of_upd v₃ (by decide)).of_upd v₄
    (by decide)
  have R₄ : Rest dclob s u₄ := I.rest.trans (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
    ((v₃.rest (by decide)).trans (v₄.rest (by decide))))
  have m₄ : u₄.mem = u.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  clear v₁ v₂ v₃ v₄
  refine WP.seq (wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₁ u₁ => wp_ptr (d := .r8) (by decide) (by omega_arith)
    fun s₂ u₂ => wp_ptr (d := .r1) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r9) (by decide) (by omega_arith)
    fun t u₆ => WP.block_nil ?_)
  have e12₄ : u₄.gpr .r12 = s.gpr .r12 := R₄.gpr _ (by decide)
  have R : Rest dclob s t := R₄.trans ((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
    (u₃.rest (by decide))).trans (u₆.rest (by decide)))
  have mt : t.mem = u.mem := by rw [u₆.mem, u₃.mem, u₂.mem, u₁.mem, m₄]
  have J0 : SelInv s base size src M.tmp o (decide ((u.gpr .r3).toNat + w32 s.mem base (src + 8 * W) = 1)) u.mem 0 t := by
    refine ⟨hs.of_rest R (by decide), R, ?_, ?_, ?_, fun i hi => absurd hi (by omega_arith), ?_⟩
    · simp only [u₆.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact b4
    · simp only [u₆.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12₄]
      exact (BitVec.add_zero _).symm
    · simp only [u₆.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12₄]
      exact (BitVec.add_zero _).symm
    · rw [mt]; exact Outside.refl _ _ _ _
  have p8 : t.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 M.tmp := by
    simp only [u₆.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12₄]
  have p9' : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 M.tmp + BitVec.ofNat 32 (4 * W) := by
    simp only [u₆.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12₄, Offset.add_add]
  clear u₁ u₂ u₃ u₆
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 M.tmp) (step := 4) (k := W)
    (SelInv s base size src M.tmp o _ u.mem) (by decide) hW0 (by omega_arith) (fun _ _ _ h f => h.fupd f) J0 p8 p9' ?_
    fun v J _ => ⟨J.ws, ?_, ?_, J.rest⟩
  · intro j hj v J pv p9v
    have e12 : v.gpr .r12 = s.gpr .r12 := J.rest.gpr _ (by decide)
    have y0 : w32 v.mem base (src + 8 * j) = w32 s.mem base (src + 8 * j) := by
      rw [J.out.w32 (by have := hsep.os; omega_arith) (by omega_arith), I.out.w32 (by have := hsep.ts; omega_arith) (by omega_arith)]
    have y1 : w32 v.mem base (src + 8 * j + 4) = w32 s.mem base (src + 8 * j + 4) := by
      rw [J.out.w32 (by have := hsep.os; omega_arith) (by omega_arith), I.out.w32 (by have := hsep.ts; omega_arith) (by omega_arith)]
    have yt : w32 v.mem base (M.tmp + 4 * j) = w32 u.mem base (M.tmp + 4 * j) :=
      J.out.w32 (by have := hsep.ot; omega_arith) (by omega_arith)
    have d0 : w32 s.mem base (src + 8 * j) < 2 ^ 16 := by
      have := hd (2 * j) (by omega_arith); rwa [show src + 4 * (2 * j) = src + 8 * j by omega_arith] at this
    have d1 : w32 s.mem base (src + 8 * j + 4) < 2 ^ 16 := by
      have := hd (2 * j + 1) (by omega_arith); rwa [show src + 4 * (2 * j + 1) = src + 8 * j + 4 by omega_arith] at this
    refine WP.mono (selBody_ok J.ws _ J.r3 (at_ptr J.r10 e12) (at_ptr pv e12) (at_ptr J.r1 e12)
      (by omega_arith) (by omega_arith) (by omega_arith) (by rw [y0]; exact d0) (by rw [y1]; exact d1))
      fun v' ⟨w, mv, ev, p10, p8v, p1v, p3, Rv, wv⟩ => ?_
    refine ⟨⟨wv, J.rest.trans (Rv.mono (by decide)), by rw [p3]; exact J.r3, by rw [p10]; exact ptr_step J.r10,
      by rw [p1v]; exact ptr_step J.r1, ?_, ?_⟩, by rw [p8v]; exact ptr_step pv, by rw [Rv.gpr _ (by decide)]; exact p9v⟩
    · intro i hi
      rw [mv]
      rcases Nat.lt_or_ge i j with h | h
      · rw [w32_write_lt (by omega_arith) (by omega_arith)]; exact J.words i h
      · rw [show i = j by omega_arith, w32_write_self, ev, yt, y0, y1]
    · rw [mv]
      exact (J.out.mono (by omega_arith) (by omega_arith)).trans ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · by_cases hb : (u.gpr .r3).toNat + w32 s.mem base (src + 8 * W) = 1
    · rw [val32_move (m := u.mem) (d := M.tmp) fun i hi => ?_, hsplit]
      · rw [ite_eq_left hb] at hres; rw [Nat.mul_comm (w32 _ _ _), ← hres]
      · have := J.words i hi
        simp only [hb, decide_true, ↓reduceIte] at this
        exact this
    · rw [val32_pack (m := s.mem) (src := src) fun i hi => ?_, hsplit]
      · rw [ite_eq_right hb] at hres; rw [Nat.mul_comm (w32 _ _ _), ← hres]
      · have := J.words i hi
        simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte] at this
        exact this
  · exact (Outs.of_outside I.out (by simp)).trans (Outs.of_outside J.out (by simp))

end VG.Proof.Mont.Arm.Dyn
