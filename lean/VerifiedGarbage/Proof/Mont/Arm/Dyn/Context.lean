module

public import VerifiedGarbage.Impl.Mont.Arm.Context
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Add
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Mont.Arm.Dyn.Mul`, which this module and modules that import it used -/

section

/-! ### `Mont.Arm.Dyn.Csub`, which this module and modules that import it used -/

section

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
  obtain hd := hdig_lt (s.gpr .r7).toNat h
  simp only [diffDigitD]
  refine wp_ldr (by omega_arith) (hs.ea h10 (by omega_arith)) (hs.read hK) fun s₁ u₁ => ?_
  refine wp_half hh (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have r6 : (VG.Proof.X25519.Arm.mask16).toNat = 2 ^ 16 - 1 := rfl
  have hx' : (s.mem.readW (off base (K + 4 * h)) 32).toNat < 2 ^ 16 := hx
  have ew : w32 s.mem base (K + 4 * h) = (s.mem.readW (off base (K + 4 * h)) 32).toNat := rfl
  obtain v5 : (s₅.gpr .r5).toNat = w32 s.mem base (K + 4 * h) + (2 ^ 16 - 1 - hdig (s.gpr .r7).toNat h) +
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
  obtain hw' : w + 2 ^ 32 * c' + Mw + 1 = x0 + 2 ^ 16 * x1 + 2 ^ 32 + c := by omega_arith
  obtain e : P * (w + 2 ^ 32 * c' + Mw + 1) = P * (x0 + 2 ^ 16 * x1 + 2 ^ 32 + c) := by rw [hw']
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
  obtain w₁ := hs.of_upd v₁ (by decide)
  obtain e10 : u₁.gpr .r10 = u₁.gpr .r12 + BitVec.ofNat 32 S := by
    rw [v₁.other .r10 (by decide), v₁.other .r12 (by decide)]; exact h10
  refine VG.Proof.X25519.Arm.WP.append (diffDigitD_ok w₁ (h := 0) (by decide)
    (by rw [v₁.other .r6 (by decide)]; exact h6) e10 (by omega_arith) (by rw [v₁.mem, Nat.mul_zero, Nat.add_zero]; exact hx0)
    (by rw [v₁.other .r3 (by decide)]; exact hc)) fun u₂ ⟨E₂, C₂, M₂, R₂⟩ => ?_
  refine wp_dp (op2_reg _ _) fun u₃ v₃ => ?_
  obtain w₃ := (w₁.of_rest R₂ (by decide)).of_upd v₃ (by decide)
  rw [v₁.mem, v₁.other .r3 (by decide), Nat.mul_zero, Nat.add_zero] at E₂
  obtain hd0 := hdig_lt (u₁.gpr .r7).toNat 0
  obtain hd1 := hdig_lt (u₁.gpr .r7).toNat 1
  obtain b₂ : (u₂.gpr .r5).toNat < 2 ^ 17 := by rw [E₂]; omega_arith
  refine VG.Proof.X25519.Arm.WP.append (diffDigitD_ok w₃ (K := S) (h := 1) (by decide)
    (by rw [v₃.other .r6 (by decide), R₂.gpr _ (by decide), v₁.other .r6 (by decide)]; exact h6)
    (by rw [v₃.other .r10 (by decide), v₃.other .r12 (by decide), R₂.gpr _ (by decide), R₂.gpr _ (by decide)]; exact e10)
    (by omega_arith) (by rw [v₃.mem, M₂, v₁.mem, Nat.mul_one]; exact hx1)
    (by rw [v₃.other .r3 (by decide), C₂]; omega_arith)) fun u₄ ⟨E₄, C₄, M₄, R₄⟩ => ?_
  refine wp_dp (op2_lsl (by decide)) fun u₅ v₅ => ?_
  obtain w₅ := (w₃.of_rest R₄ (by decide)).of_upd v₅ (by decide)
  obtain e8 : u₅.gpr .r8 = u₅.gpr .r12 + BitVec.ofNat 32 Tp := by
    simp only [v₅.get, v₃.get, v₁.get, R₄.gpr .r8 (by decide), R₄.gpr .r12 (by decide), R₂.gpr .r8 (by decide),
      R₂.gpr .r12 (by decide), reduceCtorEq, ↓reduceIte]; exact h8
  refine wp_str (by decide) (w₅.ea (d := 0) e8 (by omega_arith)) (w₅.write (d := Tp + 0) (n := 4) (by omega_arith))
    fun u₆ m₆ => wp_bump (by decide) fun u₇ v₇ => wp_bump (by decide) fun u₈ v₈ => wp_bump (by decide) fun u₉ v₉ =>
      WP.block_nil ?_
  rw [v₃.mem, M₂, v₁.mem, v₃.other .r3 (by decide), C₂, Nat.mul_one] at E₄
  rw [v₃.other .r7 (by decide), R₂.gpr .r7 (by decide)] at E₄
  obtain r2₄ : (u₄.gpr .r2).toNat = (u₂.gpr .r5).toNat % 2 ^ 16 := by
    rw [R₄.gpr _ (by decide), v₃.gpr, dpVal, toNat_and_r6 (by rw [R₂.gpr _ (by decide), v₁.other .r6 (by decide)]; exact h6)]
  obtain pk : (u₅.gpr .r2).toNat = (u₂.gpr .r5).toNat % 2 ^ 16 + (u₄.gpr .r5).toNat % 2 ^ 16 * 2 ^ 16 := by
    rw [v₅.gpr, dpVal, pack_toNat _ _ (by rw [r2₄]; omega_arith), r2₄]
  obtain r7₁ : (u₁.gpr .r7).toNat = w32 u.mem base Mo := by rw [v₁.gpr, Nat.add_zero]
  obtain hm := word_digits (w32 u.mem base Mo) (BitVec.isLt _)
  rw [r7₁] at E₂ E₄ hd0 hd1
  obtain c₉ : u₉.gpr .r3 = u₄.gpr .r3 := by
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
  obtain w₁ := hs.of_upd v₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (d := 4) (by rw [v₁.other .r10 (by decide), v₁.other .r12 (by decide)]; exact h10)
    (by omega_arith)) (w₁.read (d := S + 4) (n := 4) (by omega_arith)) fun u₂ v₂ => ?_
  obtain w₂ := w₁.of_upd v₂ (by decide)
  refine wp_dp (op2_lsl (by decide)) fun u₃ v₃ => ?_
  obtain w₃ := w₂.of_upd v₃ (by decide)
  refine wp_ldr (by decide) (w₃.ea (d := 0) (K := Tp) (by simp only [v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact h8)
    (by omega_arith)) (w₃.read (d := Tp + 0) (n := 4) (by omega_arith)) fun u₄ v₄ => ?_
  refine wp_dp (op2_reg _ _) fun u₅ v₅ => wp_dp (op2_reg _ _) fun u₆ v₆ => wp_dp (op2_reg _ _) fun u₇ v₇ => ?_
  obtain w₇ := (((w₃.of_upd v₄ (by decide)).of_upd v₅ (by decide)).of_upd v₆ (by decide)).of_upd v₇ (by decide)
  refine wp_str (by decide) (w₇.ea (d := 0) (K := O)
    (by simp only [v₇.get, v₆.get, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact h1)
    (by omega_arith)) (w₇.write (d := O + 0) (n := 4) (by omega_arith))
    fun u₈ m₈ => wp_bump (by decide) fun u₉ v₉ => wp_bump (by decide) fun u₁₀ v₁₀ => wp_bump (by decide) fun u₁₁ v₁₁ =>
      WP.block_nil ?_
  obtain m₇ : u₇.mem = u.mem := by rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  obtain r5₃ : (u₃.gpr .r5).toNat = w32 u.mem base S + w32 u.mem base (S + 4) * 2 ^ 16 := by
    rw [v₃.gpr, dpVal, v₂.other .r5 (by decide), pack_toNat _ _ (by rw [v₁.gpr, Nat.add_zero]; exact hx0), v₁.gpr,
      v₂.gpr, v₁.mem, Nat.add_zero, Nat.mod_eq_of_lt hx1]
  obtain val : u₇.gpr .r5 = if b then u.mem.readW (off base Tp) 32 else u₃.gpr .r5 := by
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
  obtain hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega_arith
  rw [hD] at hsrc h16 hts hos hd hV ⊢
  rw [hW] at ho htmp hmo h16t h16m hts htm hos hot hm ⊢
  obtain hW0 : 0 < W := by rw [← hW]; simp only [Impl.Mont.Arm.words]; omega_arith
  obtain hsep : CsubSep W src o M.tmp M.mo := ⟨hts, htm, hos, hot⟩
  clear hts htm hos hot
  unfold csubD
  rw [hW]
  refine WP.seq (wp_movw fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r1) (by decide) (by omega_arith) fun s₄ u₄ =>
    wp_ptr (d := .r8) (by decide) (by omega_arith) fun s₅ u₅ => wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₆ =>
    WP.block_nil ?_)
  obtain R : Rest dclob s t := ((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
    ((u₃.rest (by decide)).trans (u₄.rest (by decide)))).trans (u₅.rest (by decide))).trans (u₆.rest (by decide))
  obtain mt : t.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain I0 : DiffInv s base size src M.tmp M.mo 0 t := by
    refine ⟨hs.of_rest R (by decide), R, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]; decide
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
      exact (BitVec.add_zero _).symm
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
      exact (BitVec.add_zero _).symm
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]; rfl
    · rw [mt]; exact Outside.refl _ _ _ _
  obtain p1 : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 M.mo := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 M.mo + BitVec.ofNat 32 (4 * W) := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, Offset.add_add]
  clear u₁ u₂ u₃ u₄ u₅ u₆ mt R
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 M.mo) (step := 4) (k := W)
    (DiffInv s base size src M.tmp M.mo) (by decide) hW0 (by omega_arith) (fun _ _ _ h f => h.fupd f) I0 p1 p9 ?_
    fun u I _ => ?_)
  · -- The difference.
    intro j hj u I pu p9u
    obtain e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
    obtain x0 : w32 u.mem base (src + 8 * j) = w32 s.mem base (src + 8 * j) :=
      I.out.w32 (by have := hsep.ts; omega_arith) (by omega_arith)
    obtain x1 : w32 u.mem base (src + 8 * j + 4) = w32 s.mem base (src + 8 * j + 4) :=
      I.out.w32 (by have := hsep.ts; omega_arith) (by omega_arith)
    obtain xm : w32 u.mem base (M.mo + 4 * j) = w32 s.mem base (M.mo + 4 * j) :=
      I.out.w32 (by have := hsep.tm; omega_arith) (by omega_arith)
    obtain d0 : w32 s.mem base (src + 8 * j) < 2 ^ 16 := by
      have := hd (2 * j) (by omega_arith); rwa [show src + 4 * (2 * j) = src + 8 * j by omega_arith] at this
    obtain d1 : w32 s.mem base (src + 8 * j + 4) < 2 ^ 16 := by
      have := hd (2 * j + 1) (by omega_arith); rwa [show src + 4 * (2 * j + 1) = src + 8 * j + 4 by omega_arith] at this
    refine WP.mono (diffBody_ok I.ws I.r6 I.r3 (at_ptr I.r10 e12) (at_ptr pu e12) (at_ptr I.r8 e12)
      (by omega_arith) (by omega_arith) (by omega_arith) (by rw [x0]; exact d0) (by rw [x1]; exact d1))
      fun v ⟨w, mv, cv, ev, p10, p1v, p8, p6, Rv, wv⟩ => ?_
    have ev' := ev
    rw [x0, x1, xm] at ev'
    obtain O' : Outside base (M.tmp + 4 * j) 4 u.mem v.mem := by
      rw [mv]; exact writeW32_outside _ _ _ (by omega_arith)
    refine ⟨⟨wv, I.rest.trans (Rv.mono (by decide)), by rw [p6]; exact I.r6, cv, by rw [p10]; exact ptr_step I.r10,
      by rw [p8]; exact ptr_step I.r8, ?_, ?_⟩, by rw [p1v]; exact ptr_step pu, by rw [Rv.gpr _ (by decide)]; exact p9u⟩
    · rw [val32_succ, val32_succ, show 2 * (j + 1) = 2 * j + 2 by omega_arith, dval_two,
        O'.val32 (by omega_arith) (by omega_arith), mv, w32_write_self, show 32 * (j + 1) = 32 + 32 * j by omega_arith, Nat.pow_add]
      exact diff_step I.val ev'
    · rw [mv]
      exact (I.out.mono (by omega_arith) (by omega_arith)).trans ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  -- The mask, then the selection.
  obtain e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
  obtain xt : w32 u.mem base (src + 8 * W) = w32 s.mem base (src + 8 * W) :=
    I.out.w32 (by have := hsep.ts; omega_arith) (by omega_arith)
  obtain hX : dval s.mem base src (2 * W) < 2 ^ (32 * W) := by
    rw [show 32 * W = 16 * (2 * W) by omega_arith]; exact dval_lt (hd.mono (by omega_arith))
  obtain hsplit : dval s.mem base src (2 * W + 1) = dval s.mem base src (2 * W) +
      w32 s.mem base (src + 8 * W) * 2 ^ (32 * W) := by
    rw [dval, show 16 * (2 * W) = 32 * W by omega_arith, show src + 4 * (2 * W) = src + 8 * W by omega_arith]
  obtain hmP : m < 2 ^ (32 * W) := by rw [← hm]; exact val32_lt _ _ _ _
  obtain ht1 : w32 s.mem base (src + 8 * W) ≤ 1 := by
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
  obtain b4 : u₄.gpr .r3 = if decide ((u.gpr .r3).toNat + w32 s.mem base (src + 8 * W) = 1) = true then
      BitVec.allOnes 32 else 0 := by
    simp only [v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte, dpVal, Nat.add_zero, decide_eq_true_eq]
    obtain hsum : (u.gpr .r3 + u.mem.readW (off base (src + 8 * W)) 32).toNat =
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
  obtain w₄ : Ws u₄ base size := (((I.ws.of_upd v₁ (by decide)).of_upd v₂ (by decide)).of_upd v₃ (by decide)).of_upd v₄
    (by decide)
  obtain R₄ : Rest dclob s u₄ := I.rest.trans (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
    ((v₃.rest (by decide)).trans (v₄.rest (by decide))))
  obtain m₄ : u₄.mem = u.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  clear v₁ v₂ v₃ v₄
  refine WP.seq (wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₁ u₁ => wp_ptr (d := .r8) (by decide) (by omega_arith)
    fun s₂ u₂ => wp_ptr (d := .r1) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r9) (by decide) (by omega_arith)
    fun t u₆ => WP.block_nil ?_)
  obtain e12₄ : u₄.gpr .r12 = s.gpr .r12 := R₄.gpr _ (by decide)
  obtain R : Rest dclob s t := R₄.trans ((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
    (u₃.rest (by decide))).trans (u₆.rest (by decide)))
  obtain mt : t.mem = u.mem := by rw [u₆.mem, u₃.mem, u₂.mem, u₁.mem, m₄]
  obtain J0 : SelInv s base size src M.tmp o (decide ((u.gpr .r3).toNat + w32 s.mem base (src + 8 * W) = 1)) u.mem 0 t := by
    refine ⟨hs.of_rest R (by decide), R, ?_, ?_, ?_, fun i hi => absurd hi (by omega_arith), ?_⟩
    · simp only [u₆.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact b4
    · simp only [u₆.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12₄]
      exact (BitVec.add_zero _).symm
    · simp only [u₆.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12₄]
      exact (BitVec.add_zero _).symm
    · rw [mt]; exact Outside.refl _ _ _ _
  obtain p8 : t.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 M.tmp := by
    simp only [u₆.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12₄]
  obtain p9' : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 M.tmp + BitVec.ofNat 32 (4 * W) := by
    simp only [u₆.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12₄, Offset.add_add]
  clear u₁ u₂ u₃ u₆
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 M.tmp) (step := 4) (k := W)
    (SelInv s base size src M.tmp o _ u.mem) (by decide) hW0 (by omega_arith) (fun _ _ _ h f => h.fupd f) J0 p8 p9' ?_
    fun v J _ => ⟨J.ws, ?_, ?_, J.rest⟩
  · intro j hj v J pv p9v
    obtain e12 : v.gpr .r12 = s.gpr .r12 := J.rest.gpr _ (by decide)
    obtain y0 : w32 v.mem base (src + 8 * j) = w32 s.mem base (src + 8 * j) := by
      rw [J.out.w32 (by have := hsep.os; omega_arith) (by omega_arith), I.out.w32 (by have := hsep.ts; omega_arith) (by omega_arith)]
    obtain y1 : w32 v.mem base (src + 8 * j + 4) = w32 s.mem base (src + 8 * j + 4) := by
      rw [J.out.w32 (by have := hsep.os; omega_arith) (by omega_arith), I.out.w32 (by have := hsep.ts; omega_arith) (by omega_arith)]
    obtain yt : w32 v.mem base (M.tmp + 4 * j) = w32 u.mem base (M.tmp + 4 * j) :=
      J.out.w32 (by have := hsep.ot; omega_arith) (by omega_arith)
    obtain d0 : w32 s.mem base (src + 8 * j) < 2 ^ 16 := by
      have := hd (2 * j) (by omega_arith); rwa [show src + 4 * (2 * j) = src + 8 * j by omega_arith] at this
    obtain d1 : w32 s.mem base (src + 8 * j + 4) < 2 ^ 16 := by
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

end

end

/-! ### `Mont.Arm.Dyn.MulRow`, which only this module used -/

section

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: a row of the multiplication

`mulRowD M src` adds `r2 · [src]` (`D` digits, `r2` a digit) to the window of
`D + 2` digits at `r0` (`mulRowD_ok`), when the sum fits it: a word of
`[src]` (two digits, `macD_ok`) an iteration, the carry then into the
window's last two digits.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_mul wp_movw op2_imm op2_reg op2_lsr
  dpVal toNat_add_lt toNat_shr)

/-- Digit `h` of the word in `r7`, times `r2`, plus the carry `r3`, added to
the window's digit at `[r10 + 4h]`. -/
theorem macD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {K h : Nat} (hh : h < 2)
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (h10 : s.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 K)
    (hK : K + 4 * h + 4 ≤ size) (hu : (s.gpr .r2).toNat < 2 ^ 16) (hc : (s.gpr .r3).toNat < 2 ^ 16)
    (ht : w32 s.mem base (K + 4 * h) < 2 ^ 16) :
    WP isa (.block (macD h)) s fun u =>
      u.mem = s.mem.writeW (off base (K + 4 * h)) (BitVec.ofNat 32
        (((s.gpr .r2).toNat * hdig (s.gpr .r7).toNat h + w32 s.mem base (K + 4 * h) + (s.gpr .r3).toNat) % 2 ^ 16)) ∧
      (u.gpr .r3).toNat =
        ((s.gpr .r2).toNat * hdig (s.gpr .r7).toNat h + w32 s.mem base (K + 4 * h) + (s.gpr .r3).toNat) / 2 ^ 16 ∧
      Rest [.r3, .r4, .r5] s u := by
  obtain hd := hdig_lt (s.gpr .r7).toNat h
  obtain hx := step_lt hu hd ht hc
  obtain hmul : (s.gpr .r2).toNat * hdig (s.gpr .r7).toNat h < 2 ^ 32 := by
    have := Nat.mul_le_mul (Nat.le_of_lt_succ hu) (Nat.le_of_lt_succ hd); omega_using [hx]
  simp only [macD]
  refine wp_half hh h6 fun s₁ u₁ => ?_
  obtain w₁ := hs.of_upd u₁ (by decide)
  obtain e10 : s₁.gpr .r10 = s₁.gpr .r12 + BitVec.ofNat 32 K := by
    simp only [u₁.get, reduceCtorEq, ↓reduceIte]; exact h10
  refine wp_ldr (by omega_using [hh]) (w₁.ea e10 (by omega_using [hK])) (w₁.read (by omega_using [hK])) fun s₂ u₂ => wp_mla fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  obtain w₅ := (((w₁.of_upd u₂ (by decide)).of_upd u₃ (by decide)).of_upd u₄ (by decide)).of_upd u₅ (by decide)
  refine wp_str (by omega_using [hh]) (w₅.ea (by simp only [u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]; exact e10)
    (by omega_using [hK])) (w₅.write (by omega_using [hK])) fun s₆ m₆ => wp_mov (op2_lsr (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have ew : w32 s.mem base (K + 4 * h) = (s.mem.readW (off base (K + 4 * h)) 32).toNat := rfl
  obtain v4 : (s₄.gpr .r5).toNat =
      (s.gpr .r2).toNat * hdig (s.gpr .r7).toNat h + w32 s.mem base (K + 4 * h) + (s.gpr .r3).toNat := by
    simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, dpVal]
    rw [u₁.mem]
    obtain hm : (s.gpr .r2 * BitVec.ofNat 32 (hdig (s.gpr .r7).toNat h)).toNat =
        (s.gpr .r2).toNat * hdig (s.gpr .r7).toNat h := by
      rw [BitVec.toNat_mul, toNat_ofNat_dig, Nat.mod_eq_of_lt hmul]
    refine (toNat_add_eq (toNat_add_eq hm rfl ?_) rfl ?_).trans ?_ <;> omega_arith
  refine ⟨?_, ?_, ?_⟩
  · rw [u₇.mem, m₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    congr 1
    rw [u₅.gpr, dpVal, show s₄.gpr .r6 = VG.Proof.X25519.Arm.mask16 by
      simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h6]
    exact and_mask_ofNat v4
  · rw [u₇.gpr, toNat_shr, m₆.gpr, u₅.other .r5 (by decide), v4]
  · exact (((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))).trans
      ((u₅.rest (by simp)).trans ((m₆.rest _).trans (u₇.rest (by simp))))

/-- The low digits of a number, two on. -/
theorem pval_two (m : Mem) (base : Addr) (d j : Nat) :
    pval m base d (2 * j + 2) = pval m base d (2 * j) + hdig (w32 m base (d + 4 * j)) 0 * 2 ^ (32 * j) +
      hdig (w32 m base (d + 4 * j)) 1 * (2 ^ 16 * 2 ^ (32 * j)) := by
  rw [show 2 * j + 2 = 2 * j + 1 + 1 by omega_using [], pval, pval]
  simp only [pdig, show (2 * j + 1) / 2 = j by omega_using [], show 2 * j / 2 = j by omega_using [], show (2 * j + 1) % 2 = 1 by omega_using [],
    show 2 * j % 2 = 0 by omega_using [], show 16 * (2 * j) = 32 * j by omega_using [], show 16 * (2 * j + 1) = 16 + 32 * j by omega_using [],
    Nat.pow_add]

/-- An iteration of a row, as numbers. -/
theorem mac_step {D c T V P u d0 d1 t0 t1 : Nat} (h : D + c * P = T + u * V) :
    D + (u * d0 + t0 + c) % 2 ^ 16 * P + (u * d1 + t1 + (u * d0 + t0 + c) / 2 ^ 16) % 2 ^ 16 * (2 ^ 16 * P) +
      (u * d1 + t1 + (u * d0 + t0 + c) / 2 ^ 16) / 2 ^ 16 * (2 ^ 32 * P) =
      T + t0 * P + t1 * (2 ^ 16 * P) + u * (V + d0 * P + d1 * (2 ^ 16 * P)) := by
  obtain e0 := Nat.mod_add_div (u * d0 + t0 + c) (2 ^ 16)
  obtain e1 := Nat.mod_add_div (u * d1 + t1 + (u * d0 + t0 + c) / 2 ^ 16) (2 ^ 16)
  generalize (u * d0 + t0 + c) % 2 ^ 16 = a0 at *
  generalize (u * d0 + t0 + c) / 2 ^ 16 = q0 at *
  generalize (u * d1 + t1 + q0) % 2 ^ 16 = a1 at *
  generalize (u * d1 + t1 + q0) / 2 ^ 16 = q1 at *
  grind

/-- The carry into the window's last two digits, as numbers. -/
theorem carry_val {Du c P Ds V tD tD1 : Nat} (h : Du + c * P = Ds + V) :
    Du + (tD + c) % 2 ^ 16 * P + (tD1 + (tD + c) / 2 ^ 16) * (2 ^ 16 * P) =
      Ds + tD * P + tD1 * (2 ^ 16 * P) + V := by
  obtain e := Nat.mod_add_div (tD + c) (2 ^ 16)
  generalize (tD + c) % 2 ^ 16 = a at *
  generalize (tD + c) / 2 ^ 16 = q at *
  grind

/-- The invariant of a row's loop after `j` words of `[src]`. -/
structure RowInv (s : State) (base : Addr) (size w src : Nat) (j : Nat) (u : State) : Prop where
  ws : Ws u base size
  rest : Rest [.r3, .r4, .r5, .r7, .r8, .r9, .r10] s u
  r3 : (u.gpr .r3).toNat < 2 ^ 16
  r10 : u.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 w + BitVec.ofNat 32 (8 * j)
  val : dval u.mem base w (2 * j) + (u.gpr .r3).toNat * 2 ^ (32 * j) =
    dval s.mem base w (2 * j) + (s.gpr .r2).toNat * pval s.mem base src (2 * j)
  digs : Digs u.mem base w (2 * j)
  out : Outside base w (8 * j) s.mem u.mem

theorem RowInv.fupd {s : State} {base : Addr} {size w src j : Nat} {u u' : State}
    (h : RowInv s base size w src j u) (f : Fupd u u') : RowInv s base size w src j u' :=
  ⟨h.ws.of_fupd f, h.rest.trans (f.rest _), by rw [f.gpr]; exact h.r3, by rw [f.gpr]; exact h.r10,
    by rw [f.gpr, f.mem]; exact h.val, by rw [f.mem]; exact h.digs, by rw [f.mem]; exact h.out⟩

/-- The window at `r0 = r12 + w` `+= r2 · [src]` (`D` digits), when the sum
fits its `D + 2` digits. -/
theorem mulRowD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {src w : Nat}
    (hn : 0 < M.n) (h0 : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 w) (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (hu : (s.gpr .r2).toNat < 2 ^ 16) (hsrc : src + 4 * words M ≤ size) (h16 : src + 4 * words M < 2 ^ 16)
    (hw : w + 4 * digits M + 8 ≤ size) (hsep : src + 4 * words M ≤ w ∨ w + 4 * digits M + 8 ≤ src)
    (hd : Digs s.mem base w (digits M + 2))
    (hlt : dval s.mem base w (digits M + 2) + (s.gpr .r2).toNat * pval s.mem base src (digits M) <
      2 ^ (16 * (digits M + 2))) :
    WP isa (mulRowD M src) s fun u => Ws u base size ∧ Outside base w (4 * digits M + 8) s.mem u.mem ∧
      dval u.mem base w (digits M + 2) = dval s.mem base w (digits M + 2) +
        (s.gpr .r2).toNat * pval s.mem base src (digits M) ∧
      Digs u.mem base w (digits M + 2) ∧ Rest [.r3, .r4, .r5, .r7, .r8, .r9, .r10] s u := by
  have hnw := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  obtain hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega_arith
  rw [hD] at hw hsep hd hlt ⊢
  rw [hW] at hsrc h16 hsep
  obtain hW0 : 0 < W := by rw [← hW]; simp only [Impl.Mont.Arm.words]; omega_arith
  unfold mulRowD
  rw [hW]
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_ptr (d := .r8) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₄ =>
    WP.block_nil ?_)
  obtain R : Rest [.r3, .r4, .r5, .r7, .r8, .r9, .r10] s t := (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
    (u₃.rest (by decide))).trans (u₄.rest (by decide))
  obtain mt : t.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain I0 : RowInv s base size w src 0 t := by
    refine ⟨hs.of_rest R (by decide), R, ?_, ?_, ?_, fun i hi => absurd hi (by omega_arith), ?_⟩
    · simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; decide
    · simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, h0]
      exact (BitVec.add_zero _).symm
    · simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; rfl
    · rw [mt]; exact Outside.refl _ _ _ _
  obtain p8 : t.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 src := by
    simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 src + BitVec.ofNat 32 (4 * W) := by
    simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, Offset.add_add]
  clear u₁ u₂ u₃ u₄ mt R
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 src) (step := 4) (k := W)
    (RowInv s base size w src) (by decide) hW0 (by omega_arith) (fun _ _ _ h f => h.fupd f) I0 p8 p9 ?_
    fun u I _ => ?_)
  · intro j hj u I pu p9u
    simp only [List.cons_append, List.append_assoc, List.nil_append]
    obtain e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
    obtain xs : w32 u.mem base (src + 4 * j + 0) = w32 s.mem base (src + 4 * j) := I.out.w32 (by omega_arith) (by omega_arith)
    obtain x0 : w32 u.mem base (w + 8 * j) = w32 s.mem base (w + 8 * j) := I.out.w32 (by omega_arith) (by omega_arith)
    obtain x1 : w32 u.mem base (w + 8 * j + 4) = w32 s.mem base (w + 8 * j + 4) := I.out.w32 (by omega_arith) (by omega_arith)
    obtain t0 : w32 s.mem base (w + 8 * j) < 2 ^ 16 := by
      have := hd (2 * j) (by omega_arith); rwa [show w + 4 * (2 * j) = w + 8 * j by omega_arith] at this
    obtain t1 : w32 s.mem base (w + 8 * j + 4) < 2 ^ 16 := by
      have := hd (2 * j + 1) (by omega_arith); rwa [show w + 4 * (2 * j + 1) = w + 8 * j + 4 by omega_arith] at this
    obtain g6 : u.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [I.rest.gpr _ (by decide)]; exact h6
    obtain g2 : u.gpr .r2 = s.gpr .r2 := I.rest.gpr _ (by decide)
    refine wp_ldr (by decide) (I.ws.ea (K := src + 4 * j) (at_ptr pu e12) (by omega_arith))
      (I.ws.read (d := src + 4 * j + 0) (n := 4) (by omega_arith)) fun u₁ v₁ => ?_
    obtain w₁ := I.ws.of_upd v₁ (by decide)
    obtain e10 : u₁.gpr .r10 = u₁.gpr .r12 + BitVec.ofNat 32 (w + 8 * j) := by
      rw [v₁.other .r10 (by decide), v₁.other .r12 (by decide)]; exact at_ptr I.r10 e12
    refine VG.Proof.X25519.Arm.WP.append (macD_ok w₁ (h := 0) (by decide) (by rw [v₁.other .r6 (by decide)]; exact g6)
      e10 (by omega_arith) (by rw [v₁.other .r2 (by decide), g2]; exact hu) (by rw [v₁.other .r3 (by decide)]; exact I.r3)
      (by rw [v₁.mem, Nat.mul_zero, Nat.add_zero, x0]; exact t0)) fun u₂ ⟨M₂, C₂, R₂⟩ => ?_
    obtain w₂ := w₁.of_rest R₂ (by decide)
    obtain hd0 := hdig_lt (u₁.gpr .r7).toNat 0
    have := I.r3
    obtain hx := step_lt (u := (u₁.gpr .r2).toNat) (by rw [v₁.other .r2 (by decide), g2]; exact hu) hd0
      (t := w32 u₁.mem base (w + 8 * j + 4 * 0)) (by rw [v₁.mem, Nat.mul_zero, Nat.add_zero, x0]; exact t0)
      (c := (u₁.gpr .r3).toNat) (by rw [v₁.other .r3 (by decide)]; exact I.r3)
    refine VG.Proof.X25519.Arm.WP.append (macD_ok w₂ (K := w + 8 * j) (h := 1) (by decide)
      (by rw [R₂.gpr _ (by decide), v₁.other .r6 (by decide)]; exact g6)
      (by rw [R₂.gpr _ (by decide), R₂.gpr _ (by decide)]; exact e10) (by omega_arith)
      (by rw [R₂.gpr _ (by decide), v₁.other .r2 (by decide), g2]; exact hu)
      (by rw [C₂]; exact Nat.div_lt_of_lt_mul (by omega_arith))
      (by rw [M₂, Nat.mul_one, w32_write_ne (size := size) hnw (by omega_arith) (by omega_arith) (by omega_arith), v₁.mem, x1]; exact t1))
      fun u₃ ⟨M₃, C₃, R₃⟩ => ?_
    refine wp_bump (by decide) fun u₄ v₄ => wp_bump (by decide) fun u₅ v₅ => WP.block_nil ?_
    rw [R₂.gpr .r2 (by decide), R₂.gpr .r7 (by decide), C₂, M₂, Nat.mul_one, Nat.mul_zero, Nat.add_zero,
      w32_write_ne (size := size) hnw (by omega_arith) (by omega_arith) (by omega_arith)] at M₃ C₃
    obtain r7₁ : (u₁.gpr .r7).toNat = w32 s.mem base (src + 4 * j) := by rw [v₁.gpr]; exact xs
    rw [v₁.mem, x0, x1, v₁.other .r2 (by decide), v₁.other .r3 (by decide), g2, r7₁] at M₃ C₃
    obtain m₅ : u₅.mem = u₃.mem := by rw [v₅.mem, v₄.mem]
    obtain ⟨d0, d1, O⟩ := pair_writes (m := u.mem) (base := base) (Q := w + 8 * j) (by omega_arith) _ _
    rw [← M₃] at d0 d1 O
    rw [toNat_ofNat_mod16] at d0 d1
    obtain c₅ : u₅.gpr .r3 = u₃.gpr .r3 := by simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
    obtain hy0 := hdig_lt (w32 s.mem base (src + 4 * j)) 0
    obtain hy1 := hdig_lt (w32 s.mem base (src + 4 * j)) 1
    obtain hx2 := step_lt hu hy1 t1 (c := ((s.gpr .r2).toNat * hdig (w32 s.mem base (src + 4 * j)) 0 +
      w32 s.mem base (w + 8 * j) + (u.gpr .r3).toNat) / 2 ^ 16) (Nat.div_lt_of_lt_mul (by
        have := step_lt hu hy0 t0 I.r3; omega_arith))
    refine ⟨⟨(((w₂.of_rest R₃ (by decide)).of_upd v₄ (by decide)).of_upd v₅ (by decide)),
      I.rest.trans ((((v₁.rest (by decide)).trans (R₂.mono (by decide))).trans (R₃.mono (by decide))).trans
        ((v₄.rest (by decide)).trans (v₅.rest (by decide)))), ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [c₅, C₃]; exact Nat.div_lt_of_lt_mul (by omega_arith)
    · simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
      rw [R₃.gpr .r10 (by decide), R₂.gpr .r10 (by decide), v₁.other .r10 (by decide)]
      rw [I.r10, Offset.add_add, Offset.add_add, Offset.add_add, show 8 * (j + 1) = 8 * j + 8 by omega_arith]
    · rw [m₅, c₅, C₃, show 2 * (j + 1) = 2 * j + 2 by omega_arith, dval_two, d0, d1, O.dval (by omega_arith) (by omega_arith),
        show 32 * (j + 1) = 32 + 32 * j by omega_arith, Nat.pow_add, pval_two, dval_two]
      exact mac_step I.val
    · rw [m₅, show 2 * (j + 1) = 2 * j + 2 by omega_arith]
      exact digs_two (by omega_arith) O I.digs (by rw [d0]; omega_arith) (by rw [d1]; omega_arith)
    · rw [m₅]
      exact (I.out.mono (by omega_arith) (by omega_arith)).trans (O.mono (by omega_arith) (by omega_arith))
    · simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
      rw [R₃.gpr .r8 (by decide), R₂.gpr .r8 (by decide), v₁.other .r8 (by decide)]
      exact ptr_step pu
    · simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
      rw [R₃.gpr .r9 (by decide), R₂.gpr .r9 (by decide), v₁.other .r9 (by decide)]
      exact p9u
  · have e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
    obtain e10 : u.gpr .r10 = u.gpr .r12 + BitVec.ofNat 32 (w + 8 * W) := at_ptr I.r10 e12
    obtain x0 : w32 u.mem base (w + 8 * W) = w32 s.mem base (w + 8 * W) := I.out.w32 (by omega_arith) (by omega_arith)
    obtain x1 : w32 u.mem base (w + 8 * W + 4) = w32 s.mem base (w + 8 * W + 4) := I.out.w32 (by omega_arith) (by omega_arith)
    obtain t0 : w32 s.mem base (w + 8 * W) < 2 ^ 16 := by
      have := hd (2 * W) (by omega_arith); rwa [show w + 4 * (2 * W) = w + 8 * W by omega_arith] at this
    obtain t1 : w32 s.mem base (w + 8 * W + 4) < 2 ^ 16 := by
      have := hd (2 * W + 1) (by omega_arith); rwa [show w + 4 * (2 * W + 1) = w + 8 * W + 4 by omega_arith] at this
    obtain g6 : u.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [I.rest.gpr _ (by decide)]; exact h6
    have := I.r3
    refine wp_ldr (by decide) (I.ws.ea (d := 0) e10 (by omega_arith)) (I.ws.read (d := w + 8 * W + 0) (n := 4) (by omega_arith))
      fun u₁ v₁ => wp_dp (op2_reg _ _) fun u₂ v₂ => wp_dp (op2_reg _ _) fun u₃ v₃ => ?_
    obtain w₃ := ((I.ws.of_upd v₁ (by decide)).of_upd v₂ (by decide)).of_upd v₃ (by decide)
    obtain e10₃ : u₃.gpr .r10 = u₃.gpr .r12 + BitVec.ofNat 32 (w + 8 * W) := by
      simp only [v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact e10
    refine wp_str (by decide) (w₃.ea (d := 0) e10₃ (by omega_arith)) (w₃.write (d := w + 8 * W + 0) (n := 4) (by omega_arith))
      fun u₄ m₄ => ?_
    obtain w₄ := w₃.of_mupd m₄
    obtain e10₄ : u₄.gpr .r10 = u₄.gpr .r12 + BitVec.ofNat 32 (w + 8 * W) := by rw [m₄.gpr]; exact e10₃
    refine wp_ldr (by decide) (w₄.ea (d := 4) e10₄ (by omega_arith)) (w₄.read (d := w + 8 * W + 4) (n := 4) (by omega_arith))
      fun u₅ v₅ => wp_dp (op2_lsr (by decide)) fun u₆ v₆ => ?_
    obtain w₆ := (w₄.of_upd v₅ (by decide)).of_upd v₆ (by decide)
    refine wp_str (by decide) (w₆.ea (d := 4)
      (by simp only [v₆.get, v₅.get, m₄.gpr, reduceCtorEq, ↓reduceIte]; exact e10₃) (by omega_arith))
      (w₆.write (d := w + 8 * W + 4) (n := 4) (by omega_arith)) fun u₇ m₇ => WP.block_nil ?_
    have ew : (u.mem.readW (off base (w + 8 * W)) 32).toNat = w32 s.mem base (w + 8 * W) := x0
    obtain r5₂ : (u₂.gpr .r5).toNat = w32 s.mem base (w + 8 * W) + (u.gpr .r3).toNat := by
      simp only [v₂.get, v₁.get, reduceCtorEq, ↓reduceIte, dpVal, Nat.add_zero]
      rw [toNat_add_lt (by rw [ew]; omega_arith), ew]
    obtain st₁ : u₄.mem = u.mem.writeW (off base (w + 8 * W))
        (BitVec.ofNat 32 ((w32 s.mem base (w + 8 * W) + (u.gpr .r3).toNat) % 2 ^ 16)) := by
      rw [m₄.mem, v₃.mem, v₂.mem, v₁.mem, Nat.add_zero]
      congr 1
      rw [v₃.gpr, dpVal, show u₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 by
        simp only [v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact g6]
      exact and_mask_ofNat r5₂
    obtain r7₆ : (u₆.gpr .r7).toNat = w32 s.mem base (w + 8 * W + 4) +
        (w32 s.mem base (w + 8 * W) + (u.gpr .r3).toNat) / 2 ^ 16 := by
      obtain r55 : u₅.gpr .r5 = u₂.gpr .r5 := by simp only [v₅.get, m₄.gpr, v₃.get, reduceCtorEq, ↓reduceIte]
      obtain r75 : (u₅.gpr .r7).toNat = w32 s.mem base (w + 8 * W + 4) := by
        rw [v₅.gpr, st₁, ← x1]
        exact w32_write_ne (size := size) hnw (by omega_arith) (by omega_arith) (by omega_arith) _
      rw [v₆.gpr, dpVal, toNat_add_lt (by rw [r75, toNat_shr, r55, r5₂]; omega_arith), r75, toNat_shr, r55, r5₂]
    obtain st : u₇.mem = (u.mem.writeW (off base (w + 8 * W))
        (BitVec.ofNat 32 ((w32 s.mem base (w + 8 * W) + (u.gpr .r3).toNat) % 2 ^ 16))).writeW
          (off base (w + 8 * W + 4)) (u₆.gpr .r7) := by
      rw [m₇.mem, v₆.mem, v₅.mem, st₁]
    obtain ⟨d0, d1, O⟩ := pair_writes (m := u.mem) (base := base) (Q := w + 8 * W) (by omega_arith) _ _
    rw [← st] at d0 d1 O
    rw [toNat_ofNat_mod16] at d0
    rw [r7₆] at d1
    obtain V : dval u₇.mem base w (2 * W + 2) = dval s.mem base w (2 * W + 2) +
        (s.gpr .r2).toNat * pval s.mem base src (2 * W) := by
      rw [dval_two, d0, d1, O.dval (by omega_arith) (by omega_arith), dval_two, carry_val I.val]
    obtain hP : 0 < 2 ^ (32 * W) := Nat.two_pow_pos _
    refine ⟨w₆.of_mupd m₇, ?_, V, ?_, ?_⟩
    · exact (I.out.mono (by omega_arith) (by omega_arith)).trans (O.mono (by omega_arith) (by omega_arith))
    · refine digs_two (by omega_arith) O I.digs (by rw [d0]; omega_arith) ?_
      have hl := hlt
      rw [← V, dval_two, show 16 * (2 * W + 2) = 32 + 32 * W by omega_arith, Nat.pow_add] at hl
      have : w32 u₇.mem base (w + 8 * W + 4) * 2 ^ 16 * 2 ^ (32 * W) < 2 ^ 32 * 2 ^ (32 * W) := by
        rw [Nat.mul_assoc]; omega_arith
      have := Nat.lt_of_mul_lt_mul_right this
      omega_arith
    · exact I.rest.trans ((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
        ((v₃.rest (by decide)).trans (m₄.rest _))).trans
        (((v₅.rest (by decide)).trans (v₆.rest (by decide))).trans (m₇.rest _)))

end VG.Proof.Mont.Arm.Dyn

end

end

/-! ### `Mont.Arm.Dyn.DigitRow`, which only this module used -/

section

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
  obtain hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega_arith
  rw [hD] at hw_le hsb hsmo hsinv hd hT htop ⊢
  rw [hW] at hb_le hmo_le hb16 hmo16 hsb hsmo hm hB ⊢
  obtain hm0 : m < 2 ^ (16 * (2 * W)) := by
    rw [← hm, show 16 * (2 * W) = 32 * W by omega_arith]; exact val32_lt _ _ _ _
  unfold digitRowD
  -- u
  refine WP.seq (wp_ldr (by decide) (hs.ea (d := 0) h1 (by omega_arith)) (hs.read (d := Pa + 0) (n := 4) (by omega_arith))
    fun s₁ u₁ => wp_half hh (by rw [u₁.other .r6 (by decide)]; exact h6) fun s₂ u₂ => WP.block_nil ?_)
  obtain hU := hdig_lt (w32 s.mem base Pa) h
  obtain K₂ : Rest [.r0, .r2, .r3, .r4, .r5, .r7, .r8, .r9, .r10] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  obtain w₂ := hs.of_rest K₂ (by decide)
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  obtain r2₂ : (s₂.gpr .r2).toNat = hdig (w32 s.mem base Pa) h := by
    rw [u₂.gpr, u₁.gpr, Nat.add_zero, toNat_ofNat_dig]
  obtain hBp : pval s.mem base b (2 * W) = val32 s.mem base b W := pval_words _ _ _ _
  obtain hlt₁ : dval s₂.mem base w (2 * W + 2) + (s₂.gpr .r2).toNat * pval s₂.mem base b (2 * W) <
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
  obtain K₃ := K₂.trans (R₃.mono (by decide))
  obtain e0 : s₃.gpr .r0 = s₃.gpr .r12 + BitVec.ofNat 32 w := by
    rw [R₃.gpr .r0 (by decide), R₃.gpr .r12 (by decide)]
    simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h0
  refine WP.seq (wp_ldr (by decide) (w₃.ea (d := 0) e0 (by omega_arith)) (w₃.read (d := w + 0) (n := 4) (by omega_arith))
    fun s₄ u₄ => ?_)
  obtain w₄ := w₃.of_upd u₄ (by decide)
  refine wp_ldr hinv16 (w₄.ea12 (by omega_arith)) (w₄.read (d := inv) (n := 4) hinv_le)
    fun s₅ u₅ => wp_mul fun s₆ u₆ => wp_dp (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  obtain w₇ := (((w₄.of_upd u₅ (by decide)).of_upd u₆ (by decide))).of_upd u₇ (by decide)
  obtain m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain mi : w32 s₃.mem base inv = w32 s.mem base inv := O₃.w32 (by omega_arith) (by omega_arith)
  obtain ht0 : w32 s₃.mem base w = (dval s.mem base w (2 * W + 2) + hdig (w32 s.mem base Pa) h * val32 s.mem base b W) %
      2 ^ 16 := by rw [← V₃, dval_low D₃]
  obtain g6₃ : s₃.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₃.gpr _ (by decide)]; exact h6
  obtain hq : (s₇.gpr .r2).toNat = w32 s₃.mem base w * w32 s.mem base inv % 2 ^ 16 := by
    simp only [u₇.get, u₆.get, u₅.get, u₄.get, reduceCtorEq, ↓reduceIte, dpVal]
    rw [toNat_and_r6 g6₃, BitVec.toNat_mul, Nat.add_zero, u₄.mem, ← mi,
      Nat.mod_mod_of_dvd _ (show 2 ^ 16 ∣ 2 ^ 32 from ⟨2 ^ 16, by decide⟩)]
  obtain hq16 : (s₇.gpr .r2).toNat < 2 ^ 16 := by rw [hq]; exact Nat.mod_lt _ (by decide)
  obtain hmo₃ : val32 s₃.mem base M.mo W = m := by rw [O₃.val32 (by omega_arith) (by omega_arith)]; exact hm
  obtain hMp : pval s₇.mem base M.mo (2 * W) = m := by rw [m₇, pval_words, hmo₃]
  obtain hlt₂ : dval s₇.mem base w (2 * W + 2) + (s₇.gpr .r2).toNat * pval s₇.mem base M.mo (2 * W) <
      2 ^ (16 * (2 * W + 2)) := by
    rw [hMp, m₇, V₃, show 16 * (2 * W + 2) = 16 * (2 * W) + 32 by omega_arith, Nat.pow_add]
    have := row_lt hT hU hB hq16
    have : 2 * 2 ^ 16 * m < 2 * 2 ^ 16 * 2 ^ (16 * (2 * W)) := Nat.mul_lt_mul_of_pos_left hm0 (by omega_arith)
    omega_arith
  obtain e0₇ : s₇.gpr .r0 = s₇.gpr .r12 + BitVec.ofNat 32 w := by
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
  obtain hz : w32 s₈.mem base w = 0 := by
    rw [← dval_low D₈, V₈, V₃, show (T1 + q * m) % 2 ^ 16 = (T1 % 2 ^ 16 + q * m) % 2 ^ 16 by omega_arith, hq, ← ht0]
    rw [← mi]
    have := hinv; rw [← mi] at this
    exact mont_low16 _ _ _ this
  obtain htop' : w32 s₈.mem base (w + 4 * (2 * W + 2)) = 0 := by
    rw [O₈.w32 (by omega_arith) (by omega_arith), O₃.w32 (by omega_arith) (by omega_arith)]; exact htop
  obtain hsh := dval_shift hz htop'
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

end

end


/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the multiplication

`mul umaal M inv acc o a b` writes `[o] = [a] [b] R⁻¹ mod m` (`mul_ok`), on
digits (`mulD_ok`) or on words (`mulU_ok`). On digits, the accumulator is
cleared, each word of `[a]` takes the window two digits up (`rowD_ok`, by the
invariant `MulInv`), and the window, below `2m`, is reduced into `[o]`. On
words, `-m⁻¹ mod 2³²` comes from `-m⁻¹ mod 2¹⁶` by a Newton step (`inv32`),
each word of `[a]` takes the window a word up (`rowU_ok`, by `MulInvU`: two
rows of `umaal`, `mulRowU_ok`), and the window is reduced by a subtraction on
words (`csubU_ok`) and a selection (`selectW_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_mul wp_movw wp_cmp op2_imm op2_reg
  op2_lsr dpVal toNat_add_lt toNat_shr)

variable {umaal : Bool}

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
  obtain hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega_using []
  obtain ⟨acc_le, a_le, b_le, mo_le, tmp_le, o_le, inv_le, acc16, a16, b16, mo16, tmp16, o16, inv16, sa, sb, smo,
    sinv, stmp, so, tmo, ot⟩ := hL
  simp only [accLen, hD, hW] at acc_le a_le b_le mo_le tmp_le o_le acc16 a16 b16 mo16 tmp16 sa sb smo sinv stmp so tmo ot
  obtain e12 : t.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
  obtain hmt : val32 t.mem base M.mo W = m := by rw [I.out.val32 (by omega_using [smo]) (by omega_using [mo_le, hnw])]; exact hm
  obtain hit : w32 t.mem base inv = w32 s.mem base inv := I.out.w32 (by omega_using [sinv]) (by omega_using [inv_le, hnw])
  obtain hbt : val32 t.mem base b W = val32 s.mem base b W := I.out.val32 (by omega_using [sb]) (by omega_using [b_le, hnw])
  obtain hat : w32 t.mem base (a + 4 * k) = w32 s.mem base (a + 4 * k) := I.out.w32 (by omega_using [sa, hk]) (by omega_using [a_le, hk, hnw])
  obtain L0 : RowLayD M size (acc + 8 * k) b inv :=
    ⟨by rw [hW]; omega_using [b_le], by rw [hW]; omega_using [mo_le], by rw [hD]; omega_using [acc_le, hk], inv_le, by rw [hW]; omega_using [b16], by rw [hW]; omega_using [mo16], inv16,
      by rw [hW, hD]; omega_using [sb, hk], by rw [hW, hD]; omega_using [smo, hk], by rw [hD]; omega_using [sinv, hk]⟩
  obtain top0 : w32 t.mem base (acc + 8 * k + 4 * (2 * W + 2)) = 0 := by
    have := I.zeros (2 * k + 2 * W + 2) (by omega_using [hk]) (by omega_using [hk])
    rwa [show acc + 4 * (2 * k + 2 * W + 2) = acc + 8 * k + 4 * (2 * W + 2) by omega_using []] at this
  unfold rowD
  refine WP.seq (WP.mono (digitRowD_ok I.ws (m := m) (h := 0) hn L0 (by decide) I.r6 (at_ptr' I.r0 e12) (at_ptr' I.r1 e12)
    (by omega_using [a_le, hk]) (by rw [hW]; exact hmt) (by rw [hit]; exact hinv) (by rw [hW, hbt]; exact hB) (by rw [hD]; exact I.digs)
    (by rw [hD]; exact I.lt) (by rw [hD]; exact top0)) fun t₁ ⟨w₁, p0₁, O₁, D₁, ⟨q₀, hq₀, V₁⟩, R₁⟩ => ?_)
  simp only [hD, hW] at V₁ O₁ D₁
  rw [hat, hbt] at V₁
  obtain hU0 := hdig_lt (w32 s.mem base (a + 4 * k)) 0
  obtain hU1 := hdig_lt (w32 s.mem base (a + 4 * k)) 1
  obtain lt₁ : dval t₁.mem base (acc + 8 * k + 4) (2 * W + 2) < 2 * m := by
    have := row_lt I.lt hU0 hB hq₀; omega_using [V₁, this]
  obtain e12₁ : t₁.gpr .r12 = s.gpr .r12 := by rw [R₁.gpr _ (by decide)]; exact e12
  obtain L1 : RowLayD M size (acc + 8 * k + 4) b inv :=
    ⟨by rw [hW]; omega_using [b_le], by rw [hW]; omega_using [mo_le], by rw [hD]; omega_using [acc_le, hk], inv_le, by rw [hW]; omega_using [b16], by rw [hW]; omega_using [mo16], inv16,
      by rw [hW, hD]; omega_using [sb, hk], by rw [hW, hD]; omega_using [smo, hk], by rw [hD]; omega_using [sinv, hk]⟩
  obtain top1 : w32 t₁.mem base (acc + 8 * k + 4 + 4 * (2 * W + 2)) = 0 := by
    rw [O₁.w32 (by omega_using []) (by omega_using [acc_le, hk, hnw])]
    have := I.zeros (2 * k + 2 * W + 3) (by omega_using [hk]) (by omega_using [hk])
    rwa [show acc + 4 * (2 * k + 2 * W + 3) = acc + 8 * k + 4 + 4 * (2 * W + 2) by omega_using []] at this
  obtain hm₁ : val32 t₁.mem base M.mo W = m := by rw [O₁.val32 (by omega_using [smo, hk]) (by omega_using [mo_le, hnw])]; exact hmt
  obtain hi₁ : w32 t₁.mem base inv = w32 s.mem base inv := by rw [O₁.w32 (by omega_using [sinv, hk]) (by omega_using [inv_le, hnw])]; exact hit
  obtain hb₁ : val32 t₁.mem base b W = val32 s.mem base b W := by rw [O₁.val32 (by omega_using [sb, hk]) (by omega_using [b_le, hnw])]; exact hbt
  obtain ha₁ : w32 t₁.mem base (a + 4 * k) = w32 s.mem base (a + 4 * k) :=
    (O₁.w32 (d := a + 4 * k) (by omega_using [sa, hk]) (by omega_using [a_le, hk, hnw])).trans hat
  refine WP.seq (WP.mono (digitRowD_ok w₁ (m := m) (h := 1) hn L1 (by decide)
    (by rw [R₁.gpr _ (by decide)]; exact I.r6)
    (by rw [p0₁, e12₁, I.r0, Offset.add_add, Nat.add_assoc]) (Pa := a + 4 * k)
    (by rw [R₁.gpr _ (by decide), e12₁]; exact I.r1)
    (by omega_using [a_le, hk]) (by rw [hW]; exact hm₁) (by rw [hi₁]; exact hinv) (by rw [hW, hb₁]; exact hB) (by rw [hD]; exact D₁)
    (by rw [hD]; exact lt₁) (by rw [hD]; exact top1)) fun t₂ ⟨w₂, p0₂, O₂, D₂, ⟨q₁, hq₁, V₂⟩, R₂⟩ => ?_)
  simp only [hD, hW] at V₂ O₂ D₂
  rw [ha₁, hb₁] at V₂
  obtain lt₂ : dval t₂.mem base (acc + 8 * k + 4 + 4) (2 * W + 2) < 2 * m := by
    have := row_lt lt₁ hU1 hB hq₁; omega_using [V₂, this]
  obtain e12₂ : t₂.gpr .r12 = s.gpr .r12 := by rw [R₂.gpr _ (by decide)]; exact e12₁
  refine wp_bump (by decide) fun t₃ v₃ => wp_ptr (d := .r9) (by decide) (by rw [hW]; omega_using [a16]) fun t₄ v₄ =>
    wp_cmp (op2_reg _ _) fun t₅ f₅ z₅ => WP.block_nil ?_
  obtain r1₄ : t₄.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) + BitVec.ofNat 32 4 := by
    rw [v₄.other .r1 (by decide), v₃.gpr, R₂.gpr .r1 (by decide), R₁.gpr .r1 (by decide), I.r1]
  obtain r9₄ : t₄.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) + BitVec.ofNat 32 (4 * W - 4 * k) := by
    rw [v₄.gpr, v₃.other .r12 (by decide), e12₂, hW, Offset.add_add]
    rw [show a + 4 * k + (4 * W - 4 * k) = a + 4 * W by omega_using [hk]]
  obtain m₅ : t₅.mem = t₂.mem := by rw [f₅.mem, v₄.mem, v₃.mem]
  obtain R₅ : Rest dclob s t₅ := ((I.rest.trans (R₁.mono (by decide))).trans (R₂.mono (by decide))).trans
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
  | k + 1, h => by rw [dval, dval_zeros fun j hj => h j (by omega_using [hj]), h k (by omega_using []), Nat.zero_mul]

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
  obtain hW0 : 0 < W := by rw [← hW]; simp only [Impl.Mont.Arm.words]; omega_using [hn]
  refine WP.loop (M := isa)
    (fun n t' => ∃ k, n = W - k ∧ k < W ∧ MulInv s base size acc a b m W k t') ?_ W t ⟨0, rfl, hW0, h0⟩
  rintro n t' ⟨k, rfl, hk, I⟩
  refine WP.mono (rowD_ok hn hW hL hm hinv hB hk I) fun u ⟨I', hz⟩ => ?_
  by_cases hk1 : k + 1 = W
  · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hk1]; rfl, hk1 ▸ I'⟩
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hk1]; rfl, W - (k + 1), by omega_using [hk],
      k + 1, rfl, by omega_using [hk, hk1], I'⟩

/-- `[o] = [a] [b] R⁻¹ mod m` (`R = 2^(32W)`), with `m'` at `[inv]`, through
the accumulator at `[acc]` and the temporary area. `[o]` may be `[a]` or `[b]`. -/
theorem mulD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {inv acc o a b m : Nat}
    (hn : 0 < M.n) (hL : MulLayD M size inv acc o a b)
    (hm : val32 s.mem base M.mo (words M) = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b (words M) < m) :
    WP isa (Dynamic.mulD M inv acc o a b) s fun t => Ws t base size ∧
      val32 t.mem base o (words M) < m ∧
      val32 t.mem base o (words M) * 2 ^ (32 * words M) % m =
        val32 s.mem base a (words M) * val32 s.mem base b (words M) % m ∧
      Outs base [(o, 4 * words M), (M.tmp, 4 * words M), (acc, 4 * (4 * words M + 2))] s.mem t.mem ∧
      Rest dclob s t := by
  have hnw := hs.nowrap
  obtain hm0 := m_pos_of_inv16 hinv
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  obtain hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega_using []
  obtain hW0 : 0 < W := by rw [← hW]; simp only [Impl.Mont.Arm.words]; omega_using [hn]
  have hL' := hL
  obtain ⟨acc_le, a_le, b_le, mo_le, tmp_le, o_le, inv_le, acc16, a16, b16, mo16, tmp16, o16, inv16, sa, sb, smo,
    sinv, stmp, so, tmo, ot⟩ := hL'
  simp only [accLen, hD, hW] at acc_le a_le b_le mo_le tmp_le o_le acc16 a16 b16 mo16 tmp16 sa sb smo sinv stmp so tmo ot
  rw [hW] at hm hB ⊢
  unfold Dynamic.mulD
  rw [hD]
  refine WP.seq (WP.mono (zeros_ok hs (o := acc) (k := 2 * (2 * W) + 2) (by omega_using [])
    (by omega_using [acc_le]) (by omega_using [acc16])) fun t₀ ⟨w₀, Z₀, O₀, R₀⟩ => ?_)
  refine WP.seq (wp_movw fun t₁ u₁ => wp_ptr (d := .r0) (by decide) (by omega_using [acc16]) fun t₂ u₂ =>
    wp_ptr (d := .r1) (by decide) (by omega_using [a16]) fun t₃ u₃ => WP.block_nil ?_)
  obtain e12 : t₀.gpr .r12 = s.gpr .r12 := R₀.gpr _ (by decide)
  obtain I0 : MulInv s base size acc a b m W 0 t₃ := by
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
  obtain hmu : val32 u.mem base M.mo W = m := by
    rw [I.out.val32 (by omega_using [smo]) (by omega_using [mo_le, hnw])]; exact hm
  obtain hmP : m < 2 ^ (32 * W) := by rw [← hm]; exact val32_lt _ _ _ _
  obtain hsplit : dval u.mem base (acc + 8 * W) (2 * W + 2) = dval u.mem base (acc + 8 * W) (2 * W + 1) +
      w32 u.mem base (acc + 8 * W + 4 * (2 * W + 1)) * 2 ^ (16 * (2 * W + 1)) := by rw [dval]
  obtain htop : w32 u.mem base (acc + 8 * W + 4 * (2 * W + 1)) = 0 := by
    have hl := I.lt
    rw [hsplit, show 16 * (2 * W + 1) = 32 * W + 16 by omega_using [], Nat.pow_add] at hl
    rcases Nat.eq_zero_or_pos (w32 u.mem base (acc + 8 * W + 4 * (2 * W + 1))) with h | h
    · exact h
    · have : 2 ^ (32 * W) * 2 ^ 16 ≤ w32 u.mem base (acc + 8 * W + 4 * (2 * W + 1)) * (2 ^ (32 * W) * 2 ^ 16) :=
        Nat.le_mul_of_pos_left _ h
      omega_using [hl, hmP, this]
  obtain hT : dval u.mem base (acc + 8 * W) (2 * W + 1) = dval u.mem base (acc + 8 * W) (2 * W + 2) := by
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

/-! ## Selecting words

`selectW k src tmp o` writes `[o] = [tmp]` where the mask `r3` is all ones,
else `[src]` (`selectW_ok`); `[o]` may be `[src]`. -/

theorem selectW_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k src tmp o : Nat} (b : Bool)
    (h3 : s.gpr .r3 = if b then BitVec.allOnes 32 else 0) (hk : 0 < k)
    (hsrc : src + 4 * k ≤ size) (htmp : tmp + 4 * k ≤ size) (hoz : o + 4 * k ≤ size)
    (h16s : src + 4 * k < 2 ^ 16) (h16t : tmp < 2 ^ 16) (h16o : o < 2 ^ 16)
    (hos : o = src ∨ o + 4 * k ≤ src ∨ src + 4 * k ≤ o) (hot : o + 4 * k ≤ tmp ∨ tmp + 4 * k ≤ o) :
    WP isa (selectW k src tmp o) s fun t => Ws t base size ∧
      (∀ j < k, w32 t.mem base (o + 4 * j) =
        if b then w32 s.mem base (tmp + 4 * j) else w32 s.mem base (src + 4 * j)) ∧
      Outside base o (4 * k) s.mem t.mem ∧ Rest [.r1, .r5, .r7, .r8, .r9, .r10] s t := by
  have hn := hs.nowrap
  unfold selectW
  refine WP.seq (wp_ptr (d := .r10) (by decide) (by omega_using [h16s]) fun s₁ u₁ =>
    wp_ptr (d := .r8) (by decide) (by omega_using [h16t]) fun s₂ u₂ =>
    wp_ptr (d := .r1) (by decide) (by omega_using [h16o]) fun s₃ u₃ =>
    wp_ptr (d := .r9) (by decide) (by omega_using [h16s]) fun t u₄ => WP.block_nil ?_)
  obtain R : Rest [.r1, .r5, .r7, .r8, .r9, .r10] s t :=
    (((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans (u₃.rest (by simp))).trans (u₄.rest (by simp))
  obtain wt : Ws t base size := hs.of_rest R (by decide)
  obtain mt : t.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 src := by simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p8 : t.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 tmp := by simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p1 : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 o := by simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (src + 4 * k) := by simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain r3 : t.gpr .r3 = s.gpr .r3 := R.gpr _ (by decide)
  clear u₁ u₂ u₃ u₄
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 src) (step := 4) (k := k)
    (fun j u => Ws u base size ∧ Rest [.r1, .r5, .r7, .r8, .r9, .r10] s u ∧
      u.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 tmp + BitVec.ofNat 32 (4 * j) ∧
      u.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 o + BitVec.ofNat 32 (4 * j) ∧
      (∀ i < j, w32 u.mem base (o + 4 * i) =
        if b then w32 s.mem base (tmp + 4 * i) else w32 s.mem base (src + 4 * i)) ∧
      Outside base o (4 * j) s.mem u.mem)
    (by decide) hk (by omega_using [h16s]) (fun j u u' ⟨a, c, d, e, f, g⟩ F => ⟨a.of_fupd F, c.trans (F.rest _),
      by rw [F.gpr]; exact d, by rw [F.gpr]; exact e, by rw [F.mem]; exact f, by rw [F.mem]; exact g⟩)
    ⟨wt, R, by rw [p8]; exact (BitVec.add_zero _).symm, by rw [p1]; exact (BitVec.add_zero _).symm,
      fun i hi => absurd hi (Nat.not_lt_zero _), by rw [mt]; exact Outside.refl _ _ _ _⟩
    p10 (by rw [p9, Offset.add_add]) ?_ fun u ⟨a, c, _, _, f, g⟩ _ => ⟨a, f, g, c⟩
  intro j hj u ⟨wu, Ru, p8u, p1u, Vu, Ou⟩ pu p9u
  obtain e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
  obtain r3u : u.gpr .r3 = s.gpr .r3 := Ru.gpr _ (by decide)
  -- The words read are not yet written.
  obtain xs : w32 u.mem base (src + 4 * j + 0) = w32 s.mem base (src + 4 * j) :=
    Ou.w32 (by omega_using [hos, hj]) (by omega_using [h16s, hj])
  obtain xt : w32 u.mem base (tmp + 4 * j + 0) = w32 s.mem base (tmp + 4 * j) :=
    Ou.w32 (by omega_using [hot, hj]) (by omega_using [h16s, h16t, hj])
  refine wp_ldr (by decide) (wu.ea (K := src + 4 * j) (at_ptr pu e12) (by omega_using [hsrc, hj])) (wu.read (d := src + 4 * j + 0) (n := 4) (by omega_using [hsrc, hj]))
    fun u₁ v₁ => ?_
  obtain w₁ := wu.of_upd v₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (K := tmp + 4 * j) (at_ptr (by rw [v₁.other .r8 (by decide)]; exact p8u)
    (by rw [v₁.other .r12 (by decide)]; exact e12)) (by omega_using [htmp, hj])) (w₁.read (d := tmp + 4 * j + 0) (n := 4) (by omega_using [htmp, hj]))
    fun u₂ v₂ => wp_dp (op2_reg _ _) fun u₃ v₃ => wp_dp (op2_reg _ _) fun u₄ v₄ => wp_dp (op2_reg _ _) fun u₅ v₅ => ?_
  obtain w₅ : Ws u₅ base size := (((w₁.of_upd v₂ (by decide)).of_upd v₃ (by decide)).of_upd v₄ (by decide)).of_upd v₅ (by decide)
  obtain m5 : u₅.mem = u.mem := by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  refine wp_str (by decide) (w₅.ea (K := o + 4 * j) (at_ptr (by simp only [v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact p1u)
    (by simp only [v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact e12)) (by omega_using [hoz, hj])) (w₅.write (d := o + 4 * j + 0) (n := 4) (by omega_using [hoz, hj]))
    fun u₆ m₆ => wp_bump (by decide) fun u₇ v₇ => wp_bump (by decide) fun u₈ v₈ => wp_bump (by decide) fun u₉ v₉ =>
      WP.block_nil ?_
  obtain m9 : u₉.mem = u.mem.writeW (off base (o + 4 * j)) (u₅.gpr .r5) := by
    rw [v₉.mem, v₈.mem, v₇.mem, m₆.mem, m5, Nat.add_zero]
  obtain val : u₅.gpr .r5 = if b then u.mem.readW (off base (tmp + 4 * j + 0)) 32
      else u.mem.readW (off base (src + 4 * j + 0)) 32 := by
    simp only [v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte, VG.Proof.X25519.Arm.dpVal, r3u, h3]
    rw [v₁.mem, select_val]
  refine ⟨⟨((w₅.of_mupd m₆).of_upd v₇ (by decide) |>.of_upd v₈ (by decide)).of_upd v₉ (by decide),
    ⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h5, h7, h8, h9, h10⟩ := hr
    simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, h1, h5, h7, h8, h10, ↓reduceIte]; exact Ru.gpr r (by simp [h1, h5, h7, h8, h9, h10])
  · rw [v₉.rd, v₈.rd, v₇.rd, m₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]; exact Ru.rd
  · rw [v₉.wr, v₈.wr, v₇.wr, m₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]; exact Ru.wr
  · rw [v₉.sp, v₈.sp, v₇.sp, m₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp]; exact Ru.sp
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact ptr_step p8u
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact ptr_step p1u
  · intro i hi
    rw [m9]
    rcases Nat.lt_or_ge i j with h | h
    · rw [w32_write_lt (by omega_using [hoz, hn, hj]) (by omega_using [h]), Vu i h]
    · rw [show i = j by omega_using [hi, h], w32_write_self, val]
      cases b
      · exact xs
      · exact xt
  · rw [m9]
    exact (Ou.mono (Nat.le_refl _) (by omega_using [])).trans ((writeW32_outside _ _ _ (by omega_using [h16s, h16o, hj])).mono (by omega_using []) (by omega_using []))
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact ptr_step pu
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact p9u

/-! ## The multiplication on words, by `umaal` -/

/-- `s'` is `s` with `lo` and `hi` set to the low and high words of `r`. -/
structure Upd2 (s s' : State) (lo hi : Reg) (r : Nat) : Prop where
  glo : (s'.gpr lo).toNat = r % 2 ^ 32
  ghi : (s'.gpr hi).toNat = r / 2 ^ 32
  other : ∀ q, q ≠ lo → q ≠ hi → s'.gpr q = s.gpr q
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd2.rest {s s' : State} {lo hi : Reg} {r : Nat} (h : Upd2 s s' lo hi r) {ws : List Reg}
    (hl : lo ∈ ws) (hh : hi ∈ ws) : Rest ws s s' :=
  ⟨fun q hq => h.other q (fun e => hq (e ▸ hl)) (fun e => hq (e ▸ hh)), h.rd, h.wr, h.sp⟩

theorem Ws.of_upd2 {s s' : State} {lo hi : Reg} {r : Nat} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h : Upd2 s s' lo hi r) (hl : lo ≠ .r12) (hh : hi ≠ .r12) : Ws s' base size :=
  ⟨by rw [h.other _ (Ne.symm hl) (Ne.symm hh)]; exact hs.wb, h.wr ▸ hs.wr, hs.nowrap⟩

theorem umaal_lt {a b c d : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32) (hd : d < 2 ^ 32) :
    a * b + c + d < 2 ^ 64 := by
  have := Nat.mul_le_mul (Nat.le_of_lt_succ ha) (Nat.le_of_lt_succ hb)
  omega_using [this, hc, hd]

/-- `umaal lo, hi, n, m`: `hi:lo = n m + hi + lo`. -/
theorem wp_umaal {is : List Instr} {s : State} {Q : State → Prop} {lo hi n m : Reg} (hne : lo ≠ hi)
    (k : ∀ s', Upd2 s s' lo hi ((s.gpr n).toNat * (s.gpr m).toNat + (s.gpr hi).toNat + (s.gpr lo).toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.umaal lo hi n m :: is)) s Q := by
  obtain hr := umaal_lt (s.gpr n).isLt (s.gpr m).isLt (s.gpr hi).isLt (s.gpr lo).isLt
  generalize hR : (s.gpr n).toNat * (s.gpr m).toNat + (s.gpr hi).toNat + (s.gpr lo).toNat = R at hr k
  refine VG.Proof.X25519.Arm.WP.cons (s' := (s.setReg lo (BitVec.ofNat 32 R)).setReg hi (BitVec.ofNat 32 (R / 2 ^ 32)))
    (by simp only [exec, hne, ↓reduceIte, hR]) (k _ ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩)
  · simp only [State.setReg, hne, ↓reduceIte, BitVec.toNat_ofNat]
  · simp only [State.setReg, ↓reduceIte, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by decide)]; exact hr)
  · intro q h1 h2; simp only [State.setReg, h1, h2, ↓reduceIte]

/-- Word `h` of `[src]` (at `[r8 + 4h]`) times `r2`, plus the carry `r3`, added
to the window's word at `[r10 + 4h]`. -/
theorem macU_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {K S h : Nat} (hh : h < 2)
    (h10 : s.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 K) (h8 : s.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 S)
    (hK : K + 4 * h + 4 ≤ size) (hS : S + 4 * h + 4 ≤ size) :
    WP isa (.block (macU h)) s fun u =>
      u.mem = s.mem.writeW (off base (K + 4 * h)) (BitVec.ofNat 32
        (w32 s.mem base (S + 4 * h) * (s.gpr .r2).toNat + (s.gpr .r3).toNat + w32 s.mem base (K + 4 * h))) ∧
      (u.gpr .r3).toNat =
        (w32 s.mem base (S + 4 * h) * (s.gpr .r2).toNat + (s.gpr .r3).toNat + w32 s.mem base (K + 4 * h)) / 2 ^ 32 ∧
      Rest [.r3, .r5, .r7] s u := by
  simp only [macU]
  refine wp_ldr (by omega_using [hh]) (hs.ea h8 (by omega_using [hS])) (hs.read (by omega_using [hS])) fun s₁ u₁ => ?_
  obtain w₁ := hs.of_upd u₁ (by decide)
  obtain e10 : s₁.gpr .r10 = s₁.gpr .r12 + BitVec.ofNat 32 K := by
    rw [u₁.other .r10 (by decide), u₁.other .r12 (by decide)]; exact h10
  refine wp_ldr (by omega_using [hh]) (w₁.ea e10 (by omega_using [hK])) (w₁.read (by omega_using [hK])) fun s₂ u₂ => ?_
  refine wp_umaal (by decide) fun s₃ u₃ => ?_
  obtain w₃ := (w₁.of_upd u₂ (by decide)).of_upd2 u₃ (by decide) (by decide)
  obtain e10₃ : s₃.gpr .r10 = s₃.gpr .r12 + BitVec.ofNat 32 K := by
    rw [u₃.other .r10 (by decide) (by decide), u₃.other .r12 (by decide) (by decide), u₂.other .r10 (by decide),
      u₂.other .r12 (by decide)]; exact e10
  refine wp_str (by omega_using [hh]) (w₃.ea e10₃ (by omega_using [hK])) (w₃.write (by omega_using [hK])) fun s₄ m₄ =>
    WP.block_nil ?_
  obtain eR : (s₂.gpr .r7).toNat * (s₂.gpr .r2).toNat + (s₂.gpr .r3).toNat + (s₂.gpr .r5).toNat =
      w32 s.mem base (S + 4 * h) * (s.gpr .r2).toNat + (s.gpr .r3).toNat + w32 s.mem base (K + 4 * h) := by
    rw [u₂.other .r7 (by decide), u₂.other .r2 (by decide), u₂.other .r3 (by decide), u₂.gpr, u₁.gpr,
      u₁.other .r2 (by decide), u₁.other .r3 (by decide), u₁.mem]
  rw [eR] at u₃
  refine ⟨?_, ?_, ?_⟩
  · rw [m₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact congrArg _ (BitVec.eq_of_toNat_eq (by rw [u₃.glo, BitVec.toNat_ofNat]))
  · rw [m₄.gpr, u₃.ghi]
  · exact (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide) (by decide))).trans
      (m₄.rest _)

/-- The words up to an even count and the next two. -/
theorem val32_two (m : Mem) (base : Addr) (d j : Nat) :
    val32 m base d (2 * j + 2) = val32 m base d (2 * j) + w32 m base (d + 8 * j) * 2 ^ (64 * j) +
      w32 m base (d + 8 * j + 4) * (2 ^ 32 * 2 ^ (64 * j)) := by
  rw [show 2 * j + 2 = 2 * j + 1 + 1 by omega_using [], val32_succ, val32_succ,
    show d + 4 * (2 * j) = d + 8 * j by omega_using [], show d + 4 * (2 * j + 1) = d + 8 * j + 4 by omega_using [],
    show 32 * (2 * j) = 64 * j by omega_using [], show 32 * (2 * j + 1) = 32 + 64 * j by omega_using [], Nat.pow_add,
    Nat.mul_comm (2 ^ (64 * j)), Nat.mul_comm (2 ^ 32 * 2 ^ (64 * j))]

/-- An iteration of a row on words, as numbers. -/
theorem mac_stepU {D c T V P u d0 d1 t0 t1 : Nat} (h : D + c * P = T + u * V) :
    D + (d0 * u + c + t0) % 2 ^ 32 * P + (d1 * u + (d0 * u + c + t0) / 2 ^ 32 + t1) % 2 ^ 32 * (2 ^ 32 * P) +
      (d1 * u + (d0 * u + c + t0) / 2 ^ 32 + t1) / 2 ^ 32 * (2 ^ 64 * P) =
      T + t0 * P + t1 * (2 ^ 32 * P) + u * (V + d0 * P + d1 * (2 ^ 32 * P)) := by
  obtain e0 := Nat.mod_add_div (d0 * u + c + t0) (2 ^ 32)
  obtain e1 := Nat.mod_add_div (d1 * u + (d0 * u + c + t0) / 2 ^ 32 + t1) (2 ^ 32)
  generalize (d0 * u + c + t0) % 2 ^ 32 = a0 at *
  generalize (d0 * u + c + t0) / 2 ^ 32 = q0 at *
  generalize (d1 * u + q0 + t1) % 2 ^ 32 = a1 at *
  generalize (d1 * u + q0 + t1) / 2 ^ 32 = q1 at *
  grind

/-- The carry into the window's last two words, as numbers. -/
theorem carry_valU {Du c P Ds V tW tW1 : Nat} (h : Du + c * P = Ds + V) :
    Du + (c + tW) % 2 ^ 32 * P + (tW1 + (c + tW) / 2 ^ 32) * (2 ^ 32 * P) =
      Ds + tW * P + tW1 * (2 ^ 32 * P) + V := by
  obtain e := Nat.mod_add_div (c + tW) (2 ^ 32)
  generalize (c + tW) % 2 ^ 32 = a at *
  generalize (c + tW) / 2 ^ 32 = q at *
  grind

/-- The invariant of a row's loop on words after `j` pairs of words of `[src]`. -/
structure RowInvU (s : State) (base : Addr) (size w src : Nat) (j : Nat) (u : State) : Prop where
  ws : Ws u base size
  rest : Rest [.r3, .r5, .r7, .r8, .r9, .r10] s u
  r10 : u.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 w + BitVec.ofNat 32 (8 * j)
  val : val32 u.mem base w (2 * j) + (u.gpr .r3).toNat * 2 ^ (64 * j) =
    val32 s.mem base w (2 * j) + (s.gpr .r2).toNat * val32 s.mem base src (2 * j)
  out : Outside base w (8 * j) s.mem u.mem

theorem RowInvU.fupd {s : State} {base : Addr} {size w src j : Nat} {u u' : State}
    (h : RowInvU s base size w src j u) (f : Fupd u u') : RowInvU s base size w src j u' :=
  ⟨h.ws.of_fupd f, h.rest.trans (f.rest _), by rw [f.gpr]; exact h.r10, by rw [f.gpr, f.mem]; exact h.val,
    by rw [f.mem]; exact h.out⟩

/-- The window at `r0 = r12 + w` `+= r2 · [src]` (`2n` words), when the sum
fits its `2n + 2` words; `r4` is zero. -/
theorem mulRowU_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {src w n : Nat}
    (hW : words M = 2 * n) (hn : 0 < n) (h0 : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 w) (h4 : s.gpr .r4 = 0)
    (hsrc : src + 8 * n ≤ size) (h16 : src + 8 * n < 2 ^ 16) (hw : w + 8 * n + 8 ≤ size)
    (hsep : src + 8 * n ≤ w ∨ w + 8 * n + 8 ≤ src)
    (hlt : val32 s.mem base w (2 * n + 2) + (s.gpr .r2).toNat * val32 s.mem base src (2 * n) <
      2 ^ (64 * n + 64)) :
    WP isa (mulRowU M src) s fun u => Ws u base size ∧ Outside base w (8 * n + 8) s.mem u.mem ∧
      val32 u.mem base w (2 * n + 2) = val32 s.mem base w (2 * n + 2) +
        (s.gpr .r2).toNat * val32 s.mem base src (2 * n) ∧
      Rest [.r3, .r5, .r7, .r8, .r9, .r10] s u := by
  have hnw := hs.nowrap
  unfold mulRowU
  rw [hW]
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_ptr (d := .r8) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₄ =>
    WP.block_nil ?_)
  obtain R : Rest [.r3, .r5, .r7, .r8, .r9, .r10] s t := (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
    (u₃.rest (by decide))).trans (u₄.rest (by decide))
  obtain mt : t.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain I0 : RowInvU s base size w src 0 t := by
    refine ⟨hs.of_rest R (by decide), R, ?_, ?_, ?_⟩
    · simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, h0]
      exact (BitVec.add_zero _).symm
    · simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; rfl
    · rw [mt]; exact Outside.refl _ _ _ _
  obtain p8 : t.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 src := by
    simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 src + BitVec.ofNat 32 (8 * n) := by
    simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, Offset.add_add]
    rw [show src + 4 * (2 * n) = src + 8 * n by omega_using []]
  clear u₁ u₂ u₃ u₄ mt R
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 src) (step := 8) (k := n)
    (RowInvU s base size w src) (by decide) hn (by omega_arith) (fun _ _ _ h f => h.fupd f) I0 p8 p9 ?_
    fun u I _ => ?_)
  · intro j hj u I pu p9u
    simp only [List.append_assoc]
    obtain e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
    obtain xs0 : w32 u.mem base (src + 8 * j) = w32 s.mem base (src + 8 * j) := I.out.w32 (by omega_arith) (by omega_arith)
    obtain xs1 : w32 u.mem base (src + 8 * j + 4) = w32 s.mem base (src + 8 * j + 4) :=
      I.out.w32 (by omega_arith) (by omega_arith)
    obtain x0 : w32 u.mem base (w + 8 * j) = w32 s.mem base (w + 8 * j) := I.out.w32 (by omega_arith) (by omega_arith)
    obtain x1 : w32 u.mem base (w + 8 * j + 4) = w32 s.mem base (w + 8 * j + 4) := I.out.w32 (by omega_arith) (by omega_arith)
    obtain g2 : u.gpr .r2 = s.gpr .r2 := I.rest.gpr _ (by decide)
    refine VG.Proof.X25519.Arm.WP.append (macU_ok I.ws (K := w + 8 * j) (S := src + 8 * j) (h := 0) (by decide)
      (at_ptr I.r10 e12) (at_ptr pu e12) (by omega_arith) (by omega_arith)) fun u₂ ⟨M₂, C₂, R₂⟩ => ?_
    obtain w₂ := I.ws.of_rest R₂ (by decide)
    refine VG.Proof.X25519.Arm.WP.append (macU_ok w₂ (K := w + 8 * j) (S := src + 8 * j) (h := 1) (by decide)
      (by rw [R₂.gpr _ (by decide), R₂.gpr .r12 (by decide)]; exact at_ptr I.r10 e12)
      (by rw [R₂.gpr _ (by decide), R₂.gpr .r12 (by decide)]; exact at_ptr pu e12) (by omega_arith) (by omega_arith))
      fun u₃ ⟨M₃, C₃, R₃⟩ => ?_
    refine wp_bump (by decide) fun u₄ v₄ => wp_bump (by decide) fun u₅ v₅ => WP.block_nil ?_
    rw [R₂.gpr .r2 (by decide), C₂, M₂, Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.add_zero,
      w32_write_ne (size := size) hnw (by omega_arith) (by omega_arith) (by omega_arith),
      w32_write_ne (size := size) hnw (by omega_arith) (by omega_arith) (by omega_arith)] at M₃ C₃
    rw [x0, x1, xs0, xs1, g2] at M₃ C₃
    obtain m₅ : u₅.mem = u₃.mem := by rw [v₅.mem, v₄.mem]
    obtain ⟨d0, d1, O⟩ := pair_writes (m := u.mem) (base := base) (Q := w + 8 * j) (by omega_arith) _ _
    rw [← M₃] at d0 d1 O
    rw [BitVec.toNat_ofNat] at d0 d1
    obtain c₅ : u₅.gpr .r3 = u₃.gpr .r3 := by simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
    refine ⟨⟨(((w₂.of_rest R₃ (by decide)).of_upd v₄ (by decide)).of_upd v₅ (by decide)),
      I.rest.trans (((R₂.mono (by decide)).trans (R₃.mono (by decide))).trans
        ((v₄.rest (by decide)).trans (v₅.rest (by decide)))), ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
      rw [R₃.gpr .r10 (by decide), R₂.gpr .r10 (by decide)]
      rw [I.r10, Offset.add_add, Offset.add_add, Offset.add_add, show 8 * (j + 1) = 8 * j + 8 by omega_arith]
    · rw [m₅, c₅, C₃, show 2 * (j + 1) = 2 * j + 2 by omega_arith, val32_two, d0, d1, O.val32 (by omega_arith) (by omega_arith),
        show 64 * (j + 1) = 64 + 64 * j by omega_arith, Nat.pow_add, val32_two, val32_two]
      exact mac_stepU I.val
    · rw [m₅]
      exact (I.out.mono (by omega_arith) (by omega_arith)).trans (O.mono (by omega_arith) (by omega_arith))
    · simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
      rw [R₃.gpr .r8 (by decide), R₂.gpr .r8 (by decide)]
      exact ptr_step pu
    · simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]
      rw [R₃.gpr .r9 (by decide), R₂.gpr .r9 (by decide)]
      exact p9u
  · have e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
    obtain e10 : u.gpr .r10 = u.gpr .r12 + BitVec.ofNat 32 (w + 8 * n) := at_ptr I.r10 e12
    obtain x0 : w32 u.mem base (w + 8 * n) = w32 s.mem base (w + 8 * n) := I.out.w32 (by omega_arith) (by omega_arith)
    obtain x1 : w32 u.mem base (w + 8 * n + 4) = w32 s.mem base (w + 8 * n + 4) := I.out.w32 (by omega_arith) (by omega_arith)
    obtain g4 : u.gpr .r4 = 0 := by rw [I.rest.gpr _ (by decide)]; exact h4
    refine wp_ldr (by decide) (I.ws.ea (d := 0) e10 (by omega_arith)) (I.ws.read (d := w + 8 * n + 0) (n := 4) (by omega_arith))
      fun u₁ v₁ => wp_umaal (by decide) fun u₂ v₂ => ?_
    obtain w₂ := (I.ws.of_upd v₁ (by decide)).of_upd2 v₂ (by decide) (by decide)
    obtain e10₂ : u₂.gpr .r10 = u₂.gpr .r12 + BitVec.ofNat 32 (w + 8 * n) := by
      rw [v₂.other .r10 (by decide) (by decide), v₂.other .r12 (by decide) (by decide), v₁.other .r10 (by decide),
        v₁.other .r12 (by decide)]; exact e10
    refine wp_str (by decide) (w₂.ea (d := 0) e10₂ (by omega_arith)) (w₂.write (d := w + 8 * n + 0) (n := 4) (by omega_arith))
      fun u₃ m₃ => ?_
    obtain w₃ := w₂.of_mupd m₃
    obtain e10₃ : u₃.gpr .r10 = u₃.gpr .r12 + BitVec.ofNat 32 (w + 8 * n) := by rw [m₃.gpr]; exact e10₂
    refine wp_ldr (by decide) (w₃.ea (d := 4) e10₃ (by omega_arith)) (w₃.read (d := w + 8 * n + 4) (n := 4) (by omega_arith))
      fun u₄ v₄ => wp_dp (op2_reg _ _) fun u₅ v₅ => ?_
    obtain w₅ := (w₃.of_upd v₄ (by decide)).of_upd v₅ (by decide)
    refine wp_str (by decide) (w₅.ea (d := 4)
      (by simp only [v₅.get, v₄.get, reduceCtorEq, ↓reduceIte]; exact e10₃) (by omega_arith))
      (w₅.write (d := w + 8 * n + 4) (n := 4) (by omega_arith)) fun u₆ m₆ => WP.block_nil ?_
    obtain eR : (u₁.gpr .r4).toNat * (u₁.gpr .r4).toNat + (u₁.gpr .r3).toNat + (u₁.gpr .r5).toNat =
        (u.gpr .r3).toNat + w32 s.mem base (w + 8 * n) := by
      rw [v₁.other .r4 (by decide), g4, v₁.other .r3 (by decide), v₁.gpr, show (0 : BitVec 32).toNat = 0 from rfl,
        Nat.zero_mul, Nat.zero_add, Nat.add_zero]
      exact congrArg ((u.gpr .r3).toNat + ·) x0
    rw [eR] at v₂
    obtain Iv := I.val
    generalize hc : (u.gpr .r3).toNat = c at *
    generalize htW : w32 s.mem base (w + 8 * n) = tW at *
    generalize htW1 : w32 s.mem base (w + 8 * n + 4) = tW1 at *
    obtain hq : tW1 + (c + tW) / 2 ^ 32 < 2 ^ 32 := by
      have hl := hlt
      rw [val32_two, htW, htW1, show 64 * n + 64 = 64 + 64 * n by omega_using [], Nat.pow_add,
        ← carry_valU (tW := tW) (tW1 := tW1) Iv] at hl
      obtain h2 : (tW1 + (c + tW) / 2 ^ 32) * (2 ^ 32 * 2 ^ (64 * n)) < 2 ^ 32 * (2 ^ 32 * 2 ^ (64 * n)) := by
        rw [← Nat.mul_assoc (2 ^ 32) (2 ^ 32)]; omega_using [hl]
      rw [← Nat.mul_assoc, ← Nat.mul_assoc (2 ^ 32) (2 ^ 32)] at h2
      exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_mul_lt_mul_right h2)
    obtain r7₅ : (u₅.gpr .r7).toNat = tW1 + (c + tW) / 2 ^ 32 := by
      obtain r74 : (u₄.gpr .r7).toNat = tW1 := by
        rw [v₄.gpr, m₃.mem, v₂.mem, v₁.mem, Nat.add_zero, ← x1]
        exact w32_write_ne (size := size) hnw (by omega_arith) (by omega_arith) (by omega_arith) _
      obtain r34 : (u₄.gpr .r3).toNat = (c + tW) / 2 ^ 32 := by rw [v₄.other .r3 (by decide), m₃.gpr, v₂.ghi]
      rw [v₅.gpr, dpVal, toNat_add_lt (by rw [r74, r34]; exact hq), r74, r34]
    obtain st : u₆.mem = (u.mem.writeW (off base (w + 8 * n)) (u₂.gpr .r5)).writeW (off base (w + 8 * n + 4))
        (u₅.gpr .r7) := by
      rw [m₆.mem, v₅.mem, v₄.mem, m₃.mem, v₂.mem, v₁.mem, Nat.add_zero]
    obtain ⟨d0, d1, O⟩ := pair_writes (m := u.mem) (base := base) (Q := w + 8 * n) (by omega_arith) (u₂.gpr .r5)
      (u₅.gpr .r7)
    rw [← st] at d0 d1 O
    rw [v₂.glo] at d0
    rw [r7₅] at d1
    refine ⟨w₅.of_mupd m₆, ?_, ?_, ?_⟩
    · exact (I.out.mono (by omega_arith) (by omega_arith)).trans (O.mono (by omega_arith) (by omega_arith))
    · rw [val32_two, d0, d1, O.val32 (by omega_arith) (by omega_arith), val32_two, htW, htW1]
      exact carry_valU Iv
    · exact I.rest.trans ((((v₁.rest (by decide)).trans (v₂.rest (by decide) (by decide))).trans (m₃.rest _)).trans
        (((v₄.rest (by decide)).trans (v₅.rest (by decide))).trans (m₆.rest _)))

/-- The low word of a number. -/
theorem val32_low32 (m : Mem) (base : Addr) (d k : Nat) : val32 m base d (k + 1) % 2 ^ 32 = w32 m base d := by
  rw [val32, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (m.readW (off base d) 32).isLt

/-- The window one word up, when its low word is zero and the word above it
is zero. -/
theorem val32_shiftU {m : Mem} {base : Addr} {d k : Nat} (h0 : w32 m base d = 0)
    (htop : w32 m base (d + 4 * (k + 1)) = 0) :
    2 ^ 32 * val32 m base (d + 4) (k + 1) = val32 m base d (k + 1) := by
  obtain e1 : val32 m base d (k + 1 + 1) = w32 m base d + 2 ^ 32 * val32 m base (d + 4) (k + 1) := rfl
  obtain e2 := val32_succ m base d (k + 1)
  rw [e1, h0, htop, Nat.zero_add, Nat.mul_zero, Nat.add_zero] at e2
  exact e2

/-- `t₀ + q m` is a multiple of `2³²` for `q = t₀ m' mod 2³²`. -/
theorem mont_low32 (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 32 = 0) :
    (t0 + t0 * minv % 2 ^ 32 * m) % 2 ^ 32 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 32), Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod, show t0 + t0 * minv * m = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m]; omega_using [],
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-- A row keeps the window below `2³² · 2m`. -/
theorem row_ltU {T u B q m : Nat} (hT : T < 2 * m) (hu : u < 2 ^ 32) (hB : B < m) (hq : q < 2 ^ 32) :
    T + u * B + q * m < 2 ^ 32 * (2 * m) := by
  obtain h1 : u * B ≤ (2 ^ 32 - 1) * B := Nat.mul_le_mul_right _ (by omega_using [hu])
  obtain h2 : q * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega_using [hq])
  omega_using [hT, hB, h1, h2]

/-- The congruence a word on. -/
theorem cong_stepU {P T T' A B m U u q : Nat} (h0 : P * T = A * B + U * m)
    (h1 : 2 ^ 32 * T' = T + u * B + q * m) :
    2 ^ 32 * P * T' = (A + P * u) * B + (U + q * P) * m := by
  obtain e : 2 ^ 32 * P * T' = P * (2 ^ 32 * T') := by grind
  rw [e, h1, Nat.mul_add, Nat.mul_add, h0]
  grind

/-- A Newton step takes `-m⁻¹ mod 2¹⁶` to `-m⁻¹ mod 2³²`: `x (2 + m x)`. -/
theorem inv32 {m x y : Nat} (h : (m * x + 1) % 2 ^ 16 = 0) (hy : y % 2 ^ 32 = (m * x + 2) * x % 2 ^ 32) :
    (m * y + 1) % 2 ^ 32 = 0 := by
  obtain ⟨j, hj⟩ := Nat.dvd_of_mod_eq_zero h
  obtain e : m * ((m * x + 2) * x) + 1 = (m * x + 1) * (m * x + 1) := by grind
  rw [Nat.add_mod, Nat.mul_mod, hy, ← Nat.mul_mod, ← Nat.add_mod, e, hj, Nat.mul_mul_mul_comm,
    show (2 : Nat) ^ 16 * 2 ^ 16 = 2 ^ 32 from rfl]
  exact Nat.mul_mod_right _ _

/-- The machine's Newton step, as numbers. -/
theorem inv32_val (m x : Nat) :
    ((m % 2 ^ 32 * x % 2 ^ 32 + 2) % 2 ^ 32 * x) % 2 ^ 32 = ((m * x + 2) * x) % 2 ^ 32 := by
  rw [Nat.mul_mod ((m % 2 ^ 32 * x % 2 ^ 32 + 2) % 2 ^ 32) x, Nat.mod_mod, Nat.add_mod (m % 2 ^ 32 * x % 2 ^ 32) 2,
    Nat.mod_mod, Nat.mul_mod (m % 2 ^ 32) x, Nat.mod_mod, ← Nat.mul_mod m x, ← Nat.add_mod, ← Nat.mul_mod]

/-- The invariant of the multiplication on words before word `k` of `[a]`:
the window of `2n + 2` words at `acc + 4k` holds `T < 2m` with
`2^(32k) T ≡ A B` for the low `k` words `A` of `[a]`, and the words above it
are zero; `r4` is zero and `r6` is `-m⁻¹ mod 2³²`. -/
structure MulInvU (s : State) (base : Addr) (size acc a b m n : Nat) (k : Nat) (t : State) : Prop where
  ws : Ws t base size
  rest : Rest dclob s t
  r0 : t.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (acc + 4 * k)
  r1 : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k)
  r4 : t.gpr .r4 = 0
  r6 : (m * (t.gpr .r6).toNat + 1) % 2 ^ 32 = 0
  out : Outside base acc (4 * (4 * n + 2)) s.mem t.mem
  zeros : ∀ l, k + 2 * n + 2 ≤ l → l < 4 * n + 2 → w32 t.mem base (acc + 4 * l) = 0
  lt : val32 t.mem base (acc + 4 * k) (2 * n + 2) < 2 * m
  cong : ∃ U, 2 ^ (32 * k) * val32 t.mem base (acc + 4 * k) (2 * n + 2) =
    val32 s.mem base a k * val32 s.mem base b (2 * n) + U * m

/-- An iteration on words: the rows of word `k` of `[a]`, and the comparison
that ends the loop after the last. -/
theorem rowU_ok {s : State} {base : Addr} {size : Nat} {M : Mod} {inv acc o a b m n : Nat}
    (hn : 0 < n) (hW : words M = 2 * n) (hL : MulLayD M size inv acc o a b)
    (hm : val32 s.mem base M.mo (2 * n) = m) (hB : val32 s.mem base b (2 * n) < m) {k : Nat} (hk : k < 2 * n)
    {t : State} (I : MulInvU s base size acc a b m n k t) :
    WP isa (rowU M a b) t fun u => MulInvU s base size acc a b m n (k + 1) u ∧ u.z = decide (k + 1 = 2 * n) := by
  have hnw := I.ws.nowrap
  obtain hD : digits M = 4 * n := by
    have := hW; simp only [digits, Impl.Mont.Arm.words] at this ⊢; omega_using [this]
  obtain ⟨acc_le, a_le, b_le, mo_le, tmp_le, o_le, inv_le, acc16, a16, b16, mo16, tmp16, o16, inv16, sa, sb, smo,
    sinv, stmp, so, tmo, ot⟩ := hL
  simp only [accLen, hD, hW] at acc_le a_le b_le mo_le tmp_le o_le acc16 a16 b16 mo16 tmp16 sa sb smo sinv stmp so tmo ot
  obtain e12 : t.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
  obtain hmt : val32 t.mem base M.mo (2 * n) = m := by
    rw [I.out.val32 (by omega_using [smo]) (by omega_using [mo_le, hnw])]; exact hm
  obtain hbt : val32 t.mem base b (2 * n) = val32 s.mem base b (2 * n) :=
    I.out.val32 (by omega_using [sb]) (by omega_using [b_le, hnw])
  obtain hat : w32 t.mem base (a + 4 * k) = w32 s.mem base (a + 4 * k) :=
    I.out.w32 (by omega_using [sa, hk]) (by omega_using [a_le, hk, hnw])
  obtain top0 : w32 t.mem base (acc + 4 * k + 4 * (2 * n + 1 + 1)) = 0 := by
    have := I.zeros (k + 2 * n + 2) (by omega_using [hk]) (by omega_using [hk])
    rwa [show acc + 4 * (k + 2 * n + 2) = acc + 4 * k + 4 * (2 * n + 1 + 1) by omega_using []] at this
  obtain hm0 : m < 2 ^ (64 * n) := by
    rw [← hm, show 64 * n = 32 * (2 * n) by omega_using []]; exact val32_lt _ _ _ _
  obtain hak : w32 s.mem base (a + 4 * k) < 2 ^ 32 := (s.mem.readW (off base (a + 4 * k)) 32).isLt
  unfold rowU
  -- the word of `[a]`
  refine WP.seq (wp_ldr (by decide) (I.ws.ea (d := 0) (at_ptr' I.r1 e12) (by omega_using [a_le, hk]))
    (I.ws.read (d := a + 4 * k + 0) (n := 4) (by omega_using [a_le, hk])) fun t₁ u₁ => WP.block_nil ?_)
  obtain w₁ := I.ws.of_upd u₁ (by decide)
  obtain r2₁ : (t₁.gpr .r2).toNat = w32 s.mem base (a + 4 * k) := by rw [u₁.gpr, Nat.add_zero]; exact hat
  obtain hlt₁ : val32 t₁.mem base (acc + 4 * k) (2 * n + 2) + (t₁.gpr .r2).toNat * val32 t₁.mem base b (2 * n) <
      2 ^ (64 * n + 64) := by
    rw [u₁.mem, hbt, r2₁, Nat.pow_add]
    obtain h1 : w32 s.mem base (a + 4 * k) * val32 s.mem base b (2 * n) ≤ (2 ^ 32 - 1) * m :=
      Nat.mul_le_mul (by omega_using [hak]) (by omega_using [hB])
    obtain h2 : (2 ^ 32 + 1) * m < (2 ^ 32 + 1) * 2 ^ (64 * n) := Nat.mul_lt_mul_of_pos_left hm0 (by decide)
    omega_using [I.lt, h1, h2]
  refine WP.seq (WP.mono (mulRowU_ok w₁ (M := M) (src := b) (w := acc + 4 * k) hW hn
    (by rw [u₁.other .r0 (by decide), u₁.other .r12 (by decide)]; exact at_ptr' I.r0 e12)
    (by rw [u₁.other .r4 (by decide)]; exact I.r4) (by omega_using [b_le]) (by omega_using [b16])
    (by omega_using [acc_le, hk]) (by omega_using [sb, hk]) hlt₁) fun t₃ ⟨w₃, O₃, V₃, R₃⟩ => ?_)
  rw [u₁.mem, hbt, r2₁] at V₃
  rw [u₁.mem] at O₃
  -- the quotient
  obtain e0₃ : t₃.gpr .r0 = t₃.gpr .r12 + BitVec.ofNat 32 (acc + 4 * k) := by
    rw [R₃.gpr .r0 (by decide), R₃.gpr .r12 (by decide), u₁.other .r0 (by decide), u₁.other .r12 (by decide)]
    exact at_ptr' I.r0 e12
  refine WP.seq (wp_ldr (by decide) (w₃.ea (d := 0) e0₃ (by omega_using [acc_le, hk]))
    (w₃.read (d := acc + 4 * k + 0) (n := 4) (by omega_using [acc_le, hk])) fun t₄ u₄ => wp_mul fun t₅ u₅ =>
    WP.block_nil ?_)
  obtain w₅ := (w₃.of_upd u₄ (by decide)).of_upd u₅ (by decide)
  obtain m₅ : t₅.mem = t₃.mem := by rw [u₅.mem, u₄.mem]
  obtain g6 : t₃.gpr .r6 = t.gpr .r6 := by rw [R₃.gpr _ (by decide), u₁.other _ (by decide)]
  obtain hq : (t₅.gpr .r2).toNat = w32 t₃.mem base (acc + 4 * k) * (t.gpr .r6).toNat % 2 ^ 32 := by
    rw [u₅.gpr, BitVec.toNat_mul, u₄.gpr, u₄.other .r6 (by decide), g6, Nat.add_zero]
  obtain hq32 : (t₅.gpr .r2).toNat < 2 ^ 32 := (t₅.gpr .r2).isLt
  obtain hmo₃ : val32 t₃.mem base M.mo (2 * n) = m := by
    rw [O₃.val32 (by omega_using [smo, hk]) (by omega_using [mo_le, hnw])]; exact hmt
  obtain hrow := row_ltU I.lt hak hB hq32
  obtain hlt₂ : val32 t₅.mem base (acc + 4 * k) (2 * n + 2) + (t₅.gpr .r2).toNat * val32 t₅.mem base M.mo (2 * n) <
      2 ^ (64 * n + 64) := by
    rw [m₅, hmo₃, V₃, Nat.pow_add]
    obtain h2 : 2 * 2 ^ 32 * m < 2 * 2 ^ 32 * 2 ^ (64 * n) := Nat.mul_lt_mul_of_pos_left hm0 (by decide)
    omega_using [hrow, h2]
  obtain e0₅ : t₅.gpr .r0 = t₅.gpr .r12 + BitVec.ofNat 32 (acc + 4 * k) := by
    simp only [u₅.get, u₄.get, reduceCtorEq, ↓reduceIte]; exact e0₃
  refine WP.seq (WP.mono (mulRowU_ok w₅ (M := M) (src := M.mo) (w := acc + 4 * k) hW hn e0₅
    (by simp only [u₅.get, u₄.get, reduceCtorEq, ↓reduceIte]
        rw [R₃.gpr _ (by decide), u₁.other _ (by decide)]; exact I.r4)
    (by omega_using [mo_le]) (by omega_using [mo16]) (by omega_using [acc_le, hk]) (by omega_using [smo, hk]) hlt₂)
    fun t₈ ⟨w₈, O₈, V₈, R₈⟩ => ?_)
  rw [m₅, hmo₃, V₃] at V₈
  rw [m₅] at O₈
  refine wp_bump (by decide) fun t₉ v₉ => wp_bump (by decide) fun t₁₀ v₁₀ =>
    wp_ptr (d := .r9) (by decide) (by rw [hW]; omega_using [a16]) fun t₁₁ v₁₁ =>
    wp_cmp (op2_reg _ _) fun t₁₂ f₁₂ z₁₂ => WP.block_nil ?_
  obtain hz : w32 t₈.mem base (acc + 4 * k) = 0 := by
    obtain ht0 : w32 t₃.mem base (acc + 4 * k) = (val32 t.mem base (acc + 4 * k) (2 * n + 2) +
        w32 s.mem base (a + 4 * k) * val32 s.mem base b (2 * n)) % 2 ^ 32 := by rw [← V₃, val32_low32]
    rw [← val32_low32 (k := 2 * n + 1), V₈, hq]
    generalize val32 t.mem base (acc + 4 * k) (2 * n + 2) +
        w32 s.mem base (a + 4 * k) * val32 s.mem base b (2 * n) = T1 at ht0 ⊢
    rw [show ∀ x, (T1 + x * m) % 2 ^ 32 = (T1 % 2 ^ 32 + x * m) % 2 ^ 32 from fun x => by omega_using [], ← ht0]
    exact mont_low32 _ _ _ I.r6
  obtain htop' : w32 t₈.mem base (acc + 4 * k + 4 * (2 * n + 1 + 1)) = 0 := by
    rw [O₈.w32 (by omega_using []) (by omega_using [acc_le, hk, hnw]),
      O₃.w32 (by omega_using []) (by omega_using [acc_le, hk, hnw])]
    exact top0
  obtain hsh := val32_shiftU hz htop'
  obtain m₁₂ : t₁₂.mem = t₈.mem := by rw [f₁₂.mem, v₁₁.mem, v₁₀.mem, v₉.mem]
  obtain e12₈ : t₈.gpr .r12 = s.gpr .r12 := by
    rw [R₈.gpr _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), R₃.gpr _ (by decide),
      u₁.other _ (by decide)]; exact e12
  obtain r1₁₁ : t₁₁.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) + BitVec.ofNat 32 4 := by
    rw [v₁₁.other .r1 (by decide), v₁₀.gpr, v₉.other .r1 (by decide), R₈.gpr .r1 (by decide), u₅.other .r1 (by decide),
      u₄.other .r1 (by decide), R₃.gpr .r1 (by decide), u₁.other .r1 (by decide), I.r1]
  obtain r9₁₁ : t₁₁.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) + BitVec.ofNat 32 (8 * n - 4 * k) := by
    rw [v₁₁.gpr, v₁₀.other .r12 (by decide), v₉.other .r12 (by decide), e12₈, hW, Offset.add_add]
    rw [show a + 4 * k + (8 * n - 4 * k) = a + 4 * (2 * n) by omega_using [hk]]
  obtain R₁₂ : Rest dclob s t₁₂ := (((I.rest.trans (u₁.rest (by decide))).trans (R₃.mono (by decide))).trans
    (((u₄.rest (by decide)).trans (u₅.rest (by decide))).trans (R₈.mono (by decide)))).trans
    (((v₉.rest (by decide)).trans (v₁₀.rest (by decide))).trans ((v₁₁.rest (by decide)).trans (f₁₂.rest _)))
  refine ⟨⟨(((w₈.of_upd v₉ (by decide)).of_upd v₁₀ (by decide)).of_upd v₁₁ (by decide)).of_fupd f₁₂, R₁₂, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₁₂.gpr, v₁₁.other .r0 (by decide), v₁₀.other .r0 (by decide), v₉.gpr, R₈.gpr .r0 (by decide), e0₅,
      u₅.other .r12 (by decide), u₄.other .r12 (by decide), R₃.gpr .r12 (by decide), u₁.other .r12 (by decide), e12,
      Offset.add_add]
    rw [show acc + 4 * k + 4 = acc + 4 * (k + 1) by omega_using []]
  · rw [f₁₂.gpr, r1₁₁, Offset.add_add, show a + 4 * k + 4 = a + 4 * (k + 1) by omega_using []]
  · rw [f₁₂.gpr, v₁₁.other .r4 (by decide), v₁₀.other .r4 (by decide), v₉.other .r4 (by decide), R₈.gpr .r4 (by decide),
      u₅.other .r4 (by decide), u₄.other .r4 (by decide), R₃.gpr .r4 (by decide), u₁.other .r4 (by decide)]
    exact I.r4
  · rw [f₁₂.gpr, v₁₁.other .r6 (by decide), v₁₀.other .r6 (by decide), v₉.other .r6 (by decide), R₈.gpr .r6 (by decide),
      u₅.other .r6 (by decide), u₄.other .r6 (by decide), g6]
    exact I.r6
  · rw [m₁₂]
    exact (I.out.trans (O₃.mono (by omega_using []) (by omega_using [hk]))).trans
      (O₈.mono (by omega_using []) (by omega_using [hk]))
  · intro l hl hl'
    rw [m₁₂, O₈.w32 (by omega_using [hl]) (by omega_using [hl', acc_le, hnw]),
      O₃.w32 (by omega_using [hl]) (by omega_using [hl', acc_le, hnw])]
    exact I.zeros l (by omega_using [hl]) hl'
  · rw [m₁₂, show acc + 4 * (k + 1) = acc + 4 * k + 4 by omega_using []]
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ 32) ?_
    rw [hsh, V₈]; exact hrow
  · obtain ⟨U, hU⟩ := I.cong
    refine ⟨U + (t₅.gpr .r2).toNat * 2 ^ (32 * k), ?_⟩
    rw [m₁₂, show acc + 4 * (k + 1) = acc + 4 * k + 4 by omega_using [], show 32 * (k + 1) = 32 + 32 * k by omega_using [],
      Nat.pow_add, val32_succ s.mem base a k]
    exact cong_stepU hU (hsh.trans V₈)
  · rw [z₁₂, r1₁₁, r9₁₁, sub_add_add, cmp_ofNat (by omega_using []) (by omega_using [a16, hk])]
    simp only [decide_eq_decide]
    omega_using [hk]

theorem wp_mvn {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {o : Op2} {v : BitVec 32}
    (ho : o.eval s = some v) (k : ∀ s', Upd s s' d (~~~v) → WP isa (.block is) s' Q) :
    WP isa (.block (.mvn d o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (~~~v)) (by simp only [exec, ho, Option.map_some])
    (k _ (VG.Proof.X25519.Arm.Upd.setReg _ _ _))

/-- An iteration of the difference on words, as numbers. -/
theorem diff_stepU {T c P Mv D w c' mj tj : Nat} (h : T + c * P + Mv = D + P)
    (hw : w + 2 ^ 32 * c' + mj = tj + (2 ^ 32 - 1) + c) :
    T + P * w + c' * (2 ^ 32 * P) + (Mv + P * mj) = D + P * tj + 2 ^ 32 * P := by
  obtain hw' : w + 2 ^ 32 * c' + mj + 1 = tj + 2 ^ 32 + c := by omega_using [hw]
  obtain e : P * (w + 2 ^ 32 * c' + mj + 1) = P * (tj + 2 ^ 32 + c) := by rw [hw']
  grind

/-- The invariant of the difference's loop on words after `j` words. -/
structure DiffInvU (s : State) (base : Addr) (size src tmp mo : Nat) (j : Nat) (u : State) : Prop where
  ws : Ws u base size
  rest : Rest dclob s u
  r2 : u.gpr .r2 = 1
  r3 : (u.gpr .r3).toNat ≤ 1
  r10 : u.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 src + BitVec.ofNat 32 (4 * j)
  r8 : u.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 tmp + BitVec.ofNat 32 (4 * j)
  val : val32 u.mem base tmp j + (u.gpr .r3).toNat * 2 ^ (32 * j) + val32 s.mem base mo j =
    val32 s.mem base src j + 2 ^ (32 * j)
  out : Outside base tmp (4 * j) s.mem u.mem

theorem DiffInvU.fupd {s : State} {base : Addr} {size src tmp mo j : Nat} {u u' : State}
    (h : DiffInvU s base size src tmp mo j u) (f : Fupd u u') : DiffInvU s base size src tmp mo j u' :=
  ⟨h.ws.of_fupd f, h.rest.trans (f.rest _), by rw [f.gpr]; exact h.r2, by rw [f.gpr]; exact h.r3,
    by rw [f.gpr]; exact h.r10, by rw [f.gpr]; exact h.r8, by rw [f.gpr, f.mem]; exact h.val,
    by rw [f.mem]; exact h.out⟩

/-- `[o] = [src] mod m` for the number `[src] < 2m` (`2n` words and a top
word), through `[M.tmp]`. -/
theorem csubU_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {src o m n : Nat}
    (hW : words M = 2 * n) (hn : 0 < n) (hsrc : src + 4 * (2 * n + 1) ≤ size) (ho : o + 4 * (2 * n) ≤ size)
    (htmp : M.tmp + 4 * (2 * n) ≤ size) (hmo : M.mo + 4 * (2 * n) ≤ size)
    (h16 : src + 4 * (2 * n + 1) < 2 ^ 16) (h16o : o < 2 ^ 16) (h16t : M.tmp + 4 * (2 * n) < 2 ^ 16)
    (h16m : M.mo + 4 * (2 * n) < 2 ^ 16)
    (hts : M.tmp + 4 * (2 * n) ≤ src ∨ src + 4 * (2 * n + 1) ≤ M.tmp)
    (htm : M.tmp + 4 * (2 * n) ≤ M.mo ∨ M.mo + 4 * (2 * n) ≤ M.tmp)
    (hos : o + 4 * (2 * n) ≤ src ∨ src + 4 * (2 * n + 1) ≤ o)
    (hot : o + 4 * (2 * n) ≤ M.tmp ∨ M.tmp + 4 * (2 * n) ≤ o)
    (hm : val32 s.mem base M.mo (2 * n) = m) (hm0 : 0 < m) (hV : val32 s.mem base src (2 * n + 1) < 2 * m) :
    WP isa (csubU M src o) s fun t => Ws t base size ∧
      val32 t.mem base o (2 * n) = val32 s.mem base src (2 * n + 1) % m ∧
      Outs base [(M.tmp, 4 * (2 * n)), (o, 4 * (2 * n))] s.mem t.mem ∧ Rest dclob s t := by
  have hnw := hs.nowrap
  unfold csubU
  rw [hW]
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r1) (by decide) (by omega_arith) fun s₄ u₄ =>
    wp_ptr (d := .r8) (by decide) (by omega_arith) fun s₅ u₅ => wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₆ =>
    WP.block_nil ?_)
  obtain R : Rest dclob s t := ((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
    ((u₃.rest (by decide)).trans (u₄.rest (by decide)))).trans (u₅.rest (by decide))).trans (u₆.rest (by decide))
  obtain mt : t.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain I0 : DiffInvU s base size src M.tmp M.mo 0 t := by
    refine ⟨hs.of_rest R (by decide), R, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; decide
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
      exact (BitVec.add_zero _).symm
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
      exact (BitVec.add_zero _).symm
    · simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; rfl
    · rw [mt]; exact Outside.refl _ _ _ _
  obtain p1 : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 M.mo := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 M.mo + BitVec.ofNat 32 (4 * (2 * n)) := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, Offset.add_add]
  clear u₁ u₂ u₃ u₄ u₅ u₆ mt R
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 M.mo) (step := 4) (k := 2 * n)
    (DiffInvU s base size src M.tmp M.mo) (by decide) (by omega_using [hn]) (by omega_arith) (fun _ _ _ h f => h.fupd f)
    I0 p1 p9 ?_ fun u I _ => ?_)
  · intro j hj u I pu p9u
    obtain e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
    obtain xt : w32 u.mem base (src + 4 * j) = w32 s.mem base (src + 4 * j) :=
      I.out.w32 (by omega_using [hts, hj]) (by omega_using [hsrc, hnw, hj])
    obtain xm : w32 u.mem base (M.mo + 4 * j) = w32 s.mem base (M.mo + 4 * j) :=
      I.out.w32 (by omega_using [htm, hj]) (by omega_using [hmo, hnw, hj])
    refine wp_ldr (by decide) (I.ws.ea (d := 0) (at_ptr pu e12) (by omega_using [hmo, hj]))
      (I.ws.read (d := M.mo + 4 * j + 0) (n := 4) (by omega_using [hmo, hj])) fun u₁ v₁ => ?_
    refine wp_mvn (op2_reg _ _) fun u₂ v₂ => ?_
    obtain w₂ := (I.ws.of_upd v₁ (by decide)).of_upd v₂ (by decide)
    refine wp_ldr (by decide) (w₂.ea (d := 0) (K := src + 4 * j)
      (by simp only [v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact at_ptr I.r10 e12) (by omega_using [hsrc, hj]))
      (w₂.read (d := src + 4 * j + 0) (n := 4) (by omega_using [hsrc, hj])) fun u₃ v₃ => ?_
    refine wp_umaal (by decide) fun u₄ v₄ => ?_
    obtain w₄ := (w₂.of_upd v₃ (by decide)).of_upd2 v₄ (by decide) (by decide)
    refine wp_str (by decide) (w₄.ea (d := 0) (K := M.tmp + 4 * j)
      (by rw [v₄.other .r8 (by decide) (by decide), v₄.other .r12 (by decide) (by decide)]
          simp only [v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte]; exact at_ptr I.r8 e12)
      (by omega_using [htmp, hj])) (w₄.write (d := M.tmp + 4 * j + 0) (n := 4) (by omega_using [htmp, hj]))
      fun u₅ m₅ => wp_bump (by decide) fun u₆ v₆ => wp_bump (by decide) fun u₇ v₇ => wp_bump (by decide) fun u₈ v₈ =>
        WP.block_nil ?_
    obtain eR : (u₃.gpr .r7).toNat * (u₃.gpr .r2).toNat + (u₃.gpr .r3).toNat + (u₃.gpr .r5).toNat =
        (2 ^ 32 - 1 - w32 s.mem base (M.mo + 4 * j)) + (u.gpr .r3).toNat + w32 s.mem base (src + 4 * j) := by
      rw [v₃.other .r7 (by decide), v₂.gpr, v₁.gpr, v₃.other .r2 (by decide), v₂.other .r2 (by decide),
        v₁.other .r2 (by decide), I.r2, v₃.other .r3 (by decide), v₂.other .r3 (by decide), v₁.other .r3 (by decide),
        v₃.gpr, v₂.mem, v₁.mem, BitVec.toNat_not, show (1 : BitVec 32).toNat = 1 from rfl, Nat.mul_one, Nat.add_zero,
        Nat.add_zero, ← xm, ← xt]
    rw [eR] at v₄
    obtain hmj : w32 s.mem base (M.mo + 4 * j) < 2 ^ 32 := (s.mem.readW (off base (M.mo + 4 * j)) 32).isLt
    obtain htj : w32 s.mem base (src + 4 * j) < 2 ^ 32 := (s.mem.readW (off base (src + 4 * j)) 32).isLt
    have hc := I.r3
    obtain mv : u₈.mem = u.mem.writeW (off base (M.tmp + 4 * j)) (u₄.gpr .r5) := by
      rw [v₈.mem, v₇.mem, v₆.mem, m₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, Nat.add_zero]
    obtain O' : Outside base (M.tmp + 4 * j) 4 u.mem u₈.mem := by
      rw [mv]; exact writeW32_outside _ _ _ (by omega_using [htmp, hnw, hj])
    obtain c₈ : u₈.gpr .r3 = u₄.gpr .r3 := by
      rw [v₈.other .r3 (by decide), v₇.other .r3 (by decide), v₆.other .r3 (by decide), m₅.gpr]
    refine ⟨⟨(((w₄.of_mupd m₅).of_upd v₆ (by decide)).of_upd v₇ (by decide)).of_upd v₈ (by decide),
      I.rest.trans (((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans ((v₃.rest (by decide)).trans
        (v₄.rest (by decide) (by decide)))).trans (m₅.rest _)).trans (((v₆.rest (by decide)).trans
        (v₇.rest (by decide))).trans (v₈.rest (by decide)))), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [v₈.other .r2 (by decide), v₇.other .r2 (by decide), v₆.other .r2 (by decide), m₅.gpr,
        v₄.other .r2 (by decide) (by decide), v₃.other .r2 (by decide), v₂.other .r2 (by decide), v₁.other .r2 (by decide)]
      exact I.r2
    · rw [c₈, v₄.ghi]; omega_using [hc, hmj, htj]
    · rw [v₈.other .r10 (by decide), v₇.other .r10 (by decide), v₆.gpr, m₅.gpr, v₄.other .r10 (by decide) (by decide),
        v₃.other .r10 (by decide), v₂.other .r10 (by decide), v₁.other .r10 (by decide)]
      exact ptr_step I.r10
    · rw [v₈.gpr, v₇.other .r8 (by decide), v₆.other .r8 (by decide), m₅.gpr, v₄.other .r8 (by decide) (by decide),
        v₃.other .r8 (by decide), v₂.other .r8 (by decide), v₁.other .r8 (by decide)]
      exact ptr_step I.r8
    · rw [c₈, v₄.ghi, val32_succ, val32_succ s.mem base M.mo, val32_succ s.mem base src,
        O'.val32 (by omega_using []) (by omega_using [htmp, hnw, hj]), mv, w32_write_self, v₄.glo,
        show 32 * (j + 1) = 32 + 32 * j by omega_using [], Nat.pow_add]
      exact diff_stepU I.val (by omega_using [hc, hmj, htj])
    · rw [mv]
      exact (I.out.mono (by omega_using []) (by omega_using [])).trans
        ((writeW32_outside _ _ _ (by omega_using [htmp, hnw, hj])).mono (by omega_using []) (by omega_using []))
    · rw [v₈.other .r1 (by decide), v₇.gpr, v₆.other .r1 (by decide), m₅.gpr, v₄.other .r1 (by decide) (by decide),
        v₃.other .r1 (by decide), v₂.other .r1 (by decide), v₁.other .r1 (by decide)]
      exact ptr_step pu
    · rw [v₈.other .r9 (by decide), v₇.other .r9 (by decide), v₆.other .r9 (by decide), m₅.gpr,
        v₄.other .r9 (by decide) (by decide), v₃.other .r9 (by decide), v₂.other .r9 (by decide), v₁.other .r9 (by decide)]
      exact p9u
  -- The mask, then the selection.
  obtain e12 : u.gpr .r12 = s.gpr .r12 := I.rest.gpr _ (by decide)
  obtain xt : w32 u.mem base (src + 4 * (2 * n)) = w32 s.mem base (src + 4 * (2 * n)) :=
    I.out.w32 (by omega_using [hts]) (by omega_using [hsrc, hnw])
  obtain hsplit : val32 s.mem base src (2 * n + 1) = val32 s.mem base src (2 * n) +
      2 ^ (32 * (2 * n)) * w32 s.mem base (src + 4 * (2 * n)) := val32_succ _ _ _ _
  obtain hmP : m < 2 ^ (32 * (2 * n)) := by rw [← hm]; exact val32_lt _ _ _ _
  obtain ht1 : w32 s.mem base (src + 4 * (2 * n)) ≤ 1 := by
    rcases Nat.lt_or_ge (w32 s.mem base (src + 4 * (2 * n))) 2 with h | h
    · omega_using [h]
    · have := Nat.mul_le_mul_left (2 ^ (32 * (2 * n))) h; omega_using [this, hV, hsplit, hmP]
  obtain ⟨hct, hres⟩ := csub_arith (X := val32 s.mem base src (2 * n)) (t := w32 s.mem base (src + 4 * (2 * n)))
    (T := val32 u.mem base M.tmp (2 * n)) (c := (u.gpr .r3).toNat) hmP hm0
    (by rw [hsplit] at hV; exact hV) ht1 I.r3 (val32_lt _ _ _ _)
    (by have := I.val; rw [hm, Nat.mul_comm (u.gpr .r3).toNat] at this; exact this)
  refine WP.seq (wp_ldr (by decide) (I.ws.ea (d := 0) (at_ptr I.r10 e12) (by omega_using [hsrc]))
    (I.ws.read (d := src + 4 * (2 * n) + 0) (n := 4) (by omega_using [hsrc])) fun u₁ v₁ =>
    wp_dp (op2_reg _ _) fun u₂ v₂ => wp_mov (op2_imm (by decide)) fun u₃ v₃ => wp_dp (op2_reg _ _) fun u₄ v₄ =>
    WP.block_nil ?_)
  obtain b4 : u₄.gpr .r3 = if decide ((u.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * n)) = 1) = true then
      BitVec.allOnes 32 else 0 := by
    simp only [v₄.get, v₃.get, v₂.get, v₁.get, reduceCtorEq, ↓reduceIte, dpVal, Nat.add_zero, decide_eq_true_eq]
    obtain hsum : (u.gpr .r3 + u.mem.readW (off base (src + 4 * (2 * n))) 32).toNat =
        (u.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * n)) := by
      have ew : (u.mem.readW (off base (src + 4 * (2 * n))) 32).toNat = w32 s.mem base (src + 4 * (2 * n)) := xt
      rw [toNat_add_lt (by rw [ew]; omega_using [hct]), ew]
    rcases (by omega_using [hct] : (u.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * n)) = 0 ∨
        (u.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * n)) = 1) with h | h
    · rw [ite_eq_right (by omega_using [h])]
      have : u.gpr .r3 + u.mem.readW (off base (src + 4 * (2 * n))) 32 = 0 :=
        BitVec.eq_of_toNat_eq (by rw [hsum, h]; rfl)
      rw [this]; rfl
    · rw [ite_eq_left h]
      have : u.gpr .r3 + u.mem.readW (off base (src + 4 * (2 * n))) 32 = 1 :=
        BitVec.eq_of_toNat_eq (by rw [hsum, h]; rfl)
      rw [this]; rfl
  obtain w₄ : Ws u₄ base size := (((I.ws.of_upd v₁ (by decide)).of_upd v₂ (by decide)).of_upd v₃ (by decide)).of_upd v₄
    (by decide)
  obtain R₄ : Rest dclob s u₄ := I.rest.trans (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
    ((v₃.rest (by decide)).trans (v₄.rest (by decide))))
  obtain m₄ : u₄.mem = u.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  clear v₁ v₂ v₃ v₄
  refine WP.mono (selectW_ok w₄ (k := 2 * n) (src := src) (tmp := M.tmp) (o := o) _ b4 (by omega_using [hn])
    (by omega_using [hsrc]) htmp ho (by omega_using [h16]) (by omega_using [h16t]) h16o
    (by omega_using [hos]) hot) fun t ⟨wt, Wd, Ot, Rt⟩ => ⟨wt, ?_, ?_, R₄.trans (Rt.mono (by decide))⟩
  · rw [m₄] at Wd
    by_cases hb : (u.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * n)) = 1
    · rw [val32_move (m := u.mem) (d := M.tmp) fun i hi => ?_, hsplit]
      · rw [ite_eq_left hb] at hres; exact hres
      · have := Wd i hi
        simp only [hb, decide_true, ↓reduceIte] at this
        exact this
    · rw [val32_move (m := s.mem) (d := src) fun i hi => ?_, hsplit]
      · rw [ite_eq_right hb] at hres; exact hres
      · have := Wd i hi
        simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte] at this
        rw [this]
        exact I.out.w32 (by omega_using [hts, hi]) (by omega_using [hsrc, hnw, hi])
  · rw [m₄] at Ot
    exact (Outs.of_outside I.out (by simp)).trans (Outs.of_outside Ot (by simp))

theorem val32_zeros {m : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m base (d + 4 * j) = 0) → val32 m base d k = 0
  | 0, _ => rfl
  | k + 1, h => by rw [val32_succ, val32_zeros fun j hj => h j (by omega_using [hj]), h k (by omega_using []), Nat.mul_zero]

/-- The loop of `mulU`, from the invariant at word 0 to the invariant at `2n`. -/
theorem mulLoopU_ok {s : State} {base : Addr} {size : Nat} {M : Mod} {inv acc o a b m n : Nat}
    (hn : 0 < n) (hW : words M = 2 * n) (hL : MulLayD M size inv acc o a b)
    (hm : val32 s.mem base M.mo (2 * n) = m) (hB : val32 s.mem base b (2 * n) < m) {t : State}
    (h0 : MulInvU s base size acc a b m n 0 t) :
    WP isa (.loop (rowU M a b) .ne) t fun u => MulInvU s base size acc a b m n (2 * n) u := by
  refine WP.loop (M := isa)
    (fun N t' => ∃ k, N = 2 * n - k ∧ k < 2 * n ∧ MulInvU s base size acc a b m n k t') ?_ (2 * n) t
    ⟨0, rfl, by omega_using [hn], h0⟩
  rintro N t' ⟨k, rfl, hk, I⟩
  refine WP.mono (rowU_ok hn hW hL hm hB hk I) fun u ⟨I', hz⟩ => ?_
  by_cases hk1 : k + 1 = 2 * n
  · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hk1]; rfl, hk1 ▸ I'⟩
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hk1]; rfl, 2 * n - (k + 1),
      by omega_using [hk], k + 1, rfl, by omega_using [hk, hk1], I'⟩

/-- `[o] = [a] [b] R⁻¹ mod m` (`R = 2^(32W)`) on words, with `-m⁻¹ mod 2¹⁶`
at `[inv]`, through the accumulator at `[acc]` and the temporary area. `[o]`
may be `[a]` or `[b]`. -/
theorem mulU_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {inv acc o a b m : Nat}
    (hn : 0 < M.n) (hL : MulLayD M size inv acc o a b)
    (hm : val32 s.mem base M.mo (words M) = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b (words M) < m) :
    WP isa (Dynamic.mulU M inv acc o a b) s fun t => Ws t base size ∧
      val32 t.mem base o (words M) < m ∧
      val32 t.mem base o (words M) * 2 ^ (32 * words M) % m =
        val32 s.mem base a (words M) * val32 s.mem base b (words M) % m ∧
      Outs base [(o, 4 * words M), (M.tmp, 4 * words M), (acc, 4 * (4 * words M + 2))] s.mem t.mem ∧
      Rest dclob s t := by
  have hnw := hs.nowrap
  obtain hm0 := m_pos_of_inv16 hinv
  obtain ⟨n, hW, hn0⟩ : ∃ n, words M = 2 * n ∧ 0 < n := ⟨M.n, by simp only [Impl.Mont.Arm.words], hn⟩
  obtain hD : digits M = 4 * n := by
    have := hW; simp only [digits, Impl.Mont.Arm.words] at this ⊢; omega_using [this]
  have hL' := hL
  obtain ⟨acc_le, a_le, b_le, mo_le, tmp_le, o_le, inv_le, acc16, a16, b16, mo16, tmp16, o16, inv16, sa, sb, smo,
    sinv, stmp, so, tmo, ot⟩ := hL'
  simp only [accLen, hD, hW] at acc_le a_le b_le mo_le tmp_le o_le acc16 a16 b16 mo16 tmp16 sa sb smo sinv stmp so tmo ot
  rw [hW] at hm hB ⊢
  unfold Dynamic.mulU
  rw [hW]
  refine WP.seq (WP.mono (zeros_ok hs (o := acc) (k := 2 * (2 * n) + 2) (by omega_using [])
    (by omega_using [acc_le]) (by omega_using [acc16])) fun t₀ ⟨w₀, Z₀, O₀, R₀⟩ => ?_)
  obtain e12 : t₀.gpr .r12 = s.gpr .r12 := R₀.gpr _ (by decide)
  obtain xm : w32 t₀.mem base M.mo = m % 2 ^ 32 := by
    rw [O₀.w32 (by omega_using [smo, hn0]) (by omega_using [mo_le, hnw, hn0]), ← hm,
      show 2 * n = 2 * n - 1 + 1 by omega_using [hn0], val32_low32]
  obtain xi : w32 t₀.mem base inv = w32 s.mem base inv := O₀.w32 (by omega_using [sinv]) (by omega_using [inv_le, hnw])
  simp only [inverseU, List.append_assoc]
  refine WP.seq (wp_ptr (d := .r5) (by decide) (by omega_using [mo16]) fun t₁ u₁ => ?_)
  obtain w₁ := w₀.of_upd u₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (d := 0) (K := M.mo) (by rw [u₁.gpr, u₁.other .r12 (by decide)])
    (by omega_using [mo_le, hn0])) (w₁.read (d := M.mo + 0) (n := 4) (by omega_using [mo_le, hn0])) fun t₂ u₂ => ?_
  obtain w₂ := w₁.of_upd u₂ (by decide)
  refine wp_ldr inv16 (w₂.ea12 (by omega_using [inv_le])) (w₂.read (d := inv) (n := 4) inv_le) fun t₃ u₃ =>
    wp_mul fun t₄ u₄ => wp_dp (op2_imm (by decide)) fun t₅ u₅ => wp_mul fun t₆ u₆ =>
    wp_mov (op2_imm (by decide)) fun t₇ u₇ => wp_ptr (d := .r0) (by decide) (by omega_using [acc16]) fun t₈ u₈ =>
    wp_ptr (d := .r1) (by decide) (by omega_using [a16]) fun t₉ u₉ => WP.block_nil ?_
  obtain m₉ : t₉.mem = t₀.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain r6 : (m * (t₉.gpr .r6).toNat + 1) % 2 ^ 32 = 0 := by
    refine inv32 hinv ?_
    rw [Nat.mod_eq_of_lt (t₉.gpr .r6).isLt, ← inv32_val, ← xm, ← xi]
    simp only [u₉.get, u₈.get, u₇.get, u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte, dpVal,
      u₁.mem, u₂.mem, Nat.add_zero, BitVec.toNat_mul, BitVec.toNat_add]
    rfl
  obtain I0 : MulInvU s base size acc a b m n 0 t₉ := by
    refine ⟨((((((((w₂.of_upd u₃ (by decide)).of_upd u₄ (by decide)).of_upd u₅ (by decide)).of_upd u₆ (by decide)).of_upd
        u₇ (by decide)).of_upd u₈ (by decide)).of_upd u₉ (by decide))),
      (R₀.mono (by decide)).trans (((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
        ((u₃.rest (by decide)).trans (u₄.rest (by decide)))).trans (((u₅.rest (by decide)).trans
        (u₆.rest (by decide))).trans ((u₇.rest (by decide)).trans (u₈.rest (by decide))))).trans (u₉.rest (by decide))),
      ?_, ?_, ?_, r6, ?_, ?_, ?_, ⟨0, ?_⟩⟩
    · simp only [u₉.get, u₈.get, u₇.get, u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12,
        Nat.mul_zero, Nat.add_zero]
    · simp only [u₉.get, u₈.get, u₇.get, u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, e12,
        Nat.mul_zero, Nat.add_zero]
    · simp only [u₉.get, u₈.get, u₇.get, reduceCtorEq, ↓reduceIte]
    · rw [m₉]; exact O₀.mono (by omega_using []) (by omega_using [])
    · intro l _ hl'
      rw [m₉, Z₀ l (by omega_using [hl'])]
    · rw [m₉, Nat.mul_zero, Nat.add_zero, val32_zeros fun j hj => Z₀ j (by omega_using [hj])]; omega_using [hm0]
    · rw [m₉, Nat.mul_zero, Nat.add_zero, val32_zeros fun j hj => Z₀ j (by omega_using [hj])]
      simp [val32]
  clear u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉
  refine WP.seq (WP.mono (mulLoopU_ok hn0 hW hL hm hB I0) fun u I => ?_)
  obtain hmu : val32 u.mem base M.mo (2 * n) = m := by
    rw [I.out.val32 (by omega_using [smo]) (by omega_using [mo_le, hnw])]; exact hm
  obtain hmP : m < 2 ^ (32 * (2 * n)) := by rw [← hm]; exact val32_lt _ _ _ _
  obtain hsplit : val32 u.mem base (acc + 4 * (2 * n)) (2 * n + 2) = val32 u.mem base (acc + 4 * (2 * n)) (2 * n + 1) +
      2 ^ (32 * (2 * n + 1)) * w32 u.mem base (acc + 4 * (2 * n) + 4 * (2 * n + 1)) := val32_succ _ _ _ _
  obtain htop : w32 u.mem base (acc + 4 * (2 * n) + 4 * (2 * n + 1)) = 0 := by
    have hl := I.lt
    rw [hsplit, show 32 * (2 * n + 1) = 32 * (2 * n) + 32 by omega_using [], Nat.pow_add] at hl
    rcases Nat.eq_zero_or_pos (w32 u.mem base (acc + 4 * (2 * n) + 4 * (2 * n + 1))) with h | h
    · exact h
    · have : 2 ^ (32 * (2 * n)) * 2 ^ 32 ≤
          2 ^ (32 * (2 * n)) * 2 ^ 32 * w32 u.mem base (acc + 4 * (2 * n) + 4 * (2 * n + 1)) :=
        Nat.le_mul_of_pos_right _ h
      omega_using [hl, hmP, this]
  obtain hT : val32 u.mem base (acc + 4 * (2 * n)) (2 * n + 1) = val32 u.mem base (acc + 4 * (2 * n)) (2 * n + 2) := by
    rw [hsplit, htop, Nat.mul_zero]; exact (Nat.add_zero _).symm
  refine WP.mono (csubU_ok I.ws (M := M) (src := acc + 4 * (2 * n)) (o := o) (m := m) hW hn0
    (by omega_using [acc_le]) o_le tmp_le mo_le (by omega_using [acc16]) o16 tmp16 mo16
    (by omega_using [stmp]) tmo (by omega_using [so]) ot hmu hm0 (by rw [hT]; exact I.lt))
    fun t ⟨wt, V, O, R⟩ => ⟨wt, ?_, ?_, ?_, I.rest.trans R⟩
  · rw [V]; exact Nat.mod_lt _ hm0
  · obtain ⟨U, hU⟩ := I.cong
    rw [V, hT, Nat.mod_mul_mod, Nat.mul_comm, hU, Nat.add_mul_mod_self_right]
  · exact (Outs.of_outside (I.out.mono (o' := acc) (n' := 4 * (4 * (2 * n) + 2)) (Nat.le_refl _) (by omega_using []))
      (by simp)).trans (O.mono (by simp))

/-- The multiplication of either kind: on digits, or on words by `umaal`. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {inv acc o a b m : Nat}
    (hn : 0 < M.n) (hL : MulLayD M size inv acc o a b)
    (hm : val32 s.mem base M.mo (words M) = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b (words M) < m) :
    WP isa (Dynamic.mul umaal M inv acc o a b) s fun t => Ws t base size ∧
      val32 t.mem base o (words M) < m ∧
      val32 t.mem base o (words M) * 2 ^ (32 * words M) % m =
        val32 s.mem base a (words M) * val32 s.mem base b (words M) % m ∧
      Outs base [(o, 4 * words M), (M.tmp, 4 * words M), (acc, 4 * (4 * words M + 2))] s.mem t.mem ∧
      Rest dclob s t := by
  cases umaal
  · exact mulD_ok hs hn hL hm hinv hB
  · exact mulU_ok hs hn hL hm hinv hB

theorem mul_noFrames (M : Mod) (inv acc o a b : Nat) :
    @Code.noFrames Instr Cond (Dynamic.mul umaal M inv acc o a b) = true := by
  cases umaal <;> rfl

end VG.Proof.Mont.Arm.Dyn

end

end

/-! ### `Mont.Arm.Dyn.Ops`, which only this module used -/

section

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the modular addition

`addD M acc o a b` writes `[o] = [a] + [b] mod m` (`addD_ok`), in the layout
of a multiplication (`MulLayD`), whose accumulator holds the sum's digits.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest)

/-- `[o] = [a] + [b] mod m`, for `[a], [b] < m`; `[o]` may be `[a]` or `[b]`. -/
theorem addD_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {inv acc o a b m : Nat}
    (hn : 0 < M.n) (hL : MulLayD M size inv acc o a b) (hm : val32 s.mem base M.mo (words M) = m) (hm0 : 0 < m)
    (hA : val32 s.mem base a (words M) < m) (hB : val32 s.mem base b (words M) < m) :
    WP isa (addD M acc o a b) s fun t => Ws t base size ∧
      val32 t.mem base o (words M) = (val32 s.mem base a (words M) + val32 s.mem base b (words M)) % m ∧
      Outs base [(o, 4 * words M), (M.tmp, 4 * words M), (acc, 4 * (4 * words M + 2))] s.mem t.mem ∧
      Rest dclob s t := by
  have hnw := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega_using []
  obtain ⟨acc_le, a_le, b_le, mo_le, tmp_le, o_le, inv_le, acc16, a16, b16, mo16, tmp16, o16, inv16, sa, sb, smo,
    sinv, stmp, so, tmo, ot⟩ := hL
  simp only [accLen, hD, hW] at acc_le a_le b_le mo_le tmp_le o_le acc16 a16 b16 mo16 tmp16 sa sb smo sinv stmp so tmo ot
  rw [hW] at hm hA hB ⊢
  unfold addD
  refine WP.seq (WP.mono (addDigits_ok hs (M := M) (acc := acc) (a := a) (b := b) hn
    (by rw [hD]; omega_using [acc_le]) (by rw [hW]; exact a_le) (by rw [hW]; exact b_le)
    (by rw [hD]; omega_using [acc16]) (by rw [hW]; exact a16) (by omega_using [b16])
    (by rw [hD, hW]; omega_using [sa]) (by rw [hD, hW]; omega_using [sb])) fun t₁ ⟨w₁, V₁, D₁, O₁, R₁⟩ => ?_)
  simp only [hD, hW] at V₁ D₁ O₁
  have hm₁ : val32 t₁.mem base M.mo W = m := by
    rw [O₁.val32 (by omega_using [smo]) (by omega_using [mo_le, hnw])]; exact hm
  refine WP.mono (csubD_ok w₁ (M := M) (src := acc) (o := o) (m := m) hn
    (by rw [hD]; omega_using [acc_le]) (by rw [hW]; exact o_le) (by rw [hW]; exact tmp_le) (by rw [hW]; exact mo_le)
    (by rw [hD]; omega_using [acc16]) o16 (by rw [hW]; exact tmp16) (by rw [hW]; exact mo16)
    (by rw [hD, hW]; omega_using [stmp]) (by rw [hW]; exact tmo) (by rw [hD, hW]; omega_using [so])
    (by rw [hW]; exact ot) (by rw [hW]; exact hm₁) hm0 (by rw [hD]; exact D₁) (by rw [hD, V₁]; omega_using [hA, hB]))
    fun t ⟨wt, V, O, R⟩ => ⟨wt, ?_, ?_, R₁.trans R⟩
  · rw [hW] at V; rw [V, hD, V₁]
  · rw [hW] at O
    exact (Outs.of_outside (O₁.mono (o' := acc) (n' := 4 * (4 * W + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)).trans (O.mono (by simp))

end VG.Proof.Mont.Arm.Dyn

end

end


/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the context

The working space's slots (`slot_le`, `slot_sep`), the context of a modulus
`m` (`Context`: the modulus in slot 0 and `m'` in the header), what an
operation on its slots keeps (`OpKeep`), and the multiplication and addition
of slots 6 to 11 (`context_mul_ok`, `context_add_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest)

variable {umaal : Bool}

theorem slot_le {n i j : Nat} (h : i < j) : slot n i + stride n ≤ slot n j := by
  have := Nat.mul_le_mul_right (stride n) h
  simp only [slot, Nat.succ_mul] at *
  omega_using [this]

theorem slot_bound {n i : Nat} (h : i < 12) : slot n i + stride n ≤ contextBytes n := slot_le h

theorem slot_sep {n i j : Nat} (h : i ≠ j) :
    slot n i + stride n ≤ slot n j ∨ slot n j + stride n ≤ slot n i := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact .inl (slot_le h)
  · exact .inr (slot_le h)

theorem slot_header (n i : Nat) : 256 ≤ slot n i := by unfold slot; omega_using []

/-- The accumulator's four slots. -/
theorem slot_acc (n : Nat) : slot n 6 = slot n 2 + 4 * stride n := by simp only [slot]; omega_using []

/-- The context of the modulus `m`: in slot 0 of the working space, with
`m' = -m⁻¹ mod 2¹⁶` in the header, and the working space's offsets below
`2¹⁶`. -/
structure Context (n m : Nat) (base : Addr) (size : Nat) (s : State) : Prop where
  ws : Ws s base size
  size_le : contextBytes n ≤ size
  small : contextBytes n < 2 ^ 16
  n0 : 0 < n
  modulus : val32 s.mem base (slot n 0) (2 * n) = m
  gt_one : 1 < m
  inverse : (m * w32 s.mem base invO + 1) % 2 ^ 16 = 0

/-- The memory an operation on slot `o` may change: the slot, the temporary
slot and the accumulator. -/
abbrev opRanges (n o : Nat) : List (Nat × Nat) := [(slot n o, 8 * n), (slot n 1, 8 * n), (slot n 2, 4 * (8 * n + 2))]

/-- What an operation writing slot `o` keeps: the registers but `dclob`, the
regions, and the memory but `opRanges n o`. -/
structure OpKeep (n : Nat) (base : Addr) (o : Nat) (s t : State) : Prop where
  rest : Rest dclob s t
  mem : Outs base (opRanges n o) s.mem t.mem

/-- The layout of an operation on slots 6 to 11. -/
theorem context_lay {n size o a b : Nat} (hs : contextBytes n ≤ size) (h16 : contextBytes n < 2 ^ 16)
    (ho : 6 ≤ o ∧ o < 12) (ha : 6 ≤ a ∧ a < 12) (hb : 6 ≤ b ∧ b < 12) :
    MulLayD (contextMod n) size invO (accS n) (slot n o) (slot n a) (slot n b) := by
  have b0 := slot_le (n := n) (i := 0) (j := 1) (by decide)
  have b1 := slot_le (n := n) (i := 1) (j := 2) (by decide)
  have b5 := slot_le (n := n) (i := 5) (j := 6) (by decide)
  have b2 := slot_le (n := n) (i := 2) (j := 5) (by decide)
  have bo := slot_bound (n := n) ho.2
  have ba := slot_bound (n := n) ha.2
  have bb := slot_bound (n := n) hb.2
  have lo := slot_le (n := n) (i := 5) (j := o) (by omega_using [ho])
  have la := slot_le (n := n) (i := 5) (j := a) (by omega_using [ha])
  have lb := slot_le (n := n) (i := 5) (j := b) (by omega_using [hb])
  have hd := slot_header n 0
  simp only [stride] at *
  have e6 : slot n 6 = slot n 2 + 4 * (8 * n + 8) := by simp only [slot, stride]; omega_using []
  have e5 : slot n 6 = slot n 5 + (8 * n + 8) := by simp only [slot, stride]; omega_using []
  constructor <;> (try simp only [accLen, digits, Impl.Mont.Arm.words, contextMod, accS, modS, tmpS, invO]) <;> omega_arith

theorem slot_val32 {n o i k : Nat} {base : Addr} {s t : State} (K : Outs base (opRanges n o) s.mem t.mem)
    (hi : i < 12) (hk : k ≤ 2 * n) (hio : i ≠ o) (hi1 : i ≠ 1) (hi2 : 6 ≤ i ∨ i = 0)
    (hn : base.toNat + contextBytes n ≤ 2 ^ 32) :
    val32 t.mem base (slot n i) k = val32 s.mem base (slot n i) k := by
  have so := slot_sep (n := n) hio
  have st := slot_sep (n := n) hi1
  have bi := slot_bound (n := n) hi
  have l6 := slot_le (n := n) (i := 5) (j := 6) (by decide)
  have l2 := slot_le (n := n) (i := 2) (j := 5) (by decide)
  have h0 := slot_le (n := n) (i := 0) (j := 2) (by decide)
  have l6i : 6 ≤ i → slot n 6 ≤ slot n i := fun h => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := slot_le (n := n) h; omega_using [this]
    · rw [h]
  simp only [stride] at *
  have e6 : slot n 6 = slot n 2 + 4 * (8 * n + 8) := by simp only [slot, stride]; omega_using []
  apply K.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hi2 with hi2 | rfl
    · have := l6i hi2
      rcases hr with rfl | rfl | rfl <;> omega_arith
    · rcases hr with rfl | rfl | rfl <;> omega_arith
  · omega_using [hi, hk, hio, hi1, hi2, hn, so, st, bi, l6, l2, h0, l6i, e6]

theorem OpKeep.val32 {n o i k : Nat} {base : Addr} {s t : State} (K : OpKeep n base o s t)
    (hi : i < 12) (hk : k ≤ 2 * n) (hio : i ≠ o) (hi1 : i ≠ 1) (hi2 : 6 ≤ i ∨ i = 0)
    (hn : base.toNat + contextBytes n ≤ 2 ^ 32) :
    val32 t.mem base (slot n i) k = val32 s.mem base (slot n i) k :=
  slot_val32 K.mem hi hk hio hi1 hi2 hn

theorem Context.keep {n size m o : Nat} {base : Addr} {s t : State} (h : Context n m base size s) (ho0 : o ≠ 0)
    (w : Ws t base size) (K : OpKeep n base o s t) : Context n m base size t := by
  have nw : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  refine ⟨w, h.size_le, h.small, h.n0, ?_, h.gt_one, ?_⟩
  · rw [K.val32 (by decide) (Nat.le_refl _) (Ne.symm ho0) (by decide) (.inr rfl) nw]; exact h.modulus
  · have hv : val32 t.mem base 0 1 = val32 s.mem base 0 1 := by
      apply K.mem.val32
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have h0 := slot_header n o
        have h1 := slot_header n 1
        have h2 := slot_header n 2
        rcases hr with rfl | rfl | rfl <;> omega
      · decide
    have e : w32 t.mem base invO = w32 s.mem base invO := by
      simpa only [val32, Nat.mul_zero, Nat.add_zero, invO] using hv
    rw [e]; exact h.inverse

/-- A context, after code that changed only a slot from 6 on. -/
theorem Context.of_slot {n size m i : Nat} {base : Addr} {s t : State} (h : Context n m base size s)
    (w : Ws t base size) (O : Outside base (slot n i) (8 * n) s.mem t.mem) (hi : 6 ≤ i) :
    Context n m base size t := by
  have nw := h.ws.nowrap
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have l0 := slot_le (n := n) (i := 0) (j := i) (by omega_using [hi])
  have hd := slot_header n 0
  have sz := h.size_le
  simp only [stride] at *
  refine ⟨w, h.size_le, h.small, h.n0, ?_, h.gt_one, ?_⟩
  · rw [O.val32 (by omega_using [l0]) (by omega_using [nw, b0, sz])]; exact h.modulus
  · rw [O.w32 (by simp only [invO]; omega_using [l0]) (by decide)]; exact h.inverse

theorem context_mul_ok {n size m o a b : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ho : 6 ≤ o ∧ o < 12) (ha : 6 ≤ a ∧ a < 12) (hb : 6 ≤ b ∧ b < 12)
    (hB : val32 s.mem base (slot n b) (2 * n) < m) :
    WP isa (Dynamic.mul umaal (contextMod n) invO (accS n) (slot n o) (slot n a) (slot n b)) s fun t =>
      Context n m base size t ∧ OpKeep n base o s t ∧
      val32 t.mem base (slot n o) (2 * n) < m ∧
      val32 t.mem base (slot n o) (2 * n) * 2 ^ (64 * n) % m =
        val32 s.mem base (slot n a) (2 * n) * val32 s.mem base (slot n b) (2 * n) % m := by
  refine WP.mono (mul_ok h.ws h.n0 (context_lay h.size_le h.small ho ha hb) (m := m) h.modulus h.inverse hB)
    fun t ⟨w, lt, V, O, R⟩ => ?_
  have K : OpKeep n base o s t := ⟨R, by
    simpa only [Impl.Mont.Arm.words, contextMod, tmpS, accS, show 4 * (2 * n) = 8 * n by omega_using [],
      show 4 * (4 * (2 * n) + 2) = 4 * (8 * n + 2) by omega_using []] using O⟩
  exact ⟨h.keep (by omega_using [ho]) w K, K, lt, by rw [show 64 * n = 32 * (2 * n) by omega_using []]; exact V⟩

theorem context_add_ok {n size m o a b : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ho : 6 ≤ o ∧ o < 12) (ha : 6 ≤ a ∧ a < 12) (hb : 6 ≤ b ∧ b < 12)
    (hA : val32 s.mem base (slot n a) (2 * n) < m) (hB : val32 s.mem base (slot n b) (2 * n) < m) :
    WP isa (addD (contextMod n) (accS n) (slot n o) (slot n a) (slot n b)) s fun t =>
      Context n m base size t ∧ OpKeep n base o s t ∧
      val32 t.mem base (slot n o) (2 * n) =
        (val32 s.mem base (slot n a) (2 * n) + val32 s.mem base (slot n b) (2 * n)) % m := by
  refine WP.mono (addD_ok h.ws h.n0 (context_lay h.size_le h.small ho ha hb) (m := m) h.modulus
    (by have := h.gt_one; omega_using [hA]) hA hB) fun t ⟨w, V, O, R⟩ => ?_
  have K : OpKeep n base o s t := ⟨R, by
    simpa only [Impl.Mont.Arm.words, contextMod, tmpS, accS, show 4 * (2 * n) = 8 * n by omega_using [],
      show 4 * (4 * (2 * n) + 2) = 4 * (8 * n + 2) by omega_using []] using O⟩
  exact ⟨h.keep (by omega_using [ho]) w K, K, V⟩

end VG.Proof.Mont.Arm.Dyn
