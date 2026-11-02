module

import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.X25519.RISCV64.R64.Mul
import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.Ed25519.Word64
public import VerifiedGarbage.Proof.Ed25519.ScalarWord

/-!
# Ed25519 on RISCV64: a 64-byte integer modulo `L`

`scalarReduceEngine` reads the 64 bytes at `t3` a word at a time, from the
top, each folded into the remainder in `a4`–`a7` (`scalarWord_ok`), and
stores the integer modulo `L` at `SR` (`engine_ok`). It writes no memory
before that store, so the input may be anywhere readable.

`wordFold` turns the remainder `r < L` and the next word `w` in `a2` into
`v mod L`, for `v = 2^64 r + w = h 2^252 + l`: `l - t` for `t = h c` when
`t ≤ l`, `l + L - t` otherwise (`fold_cases`). Each of its four blocks is
checked against the numbers it computes (`wordFold_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Ed25519.RISCV64 VG.Proof.Ed25519
open VG.Proof.X25519.RISCV64
open VG.Proof.Ed25519.Word64 (val4 val4_lt)
open VG.Spec.Ed25519 (L decodeLE bytesAt)
open VG.Proof.X448.RISCV64.R64 (dw ew sd_ok dw_write_self dw_write_other)

section
/-! ## Numbers -/

/-- One word folded in: `t = h c < L`, and `l - t` or `l + L - t` is `v mod L`. -/
theorem fold_cases (r w : Nat) (hr : r < L) (hw : w < 2 ^ 64) :
    (w + 2 ^ 64 * r) / 2 ^ 252 * cL < L ∧
    (if (w + 2 ^ 64 * r) / 2 ^ 252 * cL ≤ (w + 2 ^ 64 * r) % 2 ^ 252 then
        (w + 2 ^ 64 * r) % 2 ^ 252 - (w + 2 ^ 64 * r) / 2 ^ 252 * cL
      else (w + 2 ^ 64 * r) % 2 ^ 252 + L - (w + 2 ^ 64 * r) / 2 ^ 252 * cL) =
      (w + 2 ^ 64 * r) % L := by
  rw [L_eq] at hr ⊢
  have hc65 : 2 ^ 65 * cL < 2 ^ 252 := by decide
  generalize hv : w + 2 ^ 64 * r = v
  have hv' : v < 2 ^ 317 := by
    rw [← hv]; have : cL < 2 ^ 125 := by decide
    omega_arith
  have hh : v / 2 ^ 252 < 2 ^ 65 := by omega_arith
  have hd := Nat.div_add_mod v (2 ^ 252)
  have hl := Nat.mod_lt v (show 0 < 2 ^ 252 by decide)
  generalize v / 2 ^ 252 = h at hh hd
  generalize v % 2 ^ 252 = l at hd hl ⊢
  subst hd
  have hx : h * cL < 2 ^ 252 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt hh)) hc65
  refine ⟨by omega_arith, ?_⟩
  by_cases ht : h * cL ≤ l
  · simp only [ht, ↓reduceIte]
    rw [show 2 ^ 252 * h + l = (l - h * cL) + h * (2 ^ 252 + cL) by rw [Nat.mul_add]; omega_arith,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega_arith)]
  · simp only [ht, ↓reduceIte]
    obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by
      rcases h with _ | h
      · simp at ht
      · omega_arith⟩
    have e1 : (g + 1) * cL = g * cL + cL := Nat.succ_mul _ _
    have e2 : g * (2 ^ 252 + cL) = g * 2 ^ 252 + g * cL := Nat.mul_add _ _ _
    rw [e1] at hx ht
    rw [show 2 ^ 252 * (g + 1) + l = (l + (2 ^ 252 + cL) - (g + 1) * cL) + g * (2 ^ 252 + cL) by
          rw [e2, e1]; omega_arith,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by rw [e1]; omega_arith)]

theorem c_limbs : orderLo.toNat + 2 ^ 64 * orderHi.toNat = cL := by decide

theorem orderHi_lt : orderHi.toNat < 2 ^ 61 := by decide

/-! ## The blocks -/

variable {s : State}

/-- The remainder in `a4`–`a7`. -/
abbrev R4 (s : State) : Nat := val4 (s.gpr .a4) (s.gpr .a5) (s.gpr .a6) (s.gpr .a7)

set_option linter.unusedSimpArgs false in
theorem foldPrep_ok :
    WP isa (.block foldPrep) s fun t =>
      (t.gpr .t0).toNat = (s.gpr .a6).toNat / 2 ^ 60 + 16 * ((s.gpr .a7).toNat % 2 ^ 60) ∧
      (t.gpr .t1).toNat = (s.gpr .a7).toNat / 2 ^ 60 ∧
      t.gpr .a4 = s.gpr .a2 ∧ t.gpr .a5 = s.gpr .a4 ∧ t.gpr .a6 = s.gpr .a5 ∧
      (t.gpr .a7).toNat = (s.gpr .a6).toNat % 2 ^ 60 ∧
      Keeps [.t0, .t1, .a4, .a5, .a6, .a7] s t := by
  apply WP.of_runBlock
  simp only [foldPrep, runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 60 < 64 by decide),
    exec_shift_d (show 4 < 64 by decide), exec_logic, exec_addi (show imm12 0 by decide),
    RegUpd.gpr_write, BitVec.ofInt_ofNat, BitVec.add_zero, reduceCtorEq,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨shr_or_shl _ _, shr60 _, trivial, trivial, trivial, shl_shr _, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2,
    ite_false]

/-- A word times a bit, `h ≤ 1`, does not wrap. -/
theorem mul_bit (h v : BitVec 64) (hh : h.toNat ≤ 1) : (h * v).toNat = h.toNat * v.toNat := by
  rw [BitVec.toNat_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hh with e | e <;> rw [e]
  · simp
  · rw [Nat.one_mul, Nat.mod_eq_of_lt v.isLt]

/-- What `foldMul` computes: `(h₀ + 2^64 h₁) (c₀ + 2^64 c₁)` in three words. -/
theorem mul_value (x h c0 c1 : BitVec 64) (hh : h.toNat ≤ 1) (hc1 : c1.toNat < 2 ^ 61) :
    (x * c0).toNat +
      2 ^ 64 * (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64) + x * c1 + h * c0).toNat +
      2 ^ 128 * (BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64) +
        (if BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64) + x * c1 < x * c1 then 1 else 0) +
        (if BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64) + x * c1 + h * c0 < h * c0 then 1 else 0) +
        h * c1).toNat =
      (x.toNat + 2 ^ 64 * h.toNat) * (c0.toNat + 2 ^ 64 * c1.toNat) := by
  have m0 := mul_words x c0
  have m1 := mul_words x c1
  generalize BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64) = p1 at *
  have ca := carry p1 (x * c1)
  have ca' := carry (p1 + x * c1) (h * c0)
  have k1 := carry_le (p1 + x * c1 < x * c1)
  have k2 := carry_le (p1 + x * c1 + h * c0 < h * c0)
  have hm0 := mul_bit h c0 hh
  have hm1 := mul_bit h c1 hh
  have hx := x.isLt
  have hq : x.toNat * c1.toNat < 2 ^ 64 * 2 ^ 61 := Nat.mul_lt_mul_of_lt_of_lt hx hc1
  have hq1 : (BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64)).toNat < 2 ^ 61 := by
    rw [BitVec.toNat_ofNat]; omega_arith
  have hhc : h.toNat * c1.toNat < 2 ^ 61 :=
    Nat.lt_of_le_of_lt (by have := Nat.mul_le_mul_right c1.toNat hh; omega_arith) hc1
  generalize BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64) = q1 at *
  generalize (if p1 + x * c1 < x * c1 then (1 : BitVec 64) else 0) = k at *
  generalize (if p1 + x * c1 + h * c0 < h * c0 then (1 : BitVec 64) else 0) = k' at *
  have htop : (q1 + k + k' + h * c1).toNat = q1.toNat + k.toNat + k'.toNat + h.toNat * c1.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, hm1]; omega_arith
  rw [htop]
  rw [hm0] at ca'
  have e : (x.toNat + 2 ^ 64 * h.toNat) * (c0.toNat + 2 ^ 64 * c1.toNat) =
      x.toNat * c0.toNat + 2 ^ 64 * (x.toNat * c1.toNat) + 2 ^ 64 * (h.toNat * c0.toNat) +
        2 ^ 128 * (h.toNat * c1.toNat) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_left_comm x.toNat (2 ^ 64),
      Nat.mul_assoc (2 ^ 64) h.toNat c0.toNat, Nat.mul_mul_mul_comm (2 ^ 64) h.toNat (2 ^ 64) c1.toNat]
    omega_arith
  rw [e]
  generalize x.toNat * c0.toNat = X0 at *
  generalize x.toNat * c1.toNat = X1 at *
  generalize h.toNat * c0.toNat = H0 at *
  generalize h.toNat * c1.toNat = H1 at *
  omega_arith

set_option linter.unusedSimpArgs false in
/-- `foldMul`: `t = (h₀ + 2^64 h₁) c` into `t2`, `a1`, `t0`, for `h₁ ≤ 1` in `t1`. -/
theorem foldMul_ok (h5 : s.gpr .t5 = orderLo) (h6 : s.gpr .t6 = orderHi) (hh : (s.gpr .t1).toNat ≤ 1) :
    WP isa (.block foldMul) s fun t =>
      (t.gpr .t2).toNat + 2 ^ 64 * (t.gpr .a1).toNat + 2 ^ 128 * (t.gpr .t0).toNat =
        ((s.gpr .t0).toNat + 2 ^ 64 * (s.gpr .t1).toNat) * cL ∧
      Keeps [.t2, .a1, .a2, .t0] s t := by
  apply WP.of_runBlock
  simp only [foldMul, runBlock_cons, runStep_some, runBlock_nil, exec_mul, exec_mulhu, exec_add,
    exec_sltu, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [← c_limbs, ← h5, ← h6]
    exact mul_value _ _ _ _ hh (by rw [h6]; exact orderHi_lt)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- A subtraction's borrow, as `sltu` computes it from the operands. -/
theorem sub_lt (r x : BitVec 64) :
    (r - x).toNat + x.toNat = r.toNat + 2 ^ 64 * (if r < x then (1 : BitVec 64) else 0).toNat := by
  have := r.isLt; have := x.isLt
  rw [BitVec.toNat_sub]
  by_cases h : r < x
  · simp only [h, ↓reduceIte]
    rw [BitVec.lt_def] at h
    show _ = _ + 2 ^ 64 * 1
    omega_arith
  · simp only [h, ↓reduceIte]
    rw [BitVec.lt_def] at h
    show _ = _ + 2 ^ 64 * 0
    omega_arith

/-- Word `k` of a subtraction with the borrow `b` in: the borrow out is one of the two `sltu`s. -/
theorem sub_borrow (r x b : BitVec 64) (hb : b.toNat ≤ 1) :
    (r - x - b).toNat + x.toNat + b.toNat =
      r.toNat + 2 ^ 64 * ((if r < x then (1 : BitVec 64) else 0) |||
        (if r - x < b then (1 : BitVec 64) else 0)).toNat ∧
    ((if r < x then (1 : BitVec 64) else 0) ||| (if r - x < b then (1 : BitVec 64) else 0)).toNat ≤ 1 := by
  have e1 := sub_lt r x
  have e2 := sub_lt (r - x) b
  have := (r - x).isLt
  by_cases h1 : r < x <;> by_cases h2 : r - x < b <;> simp only [h1, h2, ↓reduceIte] at e1 e2 ⊢
  · -- both: impossible, `r - x` wrapped so it is at least 1 ≥ b
    exfalso
    rw [BitVec.lt_def] at h2
    have : (0 : BitVec 64).toNat = 0 := rfl
    have : (1 : BitVec 64).toNat = 1 := rfl
    omega_arith
  all_goals
    have o1 : (1 : BitVec 64).toNat = 1 := rfl
    have o0 : (0 : BitVec 64).toNat = 0 := rfl
    have o10 : ((1 : BitVec 64) ||| 0) = 1 := by decide
    have o01 : ((0 : BitVec 64) ||| 1) = 1 := by decide
    have o00 : ((0 : BitVec 64) ||| 0) = 0 := by decide
    simp only [o10, o01, o00, o1, o0] at e1 e2 ⊢
    exact ⟨by omega_arith, by decide⟩

set_option linter.unusedSimpArgs false in
/-- `foldSub`: `l - t` into `a4`–`a7`, for `t` in `t2`, `a1`, `t0`, its borrow into `t1`. -/
theorem foldSub_ok :
    WP isa (.block foldSub) s fun t =>
      R4 t + ((s.gpr .t2).toNat + 2 ^ 64 * (s.gpr .a1).toNat + 2 ^ 128 * (s.gpr .t0).toNat) =
        R4 s + 2 ^ 256 * (t.gpr .t1).toNat ∧ (t.gpr .t1).toNat ≤ 1 ∧
      Keeps [.a4, .a5, .a6, .a7, .a2, .t1, .t2] s t := by
  apply WP.of_runBlock
  simp only [foldSub, subBorrow, R4, val4, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec_sub, exec_sltu, exec_logic, RegUpd.gpr_write, reduceCtorEq, ite_true,
    ite_false, Option.some.injEq, exists_eq_left']
  have e0 := sub_lt (s.gpr .a4) (s.gpr .t2)
  have b0 : (if s.gpr .a4 < s.gpr .t2 then (1 : BitVec 64) else 0).toNat ≤ 1 := carry_le _
  obtain ⟨e1, b1⟩ := sub_borrow (s.gpr .a5) (s.gpr .a1) _ b0
  obtain ⟨e2, b2⟩ := sub_borrow (s.gpr .a6) (s.gpr .t0) _ b1
  generalize (if s.gpr .a4 < s.gpr .t2 then (1 : BitVec 64) else 0) = k0 at *
  generalize ((if s.gpr .a5 < s.gpr .a1 then (1 : BitVec 64) else 0) |||
    (if s.gpr .a5 - s.gpr .a1 < k0 then (1 : BitVec 64) else 0)) = k1 at *
  generalize ((if s.gpr .a6 < s.gpr .t0 then (1 : BitVec 64) else 0) |||
    (if s.gpr .a6 - s.gpr .t0 < k1 then (1 : BitVec 64) else 0)) = k2 at *
  have e3 := sub_lt (s.gpr .a7) k2
  refine ⟨?_, carry_le _, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · generalize (if s.gpr .a7 < k2 then (1 : BitVec 64) else 0) = k3 at *
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2, ite_false]

/-- A constant under the mask `0 - b` of a bit. -/
theorem and_mask (c b : BitVec 64) (hb : b.toNat ≤ 1) :
    (c &&& (BitVec.ofInt 64 0 - b)).toNat = b.toNat * c.toNat := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with e | e
  · have : b = 0 := BitVec.eq_of_toNat_eq (by rw [e]; rfl)
    subst this; rw [e, Nat.zero_mul]; simp
  · have : b = 1 := BitVec.eq_of_toNat_eq (by rw [e]; rfl)
    subst this
    rw [e, Nat.one_mul, show BitVec.ofInt 64 0 - (1 : BitVec 64) = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes]

/-- A bit shifted up by 60. -/
theorem bit_shl60 (b : BitVec 64) (hb : b.toNat ≤ 1) : (b <<< 60).toNat = 2 ^ 60 * b.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with e | e <;> rw [e] <;> decide

/-- Two additions into one word, the carries of each `or`-ed: they cannot both be 1. -/
theorem add_carry2 (a k y : BitVec 64) (hk : k.toNat ≤ 1) :
    (a + k + y).toNat + 2 ^ 64 * ((if a + k < k then (1 : BitVec 64) else 0) |||
      (if a + k + y < y then (1 : BitVec 64) else 0)).toNat = a.toNat + k.toNat + y.toNat ∧
    ((if a + k < k then (1 : BitVec 64) else 0) |||
      (if a + k + y < y then (1 : BitVec 64) else 0)).toNat ≤ 1 := by
  have e1 := carry a k
  have e2 := carry (a + k) y
  have := (a + k).isLt
  have o1 : (1 : BitVec 64).toNat = 1 := rfl
  have o0 : (0 : BitVec 64).toNat = 0 := rfl
  have o10 : ((1 : BitVec 64) ||| 0) = 1 := by decide
  have o01 : ((0 : BitVec 64) ||| 1) = 1 := by decide
  have o00 : ((0 : BitVec 64) ||| 0) = 0 := by decide
  by_cases h1 : a + k < k <;> by_cases h2 : a + k + y < y <;>
    simp only [h1, h2, ↓reduceIte, o10, o01, o00, o1, o0] at e1 e2 ⊢
  · exfalso
    rw [BitVec.lt_def] at h2
    have : (a + k).toNat = 0 := by omega_arith
    rw [BitVec.toNat_add, this, Nat.zero_add, Nat.mod_eq_of_lt y.isLt] at h2
    omega_arith
  all_goals exact ⟨by omega_arith, by decide⟩

set_option linter.unusedSimpArgs false in
/-- `foldAdd`: `L` added to `a4`–`a7` under the mask of the bit in `t1`. -/
theorem foldAdd_ok (h5 : s.gpr .t5 = orderLo) (h6 : s.gpr .t6 = orderHi) (hb : (s.gpr .t1).toNat ≤ 1) :
    WP isa (.block foldAdd) s fun t =>
      R4 t = (R4 s + (s.gpr .t1).toNat * L) % 2 ^ 256 ∧
      Keeps [.t2, .a1, .a2, .a4, .a5, .a6, .a7, .t1] s t := by
  apply WP.of_runBlock
  simp only [foldAdd, R4, val4, runBlock_cons, runStep_some, runBlock_nil, exec_li (show imm12 0 by decide),
    exec_sub, exec_add, exec_sltu, exec_logic, exec_shift_d (show 60 < 64 by decide),
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have m0 := and_mask (s.gpr .t5) (s.gpr .t1) hb
    have m1 := and_mask (s.gpr .t6) (s.gpr .t1) hb
    have hs := bit_shl60 (s.gpr .t1) hb
    generalize s.gpr .t5 &&& (BitVec.ofInt 64 0 - s.gpr .t1) = x0 at *
    generalize s.gpr .t6 &&& (BitVec.ofInt 64 0 - s.gpr .t1) = x1 at *
    have c0 := carry (s.gpr .a4) x0
    have k0 := carry_le (s.gpr .a4 + x0 < x0)
    generalize (if s.gpr .a4 + x0 < x0 then (1 : BitVec 64) else 0) = k at *
    obtain ⟨c1, k1⟩ := add_carry2 (s.gpr .a5) k x1 k0
    generalize ((if s.gpr .a5 + k < k then (1 : BitVec 64) else 0) |||
      (if s.gpr .a5 + k + x1 < x1 then (1 : BitVec 64) else 0)) = k' at *
    have c2 := carry (s.gpr .a6) k'
    generalize (if s.gpr .a6 + k' < k' then (1 : BitVec 64) else 0) = k'' at *
    rw [h5] at m0; rw [h6] at m1
    have hL : L = orderLo.toNat + 2 ^ 64 * orderHi.toNat + 2 ^ 252 := by rw [c_limbs, L_eq]; omega_arith
    rw [hL, BitVec.toNat_add (s.gpr .a7 + k''), BitVec.toNat_add (s.gpr .a7), hs]
    have := (s.gpr .a7).isLt; have := (s.gpr .t1).isLt; have := carry_le (s.gpr .a6 + k' < k')
    have ho : orderLo.toNat < 2 ^ 64 := orderLo.isLt
    have hh := orderHi_lt
    generalize orderLo.toNat = C0 at *
    generalize orderHi.toNat = C1 at *
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with e | e <;> rw [e] at m0 m1 hs ⊢ <;>
      simp only [Nat.zero_mul, Nat.one_mul, Nat.mul_zero] at m0 m1 ⊢ <;> omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

/-- The registers `wordFold` writes. -/
abbrev foldClob : List Reg := [.t0, .t1, .t2, .a1, .a2, .a4, .a5, .a6, .a7]

/-- **One word**: the remainder `r < L` in `a4`–`a7` and the next word `w` in
`a2` become `(w + 2^64 r) mod L`. -/
theorem wordFold_ok (h5 : s.gpr .t5 = orderLo) (h6 : s.gpr .t6 = orderHi) (hr : R4 s < L) :
    WP isa (.block wordFold) s fun t =>
      R4 t = ((s.gpr .a2).toNat + 2 ^ 64 * R4 s) % L ∧ Keeps foldClob s t := by
  unfold wordFold
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono foldPrep_ok fun s1 ⟨e0, e1, e4, e5, e6, e7, k1⟩ => ?_
  have h5' : s1.gpr .t5 = orderLo := by rw [k1.gpr', h5]
  have h6' : s1.gpr .t6 = orderHi := by rw [k1.gpr', h6]
  have hL : L < 2 ^ 253 := by decide
  have h7 : (s.gpr .a7).toNat < 2 ^ 61 := by
    simp only [R4, val4] at hr
    omega_arith
  have hh : (s1.gpr .t1).toNat ≤ 1 := by rw [e1]; omega_arith
  refine WP.mono (foldMul_ok h5' h6' hh) fun s2 ⟨m, k2⟩ => ?_
  refine WP.mono foldSub_ok fun s3 ⟨d, b, k3⟩ => ?_
  have h5'' : s3.gpr .t5 = orderLo := by rw [k3.gpr', k2.gpr', h5']
  have h6'' : s3.gpr .t6 = orderHi := by rw [k3.gpr', k2.gpr', h6']
  refine WP.mono (foldAdd_ok h5'' h6'' b) fun s4 ⟨a, k4⟩ => ⟨?_, ?_⟩
  · -- the numbers
    have r2 : R4 s2 = R4 s1 := by
      simp only [R4]
      rw [k2.gpr' (r := .a4), k2.gpr' (r := .a5), k2.gpr' (r := .a6), k2.gpr' (r := .a7)]
    have t2 : (s2.gpr .t2).toNat + 2 ^ 64 * (s2.gpr .a1).toNat + 2 ^ 128 * (s2.gpr .t0).toNat =
        ((s.gpr .a2).toNat + 2 ^ 64 * R4 s) / 2 ^ 252 * cL := by
      rw [m, e0, e1]
      congr 1
      simp only [R4, val4]
      omega_arith
    have l1 : R4 s1 = ((s.gpr .a2).toNat + 2 ^ 64 * R4 s) % 2 ^ 252 := by
      simp only [R4, val4] at e7 ⊢
      rw [e4, e5, e6, e7]
      omega_arith
    obtain ⟨hT, hc⟩ := fold_cases (R4 s) (s.gpr .a2).toNat hr (s.gpr .a2).isLt
    rw [← hc, a]
    rw [r2, t2, l1] at d
    have hd : R4 s3 < 2 ^ 256 := val4_lt (s3.gpr .a4) (s3.gpr .a5) (s3.gpr .a6) (s3.gpr .a7)
    have hl := Nat.mod_lt ((s.gpr .a2).toNat + 2 ^ 64 * R4 s) (show 0 < 2 ^ 252 by decide)
    generalize ((s.gpr .a2).toNat + 2 ^ 64 * R4 s) / 2 ^ 252 * cL = T at *
    generalize ((s.gpr .a2).toNat + 2 ^ 64 * R4 s) % 2 ^ 252 = l at *
    generalize R4 s3 = D at *
    generalize (s3.gpr .t1).toNat = B at *
    have hLv : L = 2 ^ 252 + 27742317777372353535851937790883648493 := by decide
    rw [hLv] at hT a ⊢
    clear e0 e1 e4 e5 e6 e7 m t2 l1 r2 hh h7 hL hr
    by_cases ht : T ≤ l
    · simp only [ht, ↓reduceIte]
      obtain rfl : B = 0 := by omega_arith
      omega_arith
    · simp only [ht, ↓reduceIte]
      obtain rfl : B = 1 := by omega_arith
      omega_arith
  · exact ((((k1.mono (rs' := foldClob)).trans (k2.mono (rs' := foldClob))).trans
      (k3.mono (rs' := foldClob))).trans (k4.mono (rs' := foldClob))).mono

end

/-- What the scalar code writes: the remainder (and the candidate of the check
that a scalar is below `L`, `SD`, after it). -/
abbrev RD (b : Addr) : Region := ⟨b + BitVec.ofNat 64 SR, 64⟩

/-- The registers one word's fold writes. -/
abbrev wordClob : List Reg := [.a1, .a2, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t4]

/-- The registers the engine writes. -/
abbrev engClob : List Reg := [.a1, .a2, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t4, .t5, .t6]

theorem Keeps.toRest {rs : List Reg} {s s' : State} (h : Keeps rs s s') : Rest rs s s' :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

section
variable {b : Addr}

set_option linter.unusedSimpArgs false in
theorem zero4_ok {s : State} :
    WP isa (.block [.li .a4 0, .li .a5 0, .li .a6 0, .li .a7 0, .li .t4 64]) s fun t =>
      R4 t = 0 ∧ t.gpr .t4 = BitVec.ofNat 64 64 ∧ Keeps [.a4, .a5, .a6, .a7, .t4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_li (show imm12 0 by decide),
    exec_li (show imm12 64 by decide), R4, Word64.val4, RegUpd.gpr_write, reduceCtorEq, ite_true,
    ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem init_ok {s : State} :
    WP isa (.block scalarInit) s fun t =>
      R4 t = 0 ∧ t.gpr .t4 = BitVec.ofNat 64 64 ∧ t.gpr .t5 = orderLo ∧ t.gpr .t6 = orderHi ∧
      Keeps [.a4, .a5, .a6, .a7, .t4, .t0, .t5, .t6] s t := by
  unfold scalarInit
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono zero4_ok fun s1 ⟨r1, t1, k1⟩ => ?_
  refine WP.mono (Words64.movImm64_ok (by decide) orderLo) fun s2 ⟨g2, o2, m2, d2, w2, p2⟩ => ?_
  refine WP.mono (Words64.movImm64_ok (by decide) orderHi) fun s3 ⟨g3, o3, m3, d3, w3, p3⟩ => ?_
  have k3 : Keeps [.t0, .t5, .t6] s1 s3 :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [o3 r hr.2.2 hr.1, o2 r hr.2.1 hr.1], by rw [m3, m2], by rw [d3, d2], by rw [w3, w2],
      by rw [p3, p2]⟩
  refine ⟨?_, ?_, by rw [o3 _ (by decide) (by decide), g2], g3,
    (k1.trans k3).mono (rs' := [.a4, .a5, .a6, .a7, .t4, .t0, .t5, .t6])⟩
  · rw [← r1]; simp only [R4]
    rw [k3.gpr' (r := .a4), k3.gpr' (r := .a5), k3.gpr' (r := .a6), k3.gpr' (r := .a7)]
  · rw [k3.gpr', t1]

/-- One word: `t4` counted down by 8, the word at `t3 + t4` folded into the remainder. -/
theorem scalarWord_ok {s : State} {p : Addr} (h3 : s.gpr .t3 = p) {k : Nat}
    (h4 : s.gpr .t4 = BitVec.ofNat 64 (8 * (k + 1))) (h5 : s.gpr .t5 = orderLo)
    (h6 : s.gpr .t6 = orderHi) (hin : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * k)) 8)
    (hr : R4 s < L) :
    WP isa (.block scalarWord) s fun t =>
      R4 t = ((s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat + 2 ^ 64 * R4 s) % L ∧
      t.gpr .t4 = BitVec.ofNat 64 (8 * k) ∧ Keeps wordClob s t := by
  unfold scalarWord scalarLoad
  simp only [List.cons_append]
  refine wp_subi (by decide) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e4 : s1.gpr .t4 = BitVec.ofNat 64 (8 * k) := by
    rw [u1.gpr, h4, show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have e1 : s2.gpr .a1 = p + BitVec.ofNat 64 (8 * k) := by
    rw [u2.gpr, u1.other _ (by decide), h3, e4]
  refine WP.append (Words64.loadLE64_ok (d := .a2) (tmp := .t0) (tmp2 := .t1) (n := .a1) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [e1, BitVec.add_zero, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin)) fun s3 u3 => ?_
  have k3 : Keeps [.t4, .a1, .a2, .t0, .t1] s s3 :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u3.other r hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2, u2.other r hr.2.1, u1.other r hr.1],
      by rw [u3.mem, u2.mem, u1.mem], by rw [u3.rd, u2.rd, u1.rd], by rw [u3.wr, u2.wr, u1.wr],
      by rw [u3.sp, u2.sp, u1.sp]⟩
  have r3 : R4 s3 = R4 s := by
    simp only [R4]
    rw [k3.gpr' (r := .a4), k3.gpr' (r := .a5), k3.gpr' (r := .a6), k3.gpr' (r := .a7)]
  refine WP.mono (wordFold_ok (by rw [k3.gpr', h5]) (by rw [k3.gpr', h6]) (by rw [r3]; exact hr))
    fun t ⟨vt, kt⟩ => ⟨?_, by rw [kt.gpr', u3.other _ (by decide) (by decide) (by decide),
      u2.other _ (by decide), e4], (k3.trans kt).mono (rs' := wordClob)⟩
  rw [vt, r3, u3.gpr, e1, BitVec.add_zero, u2.mem, u1.mem]

/-- The remainder, stored at `SR`. -/
theorem store_ok {s : State} (hc : Ctx b s) :
    WP isa (.block scalarStore) s fun t =>
      V t.mem b SR = R4 s ∧ Rest [] s t ∧ Frame [⟨b + BitVec.ofNat 64 SR, 32⟩] s.mem t.mem := by
  unfold scalarStore
  have hS : SR = 160 := rfl
  refine sd_ok hc (by omega) (by omega) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := ⟨by rw [u1.gpr, hc.a3], hc.al, by rw [u1.wr]; exact hc.wr⟩
  refine sd_ok hc1 (by omega) (by omega) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := ⟨by rw [u2.gpr, hc1.a3], hc.al, by rw [u2.wr]; exact hc1.wr⟩
  refine sd_ok hc2 (by omega) (by omega) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := ⟨by rw [u3.gpr, hc2.a3], hc.al, by rw [u3.wr]; exact hc2.wr⟩
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [R64.V_eq4]
    simp only [R64.val4, ew, R4, Word64.val4, u4.mem, u3.mem, u2.mem, u1.mem, u3.gpr, u2.gpr, u1.gpr, hS,
      Nat.reduceMul, Nat.reduceAdd]
    simp (disch := omega) only [dw_write_self, dw_write_other]
    omega_arith
  · exact ⟨fun r _ => by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr], by rw [u4.rd, u3.rd, u2.rd, u1.rd],
      by rw [u4.wr, u3.wr, u2.wr, u1.wr], by rw [u4.sp, u3.sp, u2.sp, u1.sp]⟩
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
    simp only [hS, Nat.reduceAdd]
    have hw : ∀ d, 160 ≤ d → d + 8 ≤ 192 → ∀ {m m' : Mem}, Frame [⟨b + BitVec.ofNat 64 160, 32⟩] m m' →
        ∀ v : BitVec 64, Frame [⟨b + BitVec.ofNat 64 160, 32⟩] m (m'.writeW (b + BitVec.ofNat 64 d) v) :=
      fun d h1 h2 _ _ f v => f.writeW (List.mem_singleton_self _) _
        (Offset.contains b h1 (by omega) (by omega))
    exact hw 184 (by omega) (by omega) (hw 176 (by omega) (by omega) (hw 168 (by omega) (by omega)
      (hw 160 (by omega) (by omega) (Frame.refl _ _) _) _) _) _

theorem mod_inner (w a : Nat) : (w + 2 ^ 64 * (a % L)) % L = (w + 2 ^ 64 * a) % L := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- After the words from `n` up: the remainder of the integer they make. -/
structure EngInv (p : Addr) (s0 : State) (n : Nat) (t : State) : Prop where
  le : n ≤ 8
  keeps : Keeps engClob s0 t
  t4 : t.gpr .t4 = BitVec.ofNat 64 (8 * n)
  t5 : t.gpr .t5 = orderLo
  t6 : t.gpr .t6 = orderHi
  val : R4 t = decodeLE (bytesAt s0.mem (p + BitVec.ofNat 64 (8 * n)) (64 - 8 * n)) % L

/-- **The 64 bytes at `t3`**, modulo `L`, into `SR`. -/
theorem engine_ok {s : State} (hc : Ctx b s) {p : Addr} (h14 : s.gpr .t3 = p)
    (hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa scalarReduceEngine s fun t =>
      Rest engClob s t ∧ Frame [RD b] s.mem t.mem ∧
      V t.mem b SR = decodeLE (bytesAt s.mem p 64) % L := by
  unfold scalarReduceEngine
  have hS : SR = 160 := rfl
  refine WP.seq (WP.mono init_ok fun s1 ⟨r1, t4, t5, t6, k1⟩ => ?_)
  have i1 : EngInv p s 8 s1 := ⟨Nat.le_refl _, k1.mono (rs' := engClob), t4, t5, t6, by
      rw [r1, show 64 - 8 * 8 = 0 from rfl]; rfl⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) (fun n t => 1 ≤ n ∧ EngInv p s n t)
    (Q := fun t => EngInv p s 0 t) ?_ 8 s1 ⟨by decide, i1⟩) fun t ht => ?_)
  · intro n t ⟨hn, h⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : k < 8 := by have := h.le; omega
    have hr : R4 t < L := by rw [h.val]; exact Nat.mod_lt _ order_pos
    refine WP.mono (scalarWord_ok (p := p) (k := k) (by rw [h.keeps.gpr', h14]) h.t4 h.t5 h.t6
      (by rw [h.keeps.2.2.1, h.keeps.2.2.2.1]; exact hin k hk) hr) fun t' ⟨vt, r4, kt⟩ => ?_
    have hm : t.mem = s.mem := h.keeps.2.1
    have hv : R4 t' = decodeLE (bytesAt s.mem (p + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) % L := by
      rw [vt, h.val, hm, words_step _ _ _ hk, mod_inner]
    have i' : EngInv p s k t' := ⟨by omega, (h.keeps.trans (kt.mono (rs' := engClob))).mono, r4,
      by rw [kt.gpr', h.t5], by rw [kt.gpr', h.t6], hv⟩
    rw [eval_nonzero, r4]
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by decide, i'⟩
    · have h8 : 8 * k ≠ 0 := by omega
      exact .inr ⟨by rw [ofNat_ne_zero (by omega)]; simp [h8], k, by omega, ⟨by omega, i'⟩⟩
  · refine WP.mono (store_ok (hc.of_rest (Keeps.toRest ht.keeps) (by decide))) fun u ⟨vu, ru, fu⟩ =>
      ⟨(Keeps.toRest ht.keeps).trans (ru.mono (by decide)), ?_, ?_⟩
    · rw [← ht.keeps.2.1]
      exact fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩
    · rw [vu, ht.val, Nat.mul_zero, Nat.sub_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]

end

end VG.Proof.Ed25519.RISCV64
