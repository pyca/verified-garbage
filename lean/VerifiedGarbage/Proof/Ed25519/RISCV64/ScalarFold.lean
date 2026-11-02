module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.Ed25519.Word64
public import VerifiedGarbage.Proof.Ed25519.ScalarWord
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Ed25519 scalar reduction on RISC-V: one word

`wordFold` turns the remainder `r < L` in `a4`–`a7` and the next word `w` in
`a2` into `v mod L`, for `v = 2^64 r + w = h 2^252 + l`: `l - t` for `t = h c`
when `t ≤ l`, `l + L - t` otherwise (`fold_cases`). Each of its four blocks
is checked against the numbers it computes.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Ed25519.RISCV64 VG.Proof.Ed25519
open VG.Proof.Ed25519.Word64 (val4 val4_lt)
open VG.Spec.Ed25519 (L)

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

end VG.Proof.Ed25519.RISCV64
