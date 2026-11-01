module

import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.X448.RISCV64.R64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.X448.RISCV64.Limbs

/-!
# X448 on RISC-V, 64-bit limbs: a product added to an accumulator

`macc l h t x y` adds `x · y` to the three-word accumulator `l, h, t`
(`macc_ok`): the product's words (`mulWide_ok`), then the two-word sum into
three words (`acc_ok`), whose high word plus the carry cannot wrap around, as
the high word of a product is at most `2⁶⁴ - 2`.
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.X448.RISCV64.R64

variable {s : State}

/-- The high word of a product of words is at most `2⁶⁴ - 2`. -/
theorem nat_mulhi_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * b / 2 ^ 64 < 2 ^ 64 - 1 := by
  have : a * b ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (2 ^ 64 - 1) * (2 ^ 64 - 1) / 2 ^ 64 < 2 ^ 64 - 1 := by decide
  exact Nat.lt_of_le_of_lt (Nat.div_le_div_right this) h2

/-- The high word of a product is at most `2⁶⁴ - 2`. -/
theorem mulhi_lt (a b : BitVec 64) : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 - 1 :=
  nat_mulhi_lt a.isLt b.isLt

set_option linter.unusedSimpArgs false in
/-- `l + 2⁶⁴ h + 2¹²⁸ t += a7 + 2⁶⁴ t0`, for `t0 < 2⁶⁴ - 1`. -/
theorem acc_ok {l h t : Reg} (hlh : l ≠ h) (hlt : l ≠ t) (hht : h ≠ t)
    (hl7 : l ≠ .a7) (hl0 : l ≠ .t0) (hh7 : h ≠ .a7) (hh0 : h ≠ .t0) (ht7 : t ≠ .a7)
    (ht0 : t ≠ .t0) :
    WP isa (.block [.add l l .a7, .sltu .a7 l .a7, .add .t0 .t0 .a7, .add h h .t0,
        .sltu .t0 h .t0, .add t t .t0]) s fun s' =>
      ((s.gpr .t0).toNat < 2 ^ 64 - 1 →
        val3 s' l h t = (val3 s l h t + ((s.gpr .a7).toNat + 2 ^ 64 * (s.gpr .t0).toNat)) % 2 ^ 192) ∧
      Keeps [l, h, t, .a7, .t0] s s' := by
  apply WP.of_runBlock
  simp only [val3, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_sltu,
    RegUpd.gpr_write, hlh, hlt, hht, hl7, hl0, hh7, hh0, ht7, ht0, Ne.symm hlh, Ne.symm hlt,
    Ne.symm hht, Ne.symm hl7, Ne.symm hl0, Ne.symm hh7, Ne.symm hh0, Ne.symm ht7, Ne.symm ht0,
    show Reg.a7 ≠ Reg.t0 by decide, show Reg.t0 ≠ Reg.a7 by decide,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun hb => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · have c₀ := Wide.carry (s.gpr l) (s.gpr .a7)
    have l₀ := Wide.carry_le (s.gpr l + s.gpr .a7 < s.gpr .a7)
    generalize (if s.gpr l + s.gpr .a7 < s.gpr .a7 then (1 : BitVec 64) else 0) = k₀ at *
    have e₁ : (s.gpr .t0 + k₀).toNat = (s.gpr .t0).toNat + k₀.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have c₁ := Wide.carry (s.gpr h) (s.gpr .t0 + k₀)
    have l₁ := Wide.carry_le (s.gpr h + (s.gpr .t0 + k₀) < s.gpr .t0 + k₀)
    generalize (if s.gpr h + (s.gpr .t0 + k₀) < s.gpr .t0 + k₀ then (1 : BitVec 64) else 0) = k₁ at *
    rw [BitVec.toNat_add (s.gpr t)]
    rw [e₁] at c₁
    have := (s.gpr t).isLt
    have := (s.gpr l + s.gpr .a7).isLt
    have := (s.gpr h + (s.gpr .t0 + k₀)).isLt
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `l + 2⁶⁴ h + 2¹²⁸ t += x · y`, if the sum fits in three words. -/
theorem macc_ok {l h t x y : Reg} (hlh : l ≠ h) (hlt : l ≠ t) (hht : h ≠ t)
    (hl7 : l ≠ .a7) (hl0 : l ≠ .t0) (hh7 : h ≠ .a7) (hh0 : h ≠ .t0) (ht7 : t ≠ .a7)
    (ht0 : t ≠ .t0) (hx : x ≠ .a7) (hy : y ≠ .a7) :
    WP isa (.block (macc l h t x y)) s fun s' =>
      (val3 s l h t + (s.gpr x).toNat * (s.gpr y).toNat < 2 ^ 192 →
        val3 s' l h t = val3 s l h t + (s.gpr x).toNat * (s.gpr y).toNat) ∧
      Keeps [l, h, t, .a7, .t0] s s' := by
  have e : macc l h t x y = Impl.Words.RISCV64.mulWide .a7 .t0 x y ++
      [.add l l .a7, .sltu .a7 l .a7, .add .t0 .t0 .a7, .add h h .t0, .sltu .t0 h .t0,
        .add t t .t0] := rfl
  rw [e]
  refine WP.block_append (WP.mono (mulWide_ok (Ne.symm hx) (Ne.symm hy) (by decide))
    fun s₁ ⟨e₁, k₁⟩ => ?_)
  refine WP.mono (acc_ok hlh hlt hht hl7 hl0 hh7 hh0 ht7 ht0) fun s₂ ⟨e₂, k₂⟩ => ⟨fun hb => ?_,
    (k₁.trans k₂).mono fun r hr => ?_⟩
  · have hv : val3 s₁ l h t = val3 s l h t := by
      simp only [val3, k₁.1 l (by simp [hl7, hl0]), k₁.1 h (by simp [hh7, hh0]),
        k₁.1 t (by simp [ht7, ht0])]
    have ht : (s₁.gpr .t0).toNat < 2 ^ 64 - 1 := by
      have := mulhi_lt (s.gpr x) (s.gpr y)
      have hlo := (s₁.gpr .a7).isLt
      have : (s₁.gpr .t0).toNat ≤ (s.gpr x).toNat * (s.gpr y).toNat / 2 ^ 64 :=
        (Nat.le_div_iff_mul_le (by decide)).mpr (by rw [← e₁]; omega)
      omega
    rw [e₂ ht, hv, e₁, Nat.mod_eq_of_lt hb]
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (h | h) | (h | h | h | h | h) <;> simp only [h, true_or, or_true]

end VG.Proof.X448.RISCV64.R64
