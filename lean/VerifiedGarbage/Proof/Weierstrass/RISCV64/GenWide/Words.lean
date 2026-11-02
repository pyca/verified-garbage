module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: a multiply-accumulate step

The arithmetic of `macStep` (`Impl/Weierstrass/RISCV64/GenWide.lean`) on
registers: `t0 + 2⁶⁴ a5 := a6 · a4 + a7 + a5` (`mac_ok`), which cannot
overflow two words.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Wide

variable {s : State}

/-- The two words of `x y + t + c` for words `x`, `y`, `t`, `c`, by `mul`,
`mulhu` and two sums with `sltu` carries. -/
theorem mac_nat {x y t c lo hi c₁ u c₂ : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (ht : t < 2 ^ 64)
    (hc : c < 2 ^ 64) (hp : lo + 2 ^ 64 * hi = x * y)
    (h₁ : u + 2 ^ 64 * c₁ = lo + t) {v : Nat} (h₂ : v + 2 ^ 64 * c₂ = u + c) :
    v + 2 ^ 64 * (hi + c₁ + c₂) = x * y + t + c ∧ hi + c₁ + c₂ < 2 ^ 64 := by
  have hxy : x * y ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  constructor
  · omega
  · have hv : v + 2 ^ 64 * (hi + c₁ + c₂) = x * y + t + c := by omega
    omega

set_option linter.unusedSimpArgs false in
/-- `t0 + 2⁶⁴ a5 := a6 · a4 + a7 + a5`, through `a1` and `t3`. -/
theorem mac_ok :
    WP isa (.block [.mul .t0 .a6 .a4, .mulhu .a1 .a6 .a4, .add .t0 .t0 .a7, .sltu .t3 .t0 .a7,
        .add .a1 .a1 .t3, .add .t0 .t0 .a5, .sltu .t3 .t0 .a5, .add .a5 .a1 .t3]) s fun s' =>
      (s'.gpr .t0).toNat + 2 ^ 64 * (s'.gpr .a5).toNat =
        (s.gpr .a6).toNat * (s.gpr .a4).toNat + (s.gpr .a7).toNat + (s.gpr .a5).toNat ∧
      Keeps [.t0, .a1, .t3, .a5] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mul, exec_mulhu, exec_add, exec_sltu,
    RegUpd.gpr_write, ite_true, ite_false, Option.some.injEq, exists_eq_left', reduceCtorEq]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · generalize hX : s.gpr .a6 = X at *
    generalize hY : s.gpr .a4 = Y at *
    generalize hT : s.gpr .a7 = Tw at *
    generalize hC : s.gpr .a5 = C at *
    have hp := mul_words X Y
    generalize BitVec.ofNat 64 (X.toNat * Y.toNat / 2 ^ 64) = H at *
    have e₁ := carry (X * Y) Tw
    have l₁ := carry_le (X * Y + Tw < Tw)
    generalize (if X * Y + Tw < Tw then (1 : BitVec 64) else 0) = k₁ at *
    have e₂ := carry (X * Y + Tw) C
    have l₂ := carry_le (X * Y + Tw + C < C)
    generalize (if X * Y + Tw + C < C then (1 : BitVec 64) else 0) = k₂ at *
    have m := mac_nat X.isLt Y.isLt Tw.isLt C.isLt hp e₁ e₂
    have hA : (H + k₁).toNat = H.toNat + k₁.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hB : (H + k₁ + k₂).toNat = H.toNat + k₁.toNat + k₂.toNat := by
      rw [BitVec.toNat_add, hA, Nat.mod_eq_of_lt (by omega)]
    rw [hB]; exact m.1
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

end VG.Proof.Weierstrass.RISCV64.GenWide
