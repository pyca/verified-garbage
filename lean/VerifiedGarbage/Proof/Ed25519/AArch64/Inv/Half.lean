module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # The inversion's rows: one product accumulated

`half a m wi wo ci co` adds `a m` (`mul`, `umulh`) to the two words
`wi + 2⁶⁴ ci` into `wo + 2⁶⁴ co`, dropping a carry out of `co`. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.X25519.AArch64.Alt (exec_mul_x exec_umulh_x exec_adds_x exec_adc_x)
open VG.Impl.Ed25519.AArch64.Divstep (half)

/-- The arithmetic of `half`. -/
theorem half_arith {W C L H M wo co c e : Nat} (hm : L + 2 ^ 64 * H = M)
    (h1 : wo + 2 ^ 64 * c = W + L) (h2 : co + 2 ^ 64 * e = C + H + c) :
    wo + 2 ^ 64 * co + 2 ^ 128 * e = W + 2 ^ 64 * C + M := by
  omega

theorem half_ok (s : State) {a m wi wo ci co : Reg}
    (ha9 : a ≠ .x9) (hm9 : m ≠ .x9) (hw9 : wi ≠ .x9) (hw10 : wi ≠ .x10)
    (hc9 : ci ≠ .x9) (hc10 : ci ≠ .x10) (hco : ci ≠ wo) (hwo10 : wo ≠ .x10) (hwc : wo ≠ co) :
    WP isa (.block (half a m wi wo ci co)) s fun t =>
      (∃ e ≤ 1, (t.gpr wo).toNat + 2 ^ 64 * (t.gpr co).toNat + 2 ^ 128 * e =
        (s.gpr wi).toNat + 2 ^ 64 * (s.gpr ci).toNat + (s.gpr a).toNat * (s.gpr m).toNat) ∧
      Keeps [.x9, .x10, wo, co] s t := by
  apply WP.of_runBlock
  simp only [half, runBlock_cons, runStep_some, runBlock_nil, exec_mul_x, exec_umulh_x,
    exec_adds_x, exec_adc_x, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
      RegUpd.gpr_write, ha9, hm9, hw9, hw10, hc9, hc10, hco, hwo10, hwc,
      Ne.symm hwo10, Ne.symm hwc, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
    have hm := mul_lo_hi (s.gpr a) (s.gpr m)
    have h1 := addCarry_value (s.gpr wi) (s.gpr a * s.gpr m) false
    refine ⟨(carryOut (s.gpr ci) (mulHi (s.gpr a) (s.gpr m))
        (carryOut (s.gpr wi) (s.gpr a * s.gpr m) false)).toNat, Bool.toNat_le _, ?_⟩
    have h3 := addCarry_value (s.gpr ci) (mulHi (s.gpr a) (s.gpr m))
      (carryOut (s.gpr wi) (s.gpr a * s.gpr m) false)
    simp only [addCarry, carryOut, mulHi, Bool.toNat_false, Nat.add_zero, BitVec.add_zero] at h1 h3 hm ⊢
    exact half_arith hm h1 h3
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

end VG.Proof.Ed25519.AArch64.Inv
