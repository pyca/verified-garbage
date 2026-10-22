module

public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEight
public import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # The row-wise triangle of an eight-limb square: one product and its addition -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.SquareEight

/-- The low (`hi = false`) or high half of a product of two words. -/
def half (hi : Bool) (a b : Word) : Word :=
  if hi then BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) else a * b

/-- The product instruction of a half, into the temporary. -/
def prod (hi : Bool) (x y : Reg) : Instr :=
  if hi then .umulh tmp x y else .mul .x tmp x y

theorem half_value (a b : Word) :
    (half false a b).toNat + 2 ^ 64 * (half true a b).toNat = a.toNat * b.toNat := by
  simp only [half, Bool.false_eq_true, ↓reduceIte]
  exact mul_toNat _ _

theorem prod_adcs_ok (s : State) (hi : Bool) (r src x y : Reg) (hr : r ≠ tmp) (hs : src ≠ tmp) :
    WP isa (.block [prod hi x y, .adcs .x r src tmp]) s fun t =>
      (t.gpr r = addCarry (s.gpr src) (half hi (s.gpr x) (s.gpr y)) s.c ∧
        t.c = carryOut (s.gpr src) (half hi (s.gpr x) (s.gpr y)) s.c ∧ t.mem = s.mem) ∧
      Keep [tmp, r] s t := by
  cases hi
  all_goals
    refine WP.keep [tmp, r] ?_ (by simp [prod, writesOnly, Code.allInstrs, dsts, dstOf, Option.toList])
      rfl rfl
    simp only [tmp] at hr hs
    brun [prod, tmp, hr, hs, half]
    refine ⟨?_, rfl⟩
    simp only [addCarry, off, BitVec.ofNat_add, BitVec.add_assoc]

theorem prod_adds_ok (s : State) (hi : Bool) (r src x y : Reg) (hr : r ≠ tmp) (hs : src ≠ tmp) :
    WP isa (.block [prod hi x y, .adds .x r src tmp]) s fun t =>
      (t.gpr r = addCarry (s.gpr src) (half hi (s.gpr x) (s.gpr y)) false ∧
        t.c = carryOut (s.gpr src) (half hi (s.gpr x) (s.gpr y)) false ∧ t.mem = s.mem) ∧
      Keep [tmp, r] s t := by
  cases hi
  all_goals
    refine WP.keep [tmp, r] ?_ (by simp [prod, writesOnly, Code.allInstrs, dsts, dstOf, Option.toList])
      rfl rfl
    simp only [tmp] at hr hs
    brun [prod, tmp, hr, hs, half]
    refine ⟨?_, rfl⟩
    simp only [addCarry, off, BitVec.ofNat_add, BitVec.add_assoc]

theorem prod_adc_ok (s : State) (hi : Bool) (r src x y : Reg) (hr : r ≠ tmp) (hs : src ≠ tmp) :
    WP isa (.block [prod hi x y, .adc .x r src tmp]) s fun t =>
      (t.gpr r = addCarry (s.gpr src) (half hi (s.gpr x) (s.gpr y)) s.c ∧ t.mem = s.mem) ∧
      Keep [tmp, r] s t := by
  cases hi
  all_goals
    refine WP.keep [tmp, r] ?_ (by simp [prod, writesOnly, Code.allInstrs, dsts, dstOf, Option.toList])
      rfl rfl
    simp only [tmp] at hr hs
    brun [prod, tmp, hr, hs, half]
    simp only [addCarry, off, BitVec.ofNat_add, BitVec.add_assoc]

end VG.Proof.Bignum.AArch64.SquareEight
