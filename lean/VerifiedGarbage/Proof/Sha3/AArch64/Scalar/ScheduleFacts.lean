module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Stages
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Control
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Sha3.AArch64.Scalar.Round`, which the modules that import this one used -/

section

/-! ### `Sha3.AArch64.Scalar.Control`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Control
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Control
open VG.Proof.Sha3.AArch64

structure ConstantKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x26 → s'.gpr r = s.gpr r
  vec : s'.v = s.v
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem constant_ok (v : BitVec 64) (s : State) :
    WP isa (.block (constant v)) s fun s' =>
      ConstantKeep s s' ∧ s'.gpr .x26 = Sha3.Vector.constantLow v := by
  by_cases h1 : v.extractLsb' 16 16 = 0 <;>
    by_cases h2 : v.extractLsb' 32 16 = 0 <;>
    by_cases h3 : v.extractLsb' 48 16 = 0
  all_goals
    simp only [constant, h1, h2, h3, ite_true, ite_false,
      List.cons_append, List.nil_append]
    repeat' apply WP.cons rfl
    apply wp_nil
    refine ⟨⟨?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · intro r hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    · simp only [Sha3.Vector.constantLow, h1, h2, h3, ite_true, ite_false,
        Sha3.Vector.movkValue, RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq]

end VG.Proof.Sha3.AArch64.Scalar.Control

end

end

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

theorem laneReg_zero : ∀ i < 25, laneReg i = .x0 ↔ i = 0 := by decide +kernel

end VG.Proof.Sha3.AArch64.Scalar

end

end

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

theorem scratch_not_lane : ∀ r ∈ [Reg.x26, .x27, .x28, .x30],
    ∀ i < 25, laneReg i ≠ r := by decide +kernel

/-- These operand constraints allow a baseline-ISA implementation of BIC
as AND then XOR, and EOR-with-rotation without destroying a live source. -/
def BaselineSafe : ScalarOp → Prop
  | .bic d a _ => d ≠ a
  | .bicRor d a b _ => d ≠ a ∧ d ≠ b
  | .xorRor d a b _ => a ≠ b ∧ d ≠ b
  | .spill k _ => k < 2
  | .reload _ k => k < 2
  | _ => True

instance (op : ScalarOp) : Decidable (BaselineSafe op) := by
  cases op <;> unfold BaselineSafe <;> infer_instance

end VG.Proof.Sha3.AArch64.Scalar
