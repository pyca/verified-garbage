module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Lazy.Constant
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64

structure ConstantKeep (d : Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  vec : s'.v = s.v
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem constant_ok (d : Reg) (r : Nat) (s : State) :
    WP isa (.block (constant d r)) s fun s' =>
      ConstantKeep d s s' ∧ s'.gpr d = Sha3.Vector.constantLow (Spec.Sha3.RC r) := by
  by_cases h1 : (Spec.Sha3.RC r).extractLsb' 16 16 = 0 <;>
    by_cases h2 : (Spec.Sha3.RC r).extractLsb' 32 16 = 0 <;>
    by_cases h3 : (Spec.Sha3.RC r).extractLsb' 48 16 = 0
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

end VG.Proof.Sha3.AArch64.Scalar.Lazy.Constant
