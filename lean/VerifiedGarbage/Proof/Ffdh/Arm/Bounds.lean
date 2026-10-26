module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Init
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Unsigned public size guards for the native controller entry points. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem boundTest_ok (s : State) (b : BitVec 16) :
    WP isa (.block (boundTest b)) s fun t =>
      (t.z = decide ((s.gpr .r1).toNat < b.toNat) ∧ t.mem = s.mem) ∧ Rest [.r3, .r12] s t := by
  refine withRest_all [.r3, .r12] ?_ (by rfl) (by rfl)
  have bw : b.toNat < 2 ^ 32 := by have := b.isLt; omega
  have hto : (b.setWidth 32).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt bw]
  unfold boundTest
  ffrun [BitVec.add_zero, BitVec.zero_add, hto]
  by_cases h : b.toNat ≤ (s.gpr .r1).toNat
  · simp [h, show ¬ (s.gpr .r1).toNat < b.toNat by omega]
  · simp [h, show (s.gpr .r1).toNat < b.toNat by omega]

end VG.Proof.Ffdh.Arm
