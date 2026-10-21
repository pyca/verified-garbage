module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Public candidate status comparison changes only flags. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

theorem compareResult_ok (s : State) {status test : Nat} (small : status < 3)
    (which : test = 1 ∨ test = 2) (value : s.gpr .r0 = BitVec.ofNat 32 status) :
    WP isa (.block [.cmp .r0 (.imm (BitVec.ofNat 32 test))]) s fun t =>
      (t.z = decide (status = test) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  refine withRest [] ?_ (by
    intro r _ i hi
    simp only [instrs, List.mem_singleton] at hi
    subst i
    rfl) (by rfl)
  have choices : status = 0 ∨ status = 1 ∨ status = 2 := by omega
  rcases which with rfl | rfl
  all_goals ffrun [value]
  all_goals rcases choices with rfl | rfl | rfl <;> rfl

end VG.Proof.Ffdh.Arm.ParameterSearch
