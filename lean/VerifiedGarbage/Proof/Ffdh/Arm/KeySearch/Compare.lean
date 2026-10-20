module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Comparisons of the three public key-attempt statuses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch

open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem compareStatus_ok (s : State) {status test : Nat} (small : status < 4) (testSmall : test < 4)
    (value : s.gpr .r9 = BitVec.ofNat 32 status) :
    WP isa (.block [.cmp .r9 (.imm (BitVec.ofNat 32 test))]) s fun t =>
      (t.z = decide (status = test) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  refine withRest [] ?_ (by
    intro r _ i hi
    simp only [instrs, List.mem_singleton] at hi
    subst i
    rfl) (by rfl)
  have casesStatus : status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 3 := by omega
  have casesTest : test = 0 ∨ test = 1 ∨ test = 2 ∨ test = 3 := by omega
  rcases casesStatus with rfl | rfl | rfl | rfl <;>
    rcases casesTest with rfl | rfl | rfl | rfl <;> ffrun [value]

end VG.Proof.Ffdh.Arm.KeySearch
