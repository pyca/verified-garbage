module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Loop
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction)

def passOffset (component : Nat) (direction : Direction) : Nat :=
  128 * component + if direction = .encrypt then 0 else 120

theorem passOffset_bound : ∀ c < 3, ∀ d : Direction, passOffset c d < 2 ^ 15 := by
  intro c hc d
  cases d <;> simp only [passOffset, reduceCtorEq, ite_true, ite_false] <;> omega

theorem passStart_ok (component : Nat) (hc : component < 3) (direction : Direction)
    (s : State) :
    ∃ s', runBlock isa (passStart component direction) s = some s' ∧
      s'.gpr .r17 = s.gpr .r3 + BitVec.ofNat 64 (passOffset component direction) ∧
      s'.gpr .r16 = BitVec.ofNat 64 16 ∧ s'.mem = s.mem ∧
      s'.gpr .r18 = stepVal direction ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r16 → r ≠ .r17 → r ≠ .r18 → s'.gpr r = s.gpr r) := by
  have hb := passOffset_bound component hc direction
  let s₁ := s.write .r17 (s.gpr .r3 + BitVec.ofNat 64 (passOffset component direction))
  let s₂ := s₁.write .r16 (BitVec.ofNat 64 16)
  let s₃ := s₂.write .r18 (BitVec.ofNat 64 0)
  let s₄ := s₃.write .r18 (stepVal direction)
  have e₄ : exec (if direction = .encrypt then .addi .r18 .r18 8 else .subi .r18 .r18 8) s₃ =
      some s₄ := by
    cases direction
    · rw [ite_eq_left rfl, exec_addi (by decide) (by decide)]
      simp only [s₄, s₃, gpr_write, ite_true, stepVal]
      rfl
    · rw [ite_eq_right (by decide), exec_subi (by decide) (by decide)]
      simp only [s₄, s₃, gpr_write, ite_true, stepVal, reduceCtorEq, ite_false]
      rfl
  refine ⟨s₄, ?_, ?_, ?_, rfl, ?_, rfl, rfl, ?_⟩
  · rw [passStart, runBlock_cons, show (128 * component + if direction = .encrypt then 0 else 120)
        = passOffset component direction from rfl,
      exec_addi (by decide) hb, runStep_some, runBlock_cons, imm, exec_li (by decide),
      runStep_some, runBlock_cons, imm, exec_li (by decide), runStep_some, runBlock_cons, e₄,
      runStep_some, runBlock_nil]
  · simp only [s₄, s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₄, s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₄, gpr_write, ite_true]
  · intro r h16 h17 h18
    simp only [s₄, s₃, s₂, s₁, gpr_write, h16, h17, h18, ite_false]

end VG.Proof.TripleDes.PPC64LE
