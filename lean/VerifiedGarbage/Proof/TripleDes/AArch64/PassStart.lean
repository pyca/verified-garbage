module

public import VerifiedGarbage.Proof.TripleDes.AArch64.Loop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction)

def passOffset (component : Nat) (direction : Direction) : Nat :=
  128 * component + if direction = .encrypt then 0 else 120

theorem passOffset_bound : ∀ c < 3, ∀ d : Direction, passOffset c d < 4096 := by
  intro c hc d
  cases d <;> simp only [passOffset, reduceCtorEq, ite_true, ite_false] <;> omega

theorem stepVal_eq (s : State) (d : Direction) :
    (if d = .encrypt then s.gpr .x0 - s.gpr .x0 + BitVec.ofNat 64 8
      else s.gpr .x0 - s.gpr .x0 - BitVec.ofNat 64 8) = stepVal d := by
  cases d <;> simp [stepVal, BitVec.sub_self] <;> rfl

theorem passStart_ok (component : Nat) (hc : component < 3) (direction : Direction)
    (s : State) :
    ∃ s', runBlock isa (passStart component direction) s = some s' ∧
      s'.gpr .x22 = s.gpr .x0 + BitVec.ofNat 64 (passOffset component direction) ∧
      s'.gpr .x21 = BitVec.ofNat 64 16 ∧ s'.mem = s.mem ∧
      stepOf s' = stepVal direction ∧ (∀ w, w ≠ .v0 → s'.v w = s.v w) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x3 → r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) := by
  have hb := passOffset_bound component hc direction
  change 128 * component + (if direction = .encrypt then 0 else 120) < 4096 at hb
  let s₁ := s.write .x .x22 (s.read .x .x0 +
    BitVec.ofNat _ (128 * component + if direction = .encrypt then 0 else 120))
  let s₂ := s₁.write .x .x21 ((BitVec.ofNat 16 16).setWidth 64)
  let s₃ := s₂.write .x .x3 (s₂.read .x .x0 - s₂.read .x .x0)
  let s₄ := s₃.write .x .x3 (if direction = .encrypt then s₃.read .x .x3 + BitVec.ofNat _ 8
    else s₃.read .x .x3 - BitVec.ofNat _ 8)
  let s₅ := s₄.setV .v0 (ofVDwords (s₄.gpr .x3) (s₄.gpr .x3))
  have h3 : s₄.gpr .x3 = stepVal direction := by
    rw [← stepVal_eq s direction]
    cases direction <;>
      simp only [s₄, s₃, s₂, s₁, State.read, BitVec.setWidth_eq, gpr_write, reduceCtorEq,
        ite_true, ite_false]
  have e₄ : exec (if direction = .encrypt then .addImm .x .x3 .x3 8 else .subImm .x .x3 .x3 8)
      s₃ = some s₄ := by
    cases direction
    · exact VG.AArch64.exec_addImm_x (by decide)
    · exact VG.AArch64.exec_subImm_x (by decide)
  refine ⟨s₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [passStart, runBlock_cons, VG.AArch64.exec_addImm_x hb, runStep_some, runBlock_cons, imm,
      show exec (.movz .x .x21 (BitVec.ofNat 16 16) 0) s₁ = some s₂ from rfl, runStep_some,
      runBlock_cons, show exec (.sub .x .x3 .x0 .x0) s₂ = some s₃ from rfl, runStep_some,
      runBlock_cons, e₄, runStep_some, runBlock_cons,
      show exec (.vop (.dup .d2 .v0 .x3)) s₄ = some s₅ from rfl, runStep_some, runBlock_nil]
  · simp only [s₅, s₄, s₃, s₂, s₁, State.read, BitVec.setWidth_eq, gpr_setV, gpr_write,
      reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [s₅, s₄, s₃, s₂, s₁, gpr_setV, gpr_write, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [s₅, s₄, s₃, s₂, s₁, mem_setV, mem_write]
  · rw [stepOf, v_setV_self, VG.AArch64.vdword_ofVDwords_0, h3]
  · intro w hw
    exact v_setV_of_ne (s := s₄) _ hw
  · simp only [s₅, s₄, s₃, s₂, s₁, rd_setV, rd_write]
  · simp only [s₅, s₄, s₃, s₂, s₁, wr_setV, wr_write]
  · simp only [s₅, s₄, s₃, s₂, s₁, sp_setV, sp_write]
  · intro r hr₁ hr₂ hr₃
    simp only [s₅, s₄, s₃, s₂, s₁, gpr_setV, gpr_write, hr₁, hr₂, hr₃, ite_false]

end VG.Proof.TripleDes.AArch64
