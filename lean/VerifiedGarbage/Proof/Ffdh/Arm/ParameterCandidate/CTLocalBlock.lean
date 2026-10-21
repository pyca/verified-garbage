module

public import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Fixed local-frame blocks retain public stack addresses while their values may vary. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm

def localOnlyInstr : Instr → Bool
  | .addSp _ _ => true
  | .str _ base _ => base == .r12
  | .ldrSp dst _ => dst != .r12
  | .ldr .. | .ldrb .. | .strb .. | .push .. | .pop .. | .alloc .. | .free .. => false
  | op => !(clobbers op .r12)

private theorem localOnly_addresses {i : Instr} (allowed : localOnlyInstr i = true)
    {s t : State} (h : LocalAddress s t) : addrs i s = addrs i t := by
  cases i <;> simp only [localOnlyInstr] at allowed <;> try cases allowed
  all_goals try rfl
  all_goals try exact congrArg (fun sp => [State.addr (sp + _)]) h.2
  case str source base d =>
    have equal : base = .r12 := eq_of_beq allowed
    subst base
    simp only [addrs, h.1]

private theorem localOnly_keep {i : Instr} (allowed : localOnlyInstr i = true)
    {s t u v : State} (h : LocalAddress s t) (left : exec i s = some u) (right : exec i t = some v) :
    LocalAddress u v := by
  refine ⟨?_, (exec_sp left).trans (h.2.trans (exec_sp right).symm)⟩
  by_cases add : ∃ dst n, i = .addSp dst n
  · obtain ⟨dst, n, rfl⟩ := add
    by_cases small : n < 256
    · simp only [exec, small, ite_true, Option.some.injEq] at left right
      subst u
      subst v
      by_cases same : dst = .r12
      · subst dst
        simp only [State.setReg, ite_true, h.2]
      · simp only [State.setReg, Ne.symm same, ite_false]
        exact h.1
    · simp only [exec, small, ite_false] at left
      cases left
  · have stable : clobbers i .r12 = false := by
      cases i <;> simp_all [localOnlyInstr, clobbers, dstOf]
    exact (exec_gpr stable left).trans (h.1.trans (exec_gpr stable right).symm)

theorem localBlock_ct (code : List Instr) (allowed : code.all localOnlyInstr = true) :
    RelCT isa LocalAddress (.block code) LocalAddress := by
  induction code with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons op rest ih =>
    have valid : localOnlyInstr op = true ∧ rest.all localOnlyInstr = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using allowed
    exact RelCT.block_append ((single_ct (fun _ _ h => localOnly_addresses valid.1 h)
      (fun _ _ _ _ h left right => localOnly_keep valid.1 h left right)).seq (ih valid.2))

end VG.Proof.Ffdh.Arm.ParameterCandidate
