module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Register arithmetic and fixed stack loads expose only the shared stack pointer. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm

def stackOnlyInstr : Instr → Bool
  | .ldr .. | .str .. | .ldrb .. | .strb .. | .push .. | .pop .. | .alloc .. | .free .. => false
  | _ => true

private theorem stackOnly_addresses {i : Instr} (allowed : stackOnlyInstr i = true)
    {s t : State} (sp : s.sp = t.sp) : addrs i s = addrs i t := by
  cases i <;> simp only [stackOnlyInstr] at allowed <;> try cases allowed
  all_goals simp only [addrs, sp]

theorem stackOnly_ct (code : List Instr) (allowed : code.all stackOnlyInstr = true) :
    RelCT isa (fun s t => s.sp = t.sp) (.block code) (fun s t => s.sp = t.sp) := by
  induction code with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons op rest ih =>
    have valid : stackOnlyInstr op = true ∧ rest.all stackOnlyInstr = true := by simpa only [List.all_cons, Bool.and_eq_true] using allowed
    have step : RelCT isa (fun s t => s.sp = t.sp) (.block [op]) (fun s t => s.sp = t.sp) := by
      refine single_ct (fun _ _ h => stackOnly_addresses valid.1 h) ?_
      intro s t u v h left right
      exact (exec_sp left).trans (h.trans (exec_sp right).symm)
    exact RelCT.block_append (step.seq (ih valid.2))

end VG.Proof.Bignum.Arm
