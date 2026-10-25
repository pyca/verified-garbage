module

public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Compositional timing summaries for native RSA long division -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic

theorem divisionShift_public (n dst tmp : Nat) (carry : Bool) :
    KeyPublic (VG.Impl.Rsa.X86.Div.shift n dst tmp carry) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (VG.Impl.Rsa.X86.Div.shift 1 0 0 carry))),
      ({ regs := .ofList [.edi, .esi, .ebp, .edx, .ecx], flags := true } : VG.X86.Taint.T), ?_, by decide +kernel⟩
  exact (check_of_erase_eq (VG.Impl.Rsa.X86.Div.shift n dst tmp carry) (VG.Impl.Rsa.X86.Div.shift 1 0 0 carry)
    (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (VG.Impl.Rsa.X86.Div.shift 1 0 0 carry))) (by kernel_rfl) (by kernel_rfl) (by cases carry <;> kernel_rfl)).trans (by cases carry <;> rfl)

theorem divisionReduce_public (n rem divisor tmp : Nat) :
    KeyPublic (VG.Impl.Rsa.X86.Div.reduce n rem divisor tmp) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (VG.Impl.Rsa.X86.Div.reduce 1 0 0 0))),
      rowTaint true, ?_, rfl⟩
  exact (check_of_erase_eq (VG.Impl.Rsa.X86.Div.reduce n rem divisor tmp) (VG.Impl.Rsa.X86.Div.reduce 1 0 0 0)
    (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (VG.Impl.Rsa.X86.Div.reduce 1 0 0 0))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)

theorem divisionInsert_public (dst : Nat) : KeyPublic (.block (VG.Impl.Rsa.X86.Div.insertBit dst)) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (.block (VG.Impl.Rsa.X86.Div.insertBit 0) : Prog isa))), workspaceTaint true, ?_, rfl⟩
  exact (check_of_erase_eq (.block (VG.Impl.Rsa.X86.Div.insertBit dst)) (.block (VG.Impl.Rsa.X86.Div.insertBit 0) : Prog isa)
    (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (.block (VG.Impl.Rsa.X86.Div.insertBit 0) : Prog isa))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)

theorem divisionArrays_public (n quotient rem tmp : Nat) :
    KeyPublic (VG.Impl.Rsa.X86.Div.shiftArrays n quotient rem tmp) := by
  exact (divisionShift_public ..).seq ((divisionShift_public ..).seq (divisionInsert_public _))

theorem divisionStep_check (n quotient rem divisor tmp : Nat) : ∃ hint,
    VG.Taint.check taint (workspaceTaint true)
      (VG.Impl.Rsa.X86.Div.step n quotient rem divisor tmp) hint = some counterEndTaint := by
  obtain ⟨ah, ao, ac, al⟩ := divisionArrays_public n quotient rem tmp
  obtain ⟨rh, ro, rc, rl⟩ := divisionReduce_public n rem divisor tmp
  have tailCheck : VG.Taint.check taint (workspaceTaint true)
      (.block (VG.Impl.Rsa.X86.Div.insertBit quotient ++
        [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])) (.block []) = some counterEndTaint := by
    have last : VG.Taint.check taint (workspaceTaint true) (.block [ .mov .eax (.mem (VG.Impl.Mont.X86.sc 0)), .alu .add .eax (.reg .ebx), .store (VG.Impl.Mont.X86.sc 0) .eax, .alu .sub .esi (.imm 0), .alu .cmp .esi (.imm 0)] : Prog isa) (.block []) = some counterEndTaint := by
      rfl
    exact (check_of_erase_eq
      (.block (VG.Impl.Rsa.X86.Div.insertBit quotient ++
        [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]))
      (.block [ .mov .eax (.mem (VG.Impl.Mont.X86.sc 0)), .alu .add .eax (.reg .ebx), .store (VG.Impl.Mont.X86.sc 0) .eax, .alu .sub .esi (.imm 0), .alu .cmp .esi (.imm 0)] : Prog isa) (workspaceTaint true) (.block []) rfl rfl rfl).trans last

  exact ⟨.seq (workspaceTaint true) ah (.seq (workspaceTaint true) rh (.block [])),
    exponent_check_seq taint ac al (exponent_check_seq taint rc rl tailCheck)⟩

end VG.Proof.RsaKeyGen.X86.Key
