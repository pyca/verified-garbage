module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseTiming
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.Rsa.X86.Div
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
/-! # The entire native division wrapper hides both operands -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyDivisionTimingOps.lean`, which only this module imported.
section

/-! # Compositional timing summaries for native RSA long division -/

section
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
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86.Key

theorem divisionLoad_public (n src divisor : Nat) : KeyPublic (divisionLoad n src divisor) := by
  unfold divisionLoad VG.Impl.Rsa.X86.Keys.seqs
  refine KeyPublic.seq ?_ ((copyWords_public ..).seq (copyWords_public ..))
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (.block [.mov .eax (.imm 0),
      .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa)), zeroTaint true, ?_, by decide +kernel⟩
  exact (check_of_erase_eq _ (.block [.mov .eax (.imm 0),
      .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa) (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa)) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)

theorem divisionCompute_public (n : Nat) : KeyPublic (divisionCompute n) := by
  obtain ⟨bodyHint, body⟩ := divisionStep_check n (VG.Impl.Rsa.X86.Keys.slot n 0)
    (VG.Impl.Rsa.X86.Keys.slot n 1) (VG.Impl.Rsa.X86.Keys.slot n 2) (VG.Impl.Rsa.X86.Keys.slot n 3)
  have loop : VG.Taint.check taint (workspaceTaint true)
      (.loop (VG.Impl.Rsa.X86.Div.step n (VG.Impl.Rsa.X86.Keys.slot n 0)
        (VG.Impl.Rsa.X86.Keys.slot n 1) (VG.Impl.Rsa.X86.Keys.slot n 2)
        (VG.Impl.Rsa.X86.Keys.slot n 3)) .ne) (.loop (workspaceTaint true) bodyHint : VG.Taint.Hint VG.X86.Taint.T) = some counterEndTaint := by
    change (if taint.le (workspaceTaint true) (workspaceTaint true) then
      (VG.Taint.check taint (workspaceTaint true) _ bodyHint).bind
        (fun t => if taint.le (workspaceTaint true) t && taint.condPub t .ne then some t else none)
      else none) = _
    rw [body]
    rfl
  have countCheck : VG.Taint.check taint (workspaceTaint true)
      (.block [.mov .esi (.imm (BitVec.ofNat 32 (32 * n)))]) (.block []) = some (workspaceTaint true) := by
    have simple : VG.Taint.check taint (workspaceTaint true)
        (.block [.mov .esi (.imm 0)]) (.block []) = some (workspaceTaint true) := rfl
    exact (check_of_erase_eq (.block [.mov .esi (.imm (BitVec.ofNat 32 (32 * n)))])
      (.block [.mov .esi (.imm 0)]) (workspaceTaint true) (.block []) rfl rfl rfl).trans simple
  refine ⟨.seq (workspaceTaint true) (.seq (workspaceTaint true) (zerosHint true) (.block [])) (.loop (workspaceTaint true) bodyHint : VG.Taint.Hint VG.X86.Taint.T),
    counterEndTaint, ?_, rfl⟩
  exact exponent_check_seq taint
    (exponent_check_seq taint (zeros_check true _ _) (by kernel_rfl) countCheck) (by kernel_rfl) loop

theorem divisionStore_public (n quotient remainder : Nat) : KeyPublic (divisionStore n quotient remainder) := by
  exact (copyWords_public ..).seq (copyWords_public ..)

theorem divisionFrom_public (n src divisor quotient remainder : Nat) :
    KeyPublic (divisionFrom n src divisor quotient remainder) := by
  exact (divisionLoad_public n src divisor).seq
    ((divisionCompute_public n).seq (divisionStore_public n quotient remainder))

theorem divisionFrom_constantTime (n src divisor quotient remainder : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint true))
      (divisionFrom n src divisor quotient remainder) := by
  obtain ⟨hint, out, checked, _⟩ := divisionFrom_public n src divisor quotient remainder
  exact VG.Taint.constantTime (A := taint) (workspaceTaint true) (fun _ _ _ _ H => H)
    (hc := hint) (by rw [checked]; rfl)

end VG.Proof.RsaKeyGen.X86.Key
