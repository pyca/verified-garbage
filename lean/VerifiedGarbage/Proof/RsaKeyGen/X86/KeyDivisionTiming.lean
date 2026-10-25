module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionTimingOps
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # The entire native division wrapper hides both operands -/

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
