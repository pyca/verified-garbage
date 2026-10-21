module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
public import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # The fixed native 64-bit GCD schedule has no input-dependent branches or addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem bankStep_public (a b : Nat) : KeyPublic (bankStep a b) := by
  unfold bankStep
  apply KeyPublic.seqs
  intro c mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact bitOf_public .. | exact sub3_public .. | exact sel_public .. |
      exact masks_public | exact zeroCarry_public | exact half_public ..

theorem code_check : ∃ hint, VG.Taint.check taint (workspaceTaint false) code hint = some counterEndTaint := by
  obtain ⟨h1, o1, c1, l1⟩ := bankStep_public 0 4
  obtain ⟨h2, o2, c2, l2⟩ := bankStep_public 4 0
  let bodyHint : VG.Taint.Hint VG.X86.Taint.T :=
    .seq (workspaceTaint true) h1 (.seq (workspaceTaint true) h2 (.block []))
  have checkedBody : VG.Taint.check taint (workspaceTaint true) body bodyHint = some counterEndTaint :=
    exponent_check_seq taint c1 l1 (exponent_check_seq taint c2 l2 (by rfl))
  have checkedLoop : VG.Taint.check taint (workspaceTaint true) (.loop body .ne)
      (.loop (workspaceTaint true) bodyHint) = some counterEndTaint := by
    change (if taint.le (workspaceTaint true) (workspaceTaint true) then
      (VG.Taint.check taint (workspaceTaint true) body bodyHint).bind
        (fun t => if taint.le (workspaceTaint true) t && taint.condPub t .ne then some t else none)
      else none) = _
    rw [checkedBody]
    rfl
  refine ⟨.seq (workspaceTaint true) (.block []) (.loop (workspaceTaint true) bodyHint), ?_⟩
  exact exponent_check_seq taint (u := workspaceTaint true) (by rfl) (by rfl) checkedLoop

theorem code_trace : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) code
    (VG.X86.Taint.Agree (workspaceTaint false)) := by
  obtain ⟨hint, checked⟩ := code_check
  exact checkedProgramChange checked rfl

end VG.Proof.RsaKeyGen.X86.Gcd64
