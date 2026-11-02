module

public import VerifiedGarbage.Impl.Ffdh.Arm.CallerRows
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Bignum.Arm.DownRowUmaal
import VerifiedGarbage.Proof.Framework.Omega

/-! RSA's proven UMAAL row simulation also applies around a selected
shared callee, preserving its call name, body, trace and stack bound. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CallerRows
open VG VG.Arm VG.Impl.Ffdh.Arm VG.Impl.Bignum.Arm
open VG.Proof.Bignum.Arm

theorem exec {c : Prog isa} {s s' : State} {trace : List Leak}
    (h : Exec isa c s trace s') : Exec isa (callerRows c) s trace s' := by
  induction h with
  | icall hi => nomatch hi
  | icallNext hi => nomatch hi
  | block h =>
    simp only [callerRows]
    split
    · rename_i e; exact row_sim (e ▸ .block h)
    · split
      · rename_i e; exact DownRowUmaal.code_sim (e ▸ .block h)
      · exact .block h
  | seq h1 h2 ih1 ih2 =>
    simp only [callerRows]
    split
    · rename_i e; exact row_sim (e ▸ .seq h1 h2)
    · split
      · rename_i e; exact DownRowUmaal.code_sim (e ▸ .seq h1 h2)
      · exact .seq ih1 ih2
  | iteT hc h ih =>
    simp only [callerRows]
    split
    · rename_i e; exact row_sim (e ▸ .iteT hc h)
    · split
      · rename_i e; exact DownRowUmaal.code_sim (e ▸ .iteT hc h)
      · exact .iteT hc ih
  | iteF hc h ih =>
    simp only [callerRows]
    split
    · rename_i e; exact row_sim (e ▸ .iteF hc h)
    · split
      · rename_i e; exact DownRowUmaal.code_sim (e ▸ .iteF hc h)
      · exact .iteF hc ih
  | loopExit h hc ih =>
    simp only [callerRows]
    split
    · rename_i e; exact row_sim (e ▸ .loopExit h hc)
    · split
      · rename_i e; exact DownRowUmaal.code_sim (e ▸ .loopExit h hc)
      · exact .loopExit ih hc
  | loopNext h hc h' ih ih' =>
    simp only [callerRows]
    split
    · rename_i e; exact row_sim (e ▸ .loopNext h hc h')
    · rename_i e
      split
      · rename_i d; exact DownRowUmaal.code_sim (d ▸ .loopNext h hc h')
      · rename_i d
        simp only [callerRows, e, d, ite_false] at ih'
        exact .loopNext ih hc ih'
  | call hc h hr _ => exact .call hc h hr
  | frame hp h hq ih =>
    simp only [callerRows]
    split
    · rename_i e; exact row_sim (e ▸ .frame hp h hq)
    · split
      · rename_i e; exact DownRowUmaal.code_sim (e ▸ .frame hp h hq)
      · exact .frame hp ih hq

theorem verified {c : Prog isa} {contract : Contract isa} (h : Verified target c contract) :
    Verified target (callerRows c) contract := h.of_sim exec

theorem stack (c : Prog isa) : FrameStack.armStack (callerRows c) ≤ FrameStack.armStack c := by
  induction c with
  | icall => exact Nat.le_refl _
  | block _ =>
    simp only [callerRows]; split
    · simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
    · split
      · simp [DownRowUmaal.codeU_stack]
      · rfl
  | seq a b iha ihb =>
    simp only [callerRows]
    split
    · simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
    · split
      · simp [DownRowUmaal.codeU_stack]
      · simp only [FrameStack.armStack]; omega
  | ite _ a b iha ihb =>
    simp only [callerRows]
    split
    · simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
    · split
      · simp [DownRowUmaal.codeU_stack]
      · simp only [FrameStack.armStack]; omega
  | loop a _ ih =>
    simp only [callerRows]
    split
    · simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
    · split
      · simp [DownRowUmaal.codeU_stack]
      · exact ih
  | call _ _ _ => rfl
  | frame i a _ ih =>
    simp only [callerRows]
    split
    · simp [FrameStack.armStack, rowU, rowLoopU, rowBody, rowStep, rowStepAt]
    · split
      · simp [DownRowUmaal.codeU_stack]
      · cases i <;> simp only [FrameStack.armStack] <;> omega

end VG.Proof.Ffdh.Arm.CallerRows
