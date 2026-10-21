module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CoreReadonlyTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.SelectTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePortTiming

/-! # Width comparisons preserve the shared core's input snapshots and argument records -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.Key (Environment SizedStart OutputPair)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

structure RuntimeStart (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) (s t : State) : Prop where
  start : SizedStart E e p q p' q' s t
  left : Ws s E.base E.size E.n 32
  right : Ws t E.base E.size E.n 32
  leftArgs : Context E.base E.size sp E.argument s
  rightArgs : Context E.base E.size sp E.argument t

theorem RuntimeStart.keepIO (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) :
    KeepIO (RuntimeStart E sp e p q p' q') := by
  intro s t u v P KU MU KV MV
  have left := P.start.inputs.left.keep (P.start.inputs.left.ws.rest KU) KU (by intro d hd; rw [MU])
  have right := P.start.inputs.right.keep (P.start.inputs.right.ws.rest KV) KV (by intro d hd; rw [MV])
  have start : SizedStart E e p q p' q' u v := by
    refine ⟨⟨left, right, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [KU.1 .esp (by decide), KV.1 .esp (by decide)]; exact P.start.inputs.stack
    · rw [MU]; exact P.start.leftExponent
    · rw [MV]; exact P.start.rightExponent
    · rw [MU]; exact P.start.leftP
    · rw [MU]; exact P.start.leftQ
    · rw [MV]; exact P.start.rightP
    · rw [MV]; exact P.start.rightQ
  refine ⟨start, P.left.keep KU ?_, P.right.keep KV ?_, P.leftArgs.keep KU ?_, P.rightArgs.keep KV ?_⟩
  · rw [MU]; exact Outside.refl _ _ _ _
  · rw [MV]; exact Outside.refl _ _ _ _
  · rw [MU]; exact Frame.refl _ _
  · rw [MV]; exact Frame.refl _ _

theorem output_keepIO (E : Environment) : KeepIO (OutputPair E) := by
  intro s t u v P KU MU KV MV
  have left := P.1.left.keep (P.1.left.ws.rest KU) KU (by intro d hd; rw [MU])
  have right := P.1.right.keep (P.1.right.ws.rest KV) KV (by intro d hd; rw [MV])
  have agree : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint true) u v := by
    change VG.X86.Taint.Agree (τr [.edi, .esi]) u v
    apply agree_regs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [KU.1 .edi (by decide), KV.1 .edi (by decide)]
      exact P.2.1.reg (by rfl)
    · rw [KU.1 .esi (by decide), KV.1 .esi (by decide)]
      exact P.2.1.reg (by rfl)
  refine ⟨⟨left, right, ?_⟩, agree, ?_, ?_⟩
  · rw [KU.1 .esp (by decide), KV.1 .esp (by decide)]; exact P.1.stack
  · rw [MU]; exact P.2.2.1
  · rw [MV]; exact P.2.2.2

end VG.Proof.RsaKeyGen.X86.KeyRuntime
