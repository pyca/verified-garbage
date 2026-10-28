module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ArgumentTaint
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CorePair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePortTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Derive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InputStage
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DeriveTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # The shared arithmetic trace is unchanged by the caller's wider permissions -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86
open VG.Proof.Mont.X86.Dynamic (workspaceTaint)
open VG.Proof.RsaKeyGen.X86.Key (Environment Input ImportedPair OutputPair core_mask_bit)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

structure RuntimeImported (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) (s t : State) : Prop where
  imported : ImportedPair E e p q p' q' s t
  left : Ws s E.base E.size E.n 32
  right : Ws t E.base E.size E.n 32
  leftArgs : Context E.base E.size sp E.argument s
  rightArgs : Context E.base E.size sp E.argument t

theorem coreStart {s : State} {B : Addr} {Z n k e p q : Nat} (H : Ws s B Z n 32)
    (C : VG.Proof.RsaKeyGen.X86.Key.CoreStart B Z n k e p q s) : CoreStart B Z n k e p q s :=
  ⟨⟨H, C.pBound, C.qBound, C.zero, C.one, C.exponent, C.loaded⟩, C.pValue, C.qValue⟩

theorem deriveOutput_ok {E : Environment} {s : State} {e p q : Nat} (h : Input E s)
    (H : Ws s E.base E.size E.n 32) (C : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p q s) :
    WP isa VG.Impl.RsaKeyGen.X86.KeyRuntime.deriveLoaded s fun t => Input E t ∧
      VG.Proof.Rsa.X86.Keys.slot t.mem E.base VG.Impl.RsaKeyGen.X86.Key.kOk ≤ 1 ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  refine WP.mono (deriveLoaded_ok H widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1 widths.1 widths.2.1
    C.pBound C.qBound C.zero C.one (C.loaded.trans C.exponent.symm))
    fun t ⟨ht, O, result, K⟩ => ?_
  exact ⟨input_afterStage h H ht.old K O, core_mask_bit result, K⟩

theorem deriveOutput_trace (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (RuntimeImported E sp e p q p' q') VG.Impl.RsaKeyGen.X86.KeyRuntime.deriveLoaded (OutputPair E) := by
  intro s t tr ur u v P A C
  have widths := P.imported.inputs.left.valid.widths
  have runS := deriveLoaded_ok P.left.readonly widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1
    widths.1 widths.2.1 P.imported.left.pBound P.imported.left.qBound P.imported.left.zero
    P.imported.left.one (P.imported.left.loaded.trans P.imported.left.exponent.symm)
  have runT := deriveLoaded_ok P.right.readonly widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1
    widths.1 widths.2.1 P.imported.right.pBound P.imported.right.qBound P.imported.right.zero
    P.imported.right.one (P.imported.right.loaded.trans P.imported.right.exponent.symm)
  obtain ⟨u', AS⟩ := trace_readonly_of_wp P.left runS A
  obtain ⟨v', CT⟩ := trace_readonly_of_wp P.right runT C
  have oldS : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p q
      (readonly s E.base E.size) :=
    { P.imported.left with workspace := P.left.readonly.old }
  have oldT : VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p' q'
      (readonly t E.base E.size) :=
    { P.imported.right with workspace := P.right.readonly.old }
  have agree := readonly_agree P.leftArgs P.rightArgs P.left.hdr_le
    (P.imported.agree.reg (by rfl : VG.X86.Taint.pub (workspaceTaint true) .esi = true))
  obtain ⟨trace, agreeOut⟩ := deriveLoaded_trace E.base E.size E.n E.k e p q p' q'
    widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1 release _ _ _ _ _ _
    ⟨coreStart P.left.readonly oldS, coreStart P.right.readonly oldT, agree⟩ AS CT
  obtain ⟨sRead, sWrite⟩ := readonly_covers P.left
  obtain ⟨tRead, tWrite⟩ := readonly_covers P.right
  have widenedS := VG.X86.Exec.widen AS sRead sWrite
  have widenedT := VG.X86.Exec.widen CT tRead tWrite
  simp only [readonly, State.withRegions_withRegions, State.withRegions_self] at widenedS widenedT
  have endS := (Exec.det A widenedS).2
  have endT := (Exec.det C widenedT).2
  have publicOut : VG.X86.Taint.Agree (workspaceTaint true) u v := by
    change VG.X86.Taint.Agree (τr [.edi, .esi]) u v
    apply agree_regs
    intro r hr
    rw [endS, endT]
    change u'.gpr r = v'.gpr r
    apply agreeOut.reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  obtain ⟨leftInput, leftBit, leftKeeps⟩ := wp_result (deriveOutput_ok P.imported.inputs.left P.left P.imported.left) A
  obtain ⟨rightInput, rightBit, rightKeeps⟩ := wp_result (deriveOutput_ok P.imported.inputs.right P.right P.imported.right) C
  refine ⟨trace, ⟨leftInput, rightInput, ?_⟩, publicOut, leftBit, rightBit⟩
  rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
  exact P.imported.inputs.stack

end VG.Proof.RsaKeyGen.X86.KeyRuntime
