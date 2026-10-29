module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CorePair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePortTiming
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ArgumentTaint
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Derive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InputStage
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRetryFlag
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.SmallMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.SmallPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.KeyPartTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarPublic
/-! # The shared arithmetic trace is unchanged by the caller's wider permissions -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/RetryTiming.lean`, which only this module imported.
section

/-! # The native retry branch is public through the shared released result -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aE kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady)

def RetryTest (B : Addr) (Z n e p q p' q' : Nat) (s t : State) : Prop :=
  ReadyPair B Z n e p q p' q' s t ∧ isa.eval .ne s = isa.eval .ne t

theorem retry_eval {B : Addr} {n : Nat} {m : Mem} {s : State}
    (flag : s.zf = some (decide (¬(slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n))))) :
    isa.eval .ne s = some (decide (slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n))) := by
  change s.zf.map Bool.not = _
  rw [flag]
  by_cases small : slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n) <;> simp [small]

theorem smallMask_trace (B : Addr) (Z n e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p' q' = .inr ())) :
    RelCT isa (ReadyPair B Z n e p q p' q') smallMask (RetryTest B Z n e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := public_trace smallMask_public _ _ _ _ _ _ P.agree A C
  obtain ⟨leftWs, leftFrame, leftFlag, _⟩ := wp_result (smallMask_ok P.left P.leftReady.bit) A
  obtain ⟨rightWs, rightFrame, rightFlag, _⟩ := wp_result (smallMask_ok P.right P.rightReady.bit) C
  have leftEval := retry_eval leftFlag
  have rightEval := retry_eval rightFlag
  refine ⟨trace, ⟨leftWs, rightWs, agree, P.leftReady.small P.left.old leftFrame,
    P.rightReady.small P.right.old rightFrame⟩, ?_⟩
  rw [leftEval, rightEval]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact P.leftReady.retry_iff.trans (release.trans P.rightReady.retry_iff.symm)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/DeriveTiming.lean`, which only this module imported.
section

/-! # Complete native numeric key derivation is constant time modulo the released retry status -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aE kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady)

theorem deriveLoaded_trace (B : Addr) (Z n k e p q p' q' : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p' q' = .inr ())) :
    RelCT isa (fun s t => CoreStart B Z n k e p q s ∧ CoreStart B Z n k e p' q' t ∧
      VG.X86.Taint.Agree runtimeTaint s t)
      deriveLoaded (VG.X86.Taint.Agree runtimeTaint) := by
  intro s t tr ur u v P E F
  have bound₁ : max p q < 2 ^ (32 * k) := by
    rw [← P.1.pValue, ← P.1.qValue]
    exact Nat.max_lt.mpr ⟨P.1.pBound, P.1.qBound⟩
  have bound₂ : max p' q' < 2 ^ (32 * k) := by
    rw [← P.2.1.pValue, ← P.2.1.qValue]
    exact Nat.max_lt.mpr ⟨P.2.1.pBound, P.2.1.qBound⟩
  refine (?_ : RelCT isa (fun s t => CoreStart B Z n k e p q s ∧ CoreStart B Z n k e p' q' t ∧
    VG.X86.Taint.Agree runtimeTaint s t) deriveLoaded (VG.X86.Taint.Agree runtimeTaint)) s t tr ur u v P E F
  unfold deriveLoaded
  apply RelCT.seq (prepareReady_trace B Z n k e p q p' q' width positive even)
  apply RelCT.seq (smallMask_trace B Z n e p q p' q' release)
  apply RelCT.ite (fun _ _ P => P.2)
  · exact (public_trace retry_public).mono (fun _ _ P => P.1.1.agree) (fun _ _ P => P)
  · exact (keyPart_trace B Z n k width positive).mono (fun _ _ P =>
      ⟨⟨P.1.1.left, by rw [P.1.1.leftReady.pValue]; exact bound₁⟩,
        ⟨P.1.1.right, by rw [P.1.1.rightReady.pValue]; exact bound₂⟩, P.1.1.agree⟩) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

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
