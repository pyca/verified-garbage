module

import VerifiedGarbage.Proof.Dsa.X86.CoreSetupTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreStoreTiming
public import VerifiedGarbage.Proof.Dsa.X86.StreamTiming
public import VerifiedGarbage.Proof.Dsa.X86.CoreReduce
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreStreamSource
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Complete streaming reduction calls have secret-independent traces -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure ReductionPre (base : Addr) (size qLen inputLen : Nat) (input : Pointer) (src : Src) (s : State) : Prop where
  scr : Scr s base size
  modulusReady : OperandReady s base ((qLen + 7) / 8) (.input .q) qLen
  inputReady : StreamInput s base (contextBytes ((qLen + 7) / 8)) (pointerValue base s input) inputLen
  len : LenOperand base size ((qLen + 7) / 8) s src inputLen
  large : 255 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) qLen)
  odd : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) qLen) % 2 = 1

theorem coreReduce_relCT (base : Addr) (size qLen inputLen output : Nat) (input : Pointer) (src : Src)
    (hf : LenForm src) (hz : Layout.saved ≤ size) (h4 : 4 ≤ qLen) (hmax : qLen ≤ 384) (hw4 : qLen % 4 = 0) :
    RelCT isa (fun s t => ReductionPre base size qLen inputLen input src s ∧
      ReductionPre base size qLen inputLen input src t ∧
      pointerValue base s (.input .q) = pointerValue base t (.input .q) ∧
      pointerValue base s input = pointerValue base t input)
      (Core.reduce qLen src input output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  intro s t tr ur sf tf ⟨P, Q, Mod, Src⟩ E F
  have hn48 : (qLen + 7) / 8 ≤ 48 := by omega
  have Hn : contextBytes ((qLen + 7) / 8) ≤ 8192 :=
    Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn48) (by decide)
  have hs : contextBytes ((qLen + 7) / 8) ≤ size := by change 8256 ≤ size at hz; omega
  cases E with
  | seq E₀ Erest =>
    cases F with
    | seq F₀ Frest =>
      obtain ⟨Trace₀, _⟩ := coreSetup_relCT qLen .q base size hz _ _ _ _ _ _ ⟨P.scr, Q.scr, Mod⟩ E₀ F₀
      obtain ⟨C₁, _, _, O₁, K₁⟩ := wp_result (coreSetup_ok P.scr hz rfl h4 hmax hw4
        P.modulusReady.toReadableComponent (P.modulusReady.slot (by decide)) rfl (by have := P.large; omega) P.odd) E₀
      obtain ⟨C₂, _, _, O₂, K₂⟩ := wp_result (coreSetup_ok Q.scr hz rfl h4 hmax hw4
        Q.modulusReady.toReadableComponent (Q.modulusReady.slot (by decide)) rfl (by have := Q.large; omega) Q.odd) F₀
      have Ptr₁ := pointerValue_keep K₁ (by decide) O₁ Hn input
      have Ptr₂ := pointerValue_keep K₂ (by decide) O₂ Hn input
      cases Erest with
      | seq E₁ Etail =>
        cases Frest with
        | seq F₁ Ftail =>
          obtain ⟨Trace₁, A₁⟩ := pointer_relCT input base size hz _ _ _ _ _ _
            ⟨C₁.scr, C₂.scr, Ptr₁.trans (Src.trans Ptr₂.symm)⟩ E₁ F₁
          obtain ⟨D₁, _, M₁, L₁⟩ := wp_result (streamSource_ok C₁ hz input) E₁
          obtain ⟨D₂, _, M₂, L₂⟩ := wp_result (streamSource_ok C₂ hz input) F₁
          have SP : StreamPair ((qLen + 7) / 8) size inputLen base src _ _ :=
            ⟨A₁, D₁.scr, D₂.scr,
              P.len.stream (by rw [L₁.2.1, K₁.2.1]) (by rw [L₁.2.2, K₁.2.2]) (by rw [M₁]; exact O₁),
              Q.len.stream (by rw [L₂.2.1, K₂.2.1]) (by rw [L₂.2.2, K₂.2.2]) (by rw [M₂]; exact O₂)⟩
          have Tail := RelCT.seq (reduceStream_relCT (base := base) (len := inputLen) hf (by omega) hs)
            ((coreStore_workspace_relCT qLen output).mono
              (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
              (fun _ _ h => h))
          obtain ⟨Trace₂, Agree⟩ := Tail _ _ _ _ _ _ SP Etail Ftail
          exact ⟨by rw [Trace₀, Trace₁, Trace₂], Agree⟩

end VG.Proof.Dsa.X86
