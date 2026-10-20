module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Loading two arithmetic operands without revealing their values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem coreInputs_relCT (n al bl : Nat) (a b : Pointer) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) (hn : n ≤ 48) (ha4 : 4 ≤ al) (ha : al ≤ 8 * n) (hwa : al % 4 = 0) :
    RelCT isa (fun s t => ∃ m₁ m₂,
      Context n m₁ base size s ∧ Context n m₂ base size t ∧
      OperandReady s base n a al ∧ OperandReady t base n a al ∧
      pointerValue base s a = pointerValue base t a ∧ pointerValue base s b = pointerValue base t b)
      (.seq (Core.load n al (slot n 5) a) (Core.load n bl (slot n 8) b))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  intro s t tr ur sf tf ⟨m₁, m₂, C₁, C₂, A₁, A₂, Pa, Pb⟩ E F
  cases E with
  | seq E₁ E₂ =>
    cases F with
    | seq F₁ F₂ =>
      obtain ⟨Trace₁, _⟩ := coreLoad_relCT n al (slot n 5) a base size hz _ _ _ _ _ _ ⟨C₁.scr, C₂.scr, Pa⟩ E₁ F₁
      obtain ⟨D₁, _, K₁, O₁⟩ := wp_result (coreLoadSlot_ok C₁ hz (by decide) (by decide) ha4 ha hwa
        A₁.toReadableComponent (A₁.slot (by decide))) E₁
      obtain ⟨D₂, _, K₂, O₂⟩ := wp_result (coreLoadSlot_ok C₂ hz (by decide) (by decide) ha4 ha hwa
        A₂.toReadableComponent (A₂.slot (by decide))) F₁
      have Hn : contextBytes n ≤ 8192 := Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (by decide)
      have P₁ := pointerValue_keep K₁ (by decide) (slotOutside_whole O₁ (by decide)) Hn b
      have P₂ := pointerValue_keep K₂ (by decide) (slotOutside_whole O₂ (by decide)) Hn b
      obtain ⟨Trace₂, Agree⟩ := coreLoad_relCT n bl (slot n 8) b base size hz _ _ _ _ _ _
        ⟨D₁.scr, D₂.scr, P₁.trans (Pb.trans P₂.symm)⟩ E₂ F₂
      exact ⟨by rw [Trace₁, Trace₂], Agree⟩

end VG.Proof.Dsa.X86
