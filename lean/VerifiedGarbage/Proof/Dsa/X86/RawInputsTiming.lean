module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Pairwise component loading for validation without a Montgomery context -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem rawInputs_relCT (n al bl i j : Nat) (a b : Pointer) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) (hn : n ≤ 48) (hi : i < 9) (ha4 : 4 ≤ al) (ha : al ≤ 8 * n) (hwa : al % 4 = 0) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      OperandReady s base n a al ∧ OperandReady t base n a al ∧
      pointerValue base s a = pointerValue base t a ∧ pointerValue base s b = pointerValue base t b)
      (.seq (Core.load n al (slot n i) a) (Core.load n bl (slot n j) b))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  intro s t tr ur sf tf ⟨S, T, A₁, A₂, Pa, Pb⟩ E F
  have B := slot_bound (n := n) hi
  have C := VG.Proof.Dsa.X86.Layout.context_bound hn
  have H : 8256 ≤ size := hz
  have fit : slot n i + 8 * n ≤ size := by simp only [stride] at B; omega
  cases E with
  | seq E₁ E₂ =>
    cases F with
    | seq F₁ F₂ =>
      obtain ⟨Trace₁, _⟩ := coreLoad_relCT n al (slot n i) a base size hz _ _ _ _ _ _ ⟨S, T, Pa⟩ E₁ F₁
      obtain ⟨_, K₁, O₁⟩ := wp_result (coreLoad_ok S hz fit ha4 ha hwa A₁.toReadableComponent (A₁.slot hi)) E₁
      obtain ⟨_, K₂, O₂⟩ := wp_result (coreLoad_ok T hz fit ha4 ha hwa A₂.toReadableComponent (A₂.slot hi)) F₁
      have Hn : contextBytes n ≤ 8192 := by omega
      have P₁ := pointerValue_keep K₁ (by decide) (slotOutside_whole O₁ hi) Hn b
      have P₂ := pointerValue_keep K₂ (by decide) (slotOutside_whole O₂ hi) Hn b
      obtain ⟨Trace₂, Agree⟩ := coreLoad_relCT n bl (slot n j) b base size hz _ _ _ _ _ _
        ⟨S.of_keeps K₁ (by decide), T.of_keeps K₂ (by decide), P₁.trans (Pb.trans P₂.symm)⟩ E₂ F₂
      exact ⟨by rw [Trace₁, Trace₂], Agree⟩

end VG.Proof.Dsa.X86
