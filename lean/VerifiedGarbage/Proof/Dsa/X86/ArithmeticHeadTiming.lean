module

public import VerifiedGarbage.Proof.Dsa.X86.ArithmeticHead
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Dsa.X86.CoreSetupTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
/-! # Constant-time preparation of a binary modular operation -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/CoreInputsTiming.lean`, which only this module imported.
section

/-! # Loading two arithmetic operands without revealing their values -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def ArithmeticAgree (base : Addr) (size len bl : Nat) (modulus : Field) (a b : Pointer) (s t : State) : Prop :=
  ArithmeticPre base size len bl modulus a b s ∧ ArithmeticPre base size len bl modulus a b t ∧
  pointerValue base s (.input modulus) = pointerValue base t (.input modulus) ∧
  pointerValue base s a = pointerValue base t a ∧ pointerValue base s b = pointerValue base t b

theorem arithmeticHead_relCT (base : Addr) (size len bl : Nat) (modulus : Field) (a b : Pointer)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (ArithmeticAgree base size len bl modulus a b) (arithmeticHead len bl modulus a b)
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  intro s t tr ur sf tf ⟨P, Q, Mod, Left, Right⟩ E F
  have hn : (len + 7) / 8 ≤ 48 := by omega
  have Hn : contextBytes ((len + 7) / 8) ≤ 8192 :=
    Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (by decide)
  cases E with
  | seq E₀ E₁ =>
    cases F with
    | seq F₀ F₁ =>
      obtain ⟨Trace₀, _⟩ := coreSetup_relCT len modulus base size hz _ _ _ _ _ _ ⟨P.scr, Q.scr, Mod⟩ E₀ F₀
      obtain ⟨C₁, _, _, O₁, K₁⟩ := wp_result (coreSetup_ok P.scr hz rfl h4 hmax hw4
        P.modulusReady.toReadableComponent (P.modulusReady.slot (by decide)) rfl P.large P.odd) E₀
      obtain ⟨C₂, _, _, O₂, K₂⟩ := wp_result (coreSetup_ok Q.scr hz rfl h4 hmax hw4
        Q.modulusReady.toReadableComponent (Q.modulusReady.slot (by decide)) rfl Q.large Q.odd) F₀
      have A₁ := P.leftReady.keep K₁ (by decide) O₁ hn
      have A₂ := Q.leftReady.keep K₂ (by decide) O₂ hn
      have PL := (pointerValue_keep K₁ (by decide) O₁ Hn a).trans
        (Left.trans (pointerValue_keep K₂ (by decide) O₂ Hn a).symm)
      have PR := (pointerValue_keep K₁ (by decide) O₁ Hn b).trans
        (Right.trans (pointerValue_keep K₂ (by decide) O₂ Hn b).symm)
      obtain ⟨Trace₁, Agree⟩ := coreInputs_relCT ((len + 7) / 8) len bl a b base size hz hn h4 (by omega) hw4
        _ _ _ _ _ _ ⟨_, _, C₁, C₂, A₁, A₂, PL, PR⟩ E₁ F₁
      exact ⟨by rw [Trace₀, Trace₁], Agree⟩

end VG.Proof.Dsa.X86
