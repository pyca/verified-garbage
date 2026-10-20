module

public import VerifiedGarbage.Proof.Dsa.X86.ArithmeticHead
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreSetupTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreInputsTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Constant-time preparation of a binary modular operation -/

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
