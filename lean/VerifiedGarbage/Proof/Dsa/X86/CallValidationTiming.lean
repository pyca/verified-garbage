module

public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Dsa.X86.Validate
import VerifiedGarbage.Proof.Dsa.X86.ValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.StageChecks

/-! # Validation stages retain the public call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callRange_relCT (L : CallLayout) (len : Nat) (modulus : Field) (input : Pointer) (aboveOne : Bool)
    (M : CallOperand L (.input modulus) len) (I : CallOperand L input len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.range len modulus input aboveOne) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · apply (validateRange_relCT len modulus input aboveOne L.base L.size L.saved h4 hmax hw4).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨H.1.moduli.scr, H.2.moduli.scr, H.1.operand M (by omega) (by omega),
      H.2.operand M (by omega) (by omega), H.pointer M, H.pointer I⟩
  · intro s R
    exact WP.mono (stageRange_ok R.moduli h4 hmax hw4 (R.operand M (by omega) (by omega))
      (R.operand I (by omega) (by omega)) aboveOne) fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

theorem callEqual_relCT (L : CallLayout) (len : Nat) (a b : Pointer)
    (A : CallOperand L a len) (B : CallOperand L b len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.equalValues len a b) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · apply (validateEqual_relCT len a b L.base L.size L.saved h4 hmax hw4).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨H.1.moduli.scr, H.2.moduli.scr, H.1.operand A (by omega) (by omega),
      H.2.operand A (by omega) (by omega), H.pointer A, H.pointer B⟩
  · intro s R
    exact WP.mono (stageEqual_ok R.moduli h4 hmax hw4 (R.operand A (by omega) (by omega))
      (R.operand B (by omega) (by omega))) fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

theorem callOne_relCT (L : CallLayout) (len : Nat) (input : Pointer)
    (I : CallOperand L input len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.isOne len input) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · exact (validateOne_relCT len input L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer I⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageOne_ok R.moduli h4 hmax hw4 (R.operand I (by omega) (by omega)))
      fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

theorem callZero_relCT (L : CallLayout) (len : Nat) (input : Pointer) (wantNonzero : Bool)
    (I : CallOperand L input len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.zero len input wantNonzero) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · exact (validateZero_relCT len input wantNonzero L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer I⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageZero_ok R.moduli h4 hmax hw4 (R.operand I (by omega) (by omega)) wantNonzero)
      fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

end VG.Proof.Dsa.X86
