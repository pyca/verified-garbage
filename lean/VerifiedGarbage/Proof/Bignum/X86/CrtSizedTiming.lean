module

public import VerifiedGarbage.Proof.Bignum.X86.CrtImportTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtExportTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtPrepared
public import VerifiedGarbage.Proof.Bignum.X86.CrtNarrowTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtValidated
public import VerifiedGarbage.Proof.Bignum.X86.CrtValidationTiming

/-! # The complete fixed-width CRT operation keeps every private component secret -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

theorem sized_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (Pair base bytes len args) (Crt.sized (Spec.Rsa.modulusWords len)) (fun _ _ => True) := by
  have Prepare : RelCT isa (Pair base bytes len args)
      (.seq (Crt.importComponents (Spec.Rsa.modulusWords len))
        (.seq (Crt.validate (Spec.Rsa.modulusWords len)) (Crt.compute (Spec.Rsa.modulusWords len))))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    intro s t tr ur sf tf H E F
    cases E with | @seq _ _ _ u _ _ _ E₁ E' => cases F with | @seq _ _ _ w _ _ _ F₁ F' =>
    cases E' with | @seq _ _ _ u' _ _ _ E₂ E₃ => cases F' with | @seq _ _ _ w' _ _ _ F₂ F₃ =>
    have T₁ := importComponents_relCT base bytes len args _ _ _ _ _ _ H E₁ F₁
    have T₂ := validate_relCT (Spec.Rsa.modulusWords len) _ _ _ _ _ _
      (agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact T₁.2.agree.rf.1 _ (by decide)))
      E₂ F₂
    obtain ⟨Is, SPs, As⟩ := wp_result (validated_ok H.left) (.seq E₁ E₂)
    obtain ⟨It, SPt, At⟩ := wp_result (validated_ok H.right) (.seq F₁ F₂)
    have T₃ := compute_relCT base bytes len args _ _ _ _ _ _
      ⟨T₂.2, ⟨Is, It, SPs.trans (H.sp.trans SPt.symm)⟩, As, At⟩ E₃ F₃
    rw [T₁.1, T₂.1, T₃.1]
    exact ⟨rfl, T₃.2⟩
  apply VG.RelCT.assoc
  intro s t tr ur sf tf H E F
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (Prepare _ _ _ _ _ _ H E1 F1).1
      obtain ⟨Is, SPs, a, Ms⟩ := wp_result (prepared_ok H.left) E1
      obtain ⟨It, SPt, b, Mt⟩ := wp_result (prepared_ok H.right) F1
      have Next : Pair base bytes len args _ _ := ⟨Is, It, SPs.trans (H.sp.trans SPt.symm)⟩
      have T2 := exportResult_trace Next H.left.dimensions.1 H.left.space a b Ms Mt E2 F2
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.Bignum.X86.Crt
