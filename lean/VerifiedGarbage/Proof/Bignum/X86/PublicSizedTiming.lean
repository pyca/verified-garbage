module
public import VerifiedGarbage.Proof.Bignum.X86.PublicPair
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.PublicImportTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicApplyTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicExportTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicPrepared

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.PublicImport

/-! # The complete fixed-width public RSA operation keeps the input secret -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

theorem publicSized_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => PublicPair base bytes len args s t ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)) len = true ∧
      val32 s.mem base 128 2 = val32 t.mem base 128 2)
      (PublicFn.sized (Spec.Rsa.modulusWords len)) (fun _ _ => True) := by
  have ready {σ u : State} {tr : List Leak} (I : PublicInputs base bytes len args σ)
      (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (byteAddr (args 2)) len)) len = true)
      (E : Exec isa (PublicFn.importNumbers (Spec.Rsa.modulusWords len)) σ tr u) :
      PublicReady (Spec.Rsa.modulusWords len) bytes base u ∧
        val32 u.mem base 128 2 = val32 σ.mem base 128 2 := by
    have dims := I.dimensions
    have facts := valid_facts valid I.lower
    obtain ⟨N, -, O, K⟩ := wp_result (PublicContext.importNumbers_ok I.scratch dims.1 I.space
      (by have := I.lower; omega) dims.2.2
      (I.stack 2 (by decide)) (by rw [← I.nLen]; exact I.stack 3 (by decide))
      (I.stack 6 (by decide)) (by rw [← I.inLen]; exact I.stack 7 (by decide))
      I.nFit I.inFit I.nRead I.inRead I.nApart I.inApart) E
    exact ⟨⟨I.scratch.of_keeps K (by decide), dims.1, dims.2.1, I.space, _, N, facts.2.1, facts.1⟩,
      VG.Proof.Mont.Outside.val32 O (.inl (by decide)) (by decide)⟩
  have Prepare : RelCT isa (fun s t => PublicPair base bytes len args s t ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)) len = true ∧
      val32 s.mem base 128 2 = val32 t.mem base 128 2)
      (.seq (PublicFn.importNumbers (Spec.Rsa.modulusWords len)) (PublicFn.acceptAndPower (Spec.Rsa.modulusWords len)))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    intro s t tr ur sf tf ⟨H, Vs, Vt, Ex⟩ E F
    cases E with | seq E₁ E₂ => cases F with | seq F₁ F₂ =>
    have T₁ := importNumbers_relCT base bytes len args _ _ _ _ _ _ H E₁ F₁
    obtain ⟨Rs, Es⟩ := ready H.left Vs E₁
    obtain ⟨Rt, Et⟩ := ready H.right Vt F₁
    have A : Public _ _ := agree_regs (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; exact T₁.2.agree.rf.1 _ (by decide))
    have T₂ := acceptAndPower_relCT (Spec.Rsa.modulusWords len) bytes base _ _ _ _ _ _
      ⟨A, Rs, Rt, by rw [Es, Et, Ex]⟩ E₂ F₂
    rw [T₁.1, T₂.1]
    exact ⟨rfl, T₂.2⟩
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨H, Vs, Vt, Ex⟩ E F
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (Prepare _ _ _ _ _ _ ⟨H, Vs, Vt, Ex⟩ E1 F1).1
      obtain ⟨Is, SPs, a, Ms⟩ := wp_result (PublicContext.publicPrepared_ok H.left Vs) E1
      obtain ⟨It, SPt, b, Mt⟩ := wp_result (PublicContext.publicPrepared_ok H.right Vt) F1
      have Next : PublicPair base bytes len args _ _ := ⟨Is, It, SPs.trans (H.sp.trans SPt.symm)⟩
      have T2 := exportResult_trace Next H.left.dimensions.1 H.left.space a b Ms Mt E2 F2
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.Bignum.X86
