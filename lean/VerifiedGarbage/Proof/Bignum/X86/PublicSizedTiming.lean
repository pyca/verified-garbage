module
public import VerifiedGarbage.Proof.Bignum.X86.PublicPair
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.X86.PublicImportTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicApplyTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicExportTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicPrepared
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # The complete fixed-width public RSA operation keeps the input secret -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

theorem publicSized_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => PublicPair base bytes len args s t ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)) len = true)
      (PublicFn.sized (Spec.Rsa.modulusWords len)) (fun _ _ => True) := by
  have Prepare : RelCT isa (PublicPair base bytes len args)
      (.seq (PublicFn.importNumbers (Spec.Rsa.modulusWords len)) (PublicFn.acceptAndPower (Spec.Rsa.modulusWords len)))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply VG.RelCT.seq (importNumbers_relCT base bytes len args)
    apply (acceptAndPower_relCT (Spec.Rsa.modulusWords len)).mono
    · intro s t H
      exact agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact H.agree.rf.1 _ (by decide))
    · exact fun _ _ h => h
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨H, Vs, Vt⟩ E F
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (Prepare _ _ _ _ _ _ H E1 F1).1
      obtain ⟨Is, SPs, a, Ms⟩ := wp_result (PublicContext.publicPrepared_ok H.left Vs) E1
      obtain ⟨It, SPt, b, Mt⟩ := wp_result (PublicContext.publicPrepared_ok H.right Vt) F1
      have Next : PublicPair base bytes len args _ _ := ⟨Is, It, SPs.trans (H.sp.trans SPt.symm)⟩
      have T2 := exportResult_trace Next H.left.dimensions.1 H.left.space a b Ms Mt E2 F2
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.Bignum.X86
