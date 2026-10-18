module

public import VerifiedGarbage.Proof.Bignum.X86.CrtImportTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtExportTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtPrepared

/-! # The complete fixed-width CRT operation keeps every private component secret -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

theorem sized_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (Pair base bytes len args) (Crt.sized (Spec.Rsa.modulusWords len)) (fun _ _ => True) := by
  have Prepare (hn : 0 < Spec.Rsa.modulusWords len) : RelCT isa (Pair base bytes len args)
      (.seq (Crt.importComponents (Spec.Rsa.modulusWords len))
        (.seq (Crt.validate (Spec.Rsa.modulusWords len)) (Crt.compute (Spec.Rsa.modulusWords len))))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply VG.RelCT.seq (importComponents_relCT base bytes len args)
    apply (VG.RelCT.seq (validate_relCT (Spec.Rsa.modulusWords len))
      (compute_relCT (Spec.Rsa.modulusWords len) hn)).mono
    · intro s t H
      exact agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact H.agree.rf.1 _ (by decide))
    · exact fun _ _ h => h
  apply VG.RelCT.assoc
  intro s t tr ur sf tf H E F
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (Prepare H.left.dimensions.1 _ _ _ _ _ _ H E1 F1).1
      obtain ⟨Is, SPs, a, Ms⟩ := wp_result (prepared_ok H.left) E1
      obtain ⟨It, SPt, b, Mt⟩ := wp_result (prepared_ok H.right) F1
      have Next : Pair base bytes len args _ _ := ⟨Is, It, SPs.trans (H.sp.trans SPt.symm)⟩
      have T2 := exportResult_trace Next H.left.dimensions.1 H.left.space a b Ms Mt E2 F2
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.Bignum.X86.Crt
