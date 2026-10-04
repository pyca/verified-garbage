import VerifiedGarbage.Proof.Blake2.X86_64.BackendS

/-! # BLAKE2s on baseline x86-64 -/

namespace VG.Variants.Blake2s.X86_64.Scalar

def variant : Proof.Blake2.X86_64.BackendS where
  suffix := ""
  features := []
  code := Impl.Blake2.X86_64.compress Spec.Blake2.s
  callee := Proof.Blake2.X86_64.Stream.calleeS
  verified := Proof.Blake2.X86_64.compressS_verified
  spSafe := Code.all_of_allInstrs (by lit_decide)
  updateCT := Proof.Blake2.X86_64.Stream.updateS_ct
  finalizeCT := Proof.Blake2.X86_64.Stream.finalizeS_ct
  updateMxcsr := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.s).allInstrs _ = true
    lit_decide
  finalizeMxcsr := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s).allInstrs _ = true
    lit_decide
  updateSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.s).allInstrs _ = true
    lit_decide)
  finalizeSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s).allInstrs _ = true
    lit_decide)
  updateDepth := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.s).x86_64Depth ≤ 8
    lit_decide
  finalizeDepth := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s).x86_64Depth ≤ 8
    lit_decide

end VG.Variants.Blake2s.X86_64.Scalar
