import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Stream

/-!
# BLAKE2s on x86-64 with AVX

A variant of `Blake2s` on x86-64 (see `TCB/Emit.lean`):
`vg_blake2s_compress_avx`, the work vector in four 128-bit registers, whose
`VEX.128` instructions need AVX alone; the streaming functions calling it
need it too.
-/

namespace VG.Variants.Blake2s.X86_64.Avx

def variant : Proof.Blake2.X86_64.BackendS where
  suffix := "_avx"
  features := ["avx"]
  code := Impl.Blake2.X86_64.Avx.compress
  callee := Proof.Blake2.X86_64.Avx.callee
  verified := Proof.Blake2.X86_64.Avx.compress_verified
  spSafe := Code.all_of_allInstrs (by lit_decide)
  updateCT := Proof.Blake2.X86_64.Avx.update_ct
  finalizeCT := Proof.Blake2.X86_64.Avx.finalize_ct
  updateMxcsr := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).allInstrs _ = true
    lit_decide
  finalizeMxcsr := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).allInstrs _ =
      true
    lit_decide
  updateSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).allInstrs _ = true
    lit_decide)
  finalizeSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).allInstrs _ =
      true
    lit_decide)
  updateDepth := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).x86_64Depth ≤ 8
    lit_decide
  finalizeDepth := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.s Proof.Blake2.X86_64.Avx.avx).x86_64Depth ≤ 8
    lit_decide

end VG.Variants.Blake2s.X86_64.Avx
