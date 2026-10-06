import VerifiedGarbage.Proof.Blake2.X86_64.Avx512.Stream

/-!
# BLAKE2b on x86-64 with AVX-512

A variant of `Blake2b` on x86-64 (see `TCB/Emit.lean`):
`vg_blake2b_compress_avx512`, the work vector in four 256-bit registers and
each rotation one `vprorq` (its EVEX.256 form), which needs AVX, AVX2,
AVX512F and AVX512VL; the streaming functions calling it, and everything
built on them (Argon2's H′ and derivation, whose instances are named by
`Emit.qualifiedName`, e.g. `vg_argon2_blake2b_avx512_g_avx512`), need them
too.
-/

namespace VG.Variants.Blake2b.X86_64.Avx512

def variant : Proof.Blake2.X86_64.Backend where
  suffix := "_avx512"
  features := ["avx", "avx2", "avx512f", "avx512vl"]
  code := Impl.Blake2.X86_64.Avx512.compress
  callee := Proof.Blake2.X86_64.Avx512.callee
  verified := Proof.Blake2.X86_64.Avx512.compress_verified
  spSafe := Code.all_of_allInstrs (by lit_decide)
  updateCT := Proof.Blake2.X86_64.Avx512.update_ct
  finalizeCT := Proof.Blake2.X86_64.Avx512.finalize_ct
  updateMxcsr := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.b Proof.Blake2.X86_64.Avx512.avx512).allInstrs _ = true
    lit_decide
  finalizeMxcsr := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b Proof.Blake2.X86_64.Avx512.avx512).allInstrs _ =
      true
    lit_decide
  updateSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.b Proof.Blake2.X86_64.Avx512.avx512).allInstrs _ = true
    lit_decide)
  finalizeSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b Proof.Blake2.X86_64.Avx512.avx512).allInstrs _ =
      true
    lit_decide)
  updateDepth := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.b Proof.Blake2.X86_64.Avx512.avx512).x86_64Depth ≤ 8
    lit_decide
  finalizeDepth := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b Proof.Blake2.X86_64.Avx512.avx512).x86_64Depth ≤ 8
    lit_decide

end VG.Variants.Blake2b.X86_64.Avx512
