import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Argon2.X86_64.CompressImpl

/-!
# Argon2's G on x86-64 with AVX2

A variant of `Argon2Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_argon2_compress_avx2`, which needs AVX and AVX2; the derivation calling
it needs them too.
-/

namespace VG.Variants.Argon2Compress.X86_64.Avx2

open VG VG.X86_64 VG.Proof.Argon2.X86_64

@[instance_reducible] def variant : CompressImpl where
  suffix := "_avx2"
  features := ["avx", "avx2"]
  code := Impl.Argon2.X86_64.Avx2.compress
  correct := Avx2.compress_correct
  ct := Avx2.compress_ct
  noSp := noSp_of_allInstrs (by lit_decide)
  depth := by lit_decide
  ctl := Avx2.compress_ctl
  spSafe := by lit_decide

end VG.Variants.Argon2Compress.X86_64.Avx2
