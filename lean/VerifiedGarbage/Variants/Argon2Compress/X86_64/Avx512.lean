import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Compress
import VerifiedGarbage.Proof.Argon2.X86_64.CompressImpl

/-!
# Argon2's G on x86-64 with AVX-512

A variant of `Argon2Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_argon2_compress_avx512`, which needs AVX512F (and AVX, for its closing
`vzeroupper`); the derivation calling it needs them too.
-/

namespace VG.Variants.Argon2Compress.X86_64.Avx512

open VG VG.X86_64 VG.Proof.Argon2.X86_64

@[instance_reducible] def variant : CompressImpl where
  suffix := "_avx512"
  features := ["avx", "avx512f"]
  code := Impl.Argon2.X86_64.Avx512.compress
  correct := Avx512.compress_correct
  ct := Avx512.compress_ct
  noSp := noSp_of_allInstrs (by lit_decide)
  depth := by lit_decide
  ctl := Avx512.compress_ctl
  spSafe := by lit_decide

end VG.Variants.Argon2Compress.X86_64.Avx512
