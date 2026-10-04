import VerifiedGarbage.Proof.Argon2.X86_64.Compress
import VerifiedGarbage.Proof.Argon2.X86_64.CompressImpl

/-!
# Argon2's G on baseline x86-64

A variant of `Argon2Compress` on x86-64 (see `TCB/Emit.lean`):
`vg_argon2_compress`, in the baseline ISA, which the derivation calls.
-/

namespace VG.Variants.Argon2Compress.X86_64.Scalar

open VG VG.X86_64 VG.Proof.Argon2.X86_64

@[instance_reducible] def variant : CompressImpl where
  suffix := ""
  features := []
  code := Impl.Argon2.X86_64.compress
  correct := compress_correct
  ct := compress_ct
  noSp := noSp_of_allInstrs (by lit_decide)
  depth := by lit_decide
  ctl := ctlOk_of_allInstrs (by lit_decide)
  spSafe := by lit_decide

end VG.Variants.Argon2Compress.X86_64.Scalar
