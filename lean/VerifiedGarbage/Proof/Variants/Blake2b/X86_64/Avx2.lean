module

public import VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Stream
public import VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Compress
public import VerifiedGarbage.Proof.Blake2.X86_64.Backend
import VerifiedGarbage.Proof.Framework.Lit

/-!
# BLAKE2b on x86-64 with AVX2: the variant's code and proofs

The variant `VG.Variants.Blake2b.X86_64.Avx2.variant`
(`Variants/Blake2b/X86_64/Avx2.lean`), with the proofs its interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.Blake2b.X86_64.Avx2

def variant : Proof.Blake2.X86_64.Backend where
  suffix := "_avx2"
  features := ["avx", "avx2"]
  code := Impl.Blake2.X86_64.Avx2.compress
  callee := Proof.Blake2.X86_64.Avx2.callee
  verified := Proof.Blake2.X86_64.Avx2.compress_verified
  spSafe := Code.all_of_allInstrs (by lit_decide)
  updateCT := Proof.Blake2.X86_64.Avx2.update_ct
  finalizeCT := Proof.Blake2.X86_64.Avx2.finalize_ct
  updateMxcsr := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.b Proof.Blake2.X86_64.Avx2.avx2).allInstrs _ = true
    lit_decide
  finalizeMxcsr := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b Proof.Blake2.X86_64.Avx2.avx2).allInstrs _ =
      true
    lit_decide
  updateSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.b Proof.Blake2.X86_64.Avx2.avx2).allInstrs _ = true
    lit_decide)
  finalizeSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b Proof.Blake2.X86_64.Avx2.avx2).allInstrs _ =
      true
    lit_decide)
  updateDepth := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.b Proof.Blake2.X86_64.Avx2.avx2).x86_64Depth ≤ 8
    lit_decide
  finalizeDepth := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b Proof.Blake2.X86_64.Avx2.avx2).x86_64Depth ≤ 8
    lit_decide

end VG.Proof.Variants.Blake2b.X86_64.Avx2
