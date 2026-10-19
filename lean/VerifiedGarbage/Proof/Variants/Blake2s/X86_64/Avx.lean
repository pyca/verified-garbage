module

public import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Stream
public import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Compress
public import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# BLAKE2s on x86-64 with AVX: the variant's code and proofs

The variant `VG.Variants.Blake2s.X86_64.Avx.variant`
(`Variants/Blake2s/X86_64/Avx.lean`), with the proofs its interface asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.Blake2s.X86_64.Avx

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

end VG.Proof.Variants.Blake2s.X86_64.Avx
