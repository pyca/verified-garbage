module

public import VerifiedGarbage.Proof.Blake2.X86_64.Backend
public import VerifiedGarbage.Proof.Blake2.X86_64.Compress
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
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
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# BLAKE2b on baseline x86-64: the variant's code and proofs

The variant `VG.Variants.Blake2b.X86_64.Scalar.variant`
(`Variants/Blake2b/X86_64/Scalar.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.Blake2b.X86_64.Scalar

def variant : Proof.Blake2.X86_64.Backend where
  suffix := ""
  features := []
  code := Impl.Blake2.X86_64.compress Spec.Blake2.b
  callee := Proof.Blake2.X86_64.Stream.calleeB
  verified := Proof.Blake2.X86_64.compressB_verified
  spSafe := Code.all_of_allInstrs (by lit_decide)
  updateCT := Proof.Blake2.X86_64.Stream.updateB_ct
  finalizeCT := Proof.Blake2.X86_64.Stream.finalizeB_ct
  updateMxcsr := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.b).allInstrs _ = true
    lit_decide
  finalizeMxcsr := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b).allInstrs _ = true
    lit_decide
  updateSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.b).allInstrs _ = true
    lit_decide)
  finalizeSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b).allInstrs _ = true
    lit_decide)
  updateDepth := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.b).x86_64Depth ≤ 8
    lit_decide
  finalizeDepth := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b).x86_64Depth ≤ 8
    lit_decide

end VG.Proof.Variants.Blake2b.X86_64.Scalar
