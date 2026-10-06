import VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Blake2.X86_64.Backend

/-!
# BLAKE2b on x86-64 with AVX2: the streaming functions

`update` and `finalize` calling `vg_blake2b_compress_avx2` (`avx2`): what
their proofs of correctness need of it (`callee`), and their constant time,
by the same taint analysis as with the scalar compression function
(`Proof/Blake2/X86_64/Stream/CT.lean`), of the code with this callee.
-/

namespace VG.Proof.Blake2.X86_64.Avx2

open VG VG.X86_64 VG.Spec.Blake2
open VG.Proof.Blake2.X86_64.Stream (CalleeOk τUpdate τFinalize update_agree finalize_agree okB)

theorem callee : CalleeOk b Impl.Blake2.X86_64.Avx2.compress :=
  CalleeOk.of_verified compress_correct (by lit_decide) (by lit_decide)

theorem update_ct : ConstantTime isa (updateX86_64 b).pre (updateX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.update b avx2) :=
  VG.Taint.constantTime (A := taint) (τUpdate 64) (fun _ _ h₁ h₂ hp => update_agree okB h₁ h₂ hp)
    (by taint_decide)

theorem finalize_ct : ConstantTime isa (finalizeX86_64 b).pre (finalizeX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.finalize b avx2) :=
  VG.Taint.constantTime (A := taint) (τFinalize 64)
    (fun _ _ h₁ h₂ hp => finalize_agree okB h₁ h₂ hp) (by taint_decide)

end VG.Proof.Blake2.X86_64.Avx2
