module
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Common
public import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Lit

import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Compress
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Common
meta import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Lit
meta import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Compress
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# BLAKE2s on x86-64 with AVX: the streaming functions

`update` and `finalize` calling `vg_blake2s_compress_avx` (`avx`): what
their proofs of correctness need of it (`callee`), and their constant time,
by the same taint analysis as with the scalar compression function
(`Proof/Blake2/X86_64/Stream/CT.lean`), of the code with this callee.
-/

@[expose] public section

namespace VG.Proof.Blake2.X86_64.Avx

open VG VG.X86_64 VG.Spec.Blake2
open VG.Proof.Blake2.X86_64.Stream (CalleeOk τUpdate τFinalize update_agree finalize_agree okS)

theorem callee : CalleeOk s Impl.Blake2.X86_64.Avx.compress :=
  CalleeOk.of_verified compress_correct (by lit_decide) (by lit_decide)

theorem update_ct : ConstantTime isa (updateX86_64 s).pre (updateX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.update s avx) :=
  VG.Taint.constantTime (A := taint) (τUpdate 32) (fun _ _ h₁ h₂ hp => update_agree okS h₁ h₂ hp)
    (by taint_decide)

theorem finalize_ct : ConstantTime isa (finalizeX86_64 s).pre (finalizeX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.finalize s avx) :=
  VG.Taint.constantTime (A := taint) (τFinalize 32)
    (fun _ _ h₁ h₂ hp => finalize_agree okS h₁ h₂ hp) (by taint_decide)

end VG.Proof.Blake2.X86_64.Avx
