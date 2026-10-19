module
public import VerifiedGarbage.Proof.Argon2.X86_64.Taint
public import VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Lit
public import VerifiedGarbage.Proof.Blake2.X86_64.Lit
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Common

import VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Compress
meta import VerifiedGarbage.Proof.Blake2.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Argon2.X86_64.Compress
import VerifiedGarbage.Proof.Argon2.X86_64.Finish
import VerifiedGarbage.Proof.Argon2.X86_64.Mix
import VerifiedGarbage.Proof.Blake2.X86_64.Backend
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
meta import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
meta import VerifiedGarbage.Proof.Argon2.Permutation
meta import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Compress
meta import VerifiedGarbage.Proof.Argon2.X86_64.Compress
meta import VerifiedGarbage.Proof.Argon2.X86_64.Finish
meta import VerifiedGarbage.Proof.Argon2.X86_64.Mix
meta import VerifiedGarbage.Proof.Blake2.X86_64.Backend
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Sha256.Stream

/-!
# BLAKE2b on x86-64 with AVX2: the streaming functions

`update` and `finalize` calling `vg_blake2b_compress_avx2` (`avx2`): what
their proofs of correctness need of it (`callee`), and their constant time,
by the same taint analysis as with the scalar compression function
(`Proof/Blake2/X86_64/Stream/CT.lean`), of the code with this callee.
-/

@[expose] public section

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
