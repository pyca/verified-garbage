module

public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Blake2.X86.Blake2b
public import VerifiedGarbage.Proof.Blake2.X86.Blake2s
public import VerifiedGarbage.Impl.Blake2.X86.Fn
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Blake2.X86.LitB
import VerifiedGarbage.Proof.Blake2.X86.LitS
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Blake2.X86.Blake2b
meta import VerifiedGarbage.Proof.Blake2.X86.Blake2s
meta import VerifiedGarbage.Impl.Blake2.X86.Fn
meta import VerifiedGarbage.Proof.Blake2.Scratch
meta import VerifiedGarbage.Proof.Blake2.X86.LitB
meta import VerifiedGarbage.Proof.Blake2.X86.LitS

/-!
# BLAKE2's streaming functions on x86 (32-bit), without secret residue

The code as emitted (`Impl.Blake2.X86.Fn`) meets each function's contract in
constant time and returns without secret residue. `init` calls nothing and
has no frame (`X86.Scrub.verifiedScrubbed`). `update` and `finalize` zero
the stack their contracts reserve below `esp`, which their scratch frame and
the compression function's calls use, given that their postconditions read
the memory on return only within their buffers (`Proof/Blake2/Scratch.lean`,
which the other targets use too) (`X86.Scrub.verifiedScrubbedF`).
-/

@[expose] public section

namespace VG.Proof.Blake2.X86.Scrub

open VG VG.X86 VG.X86.Scrub VG.Spec.Blake2

theorem initB_scrubbed :
    VerifiedScrubbed target (Impl.Blake2.X86.Fn.init b) (initBContract X86.abi) 0 :=
  verifiedScrubbed (api := initBApi)
    { code := Impl.Blake2.X86.Stream.init b
      verified := Proof.Blake2.X86.B.initB_verified }

theorem updateB_scrubbed :
    VerifiedScrubbed target Impl.Blake2.X86.Fn.updateB (updateBContract X86.abi (32 + 604)) 0 :=
  verifiedScrubbedF (api := updateBApi)
    { code := Impl.StackScratch.X86.withStackScratch 604 5
        (Impl.Blake2.X86.Stream.update 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress)
      verified := Proof.Blake2.X86.B.updateB_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateBPost_out _))

theorem finalizeB_scrubbed :
    VerifiedScrubbed target Impl.Blake2.X86.Fn.finalizeB (finalizeBContract X86.abi (32 + 600)) 0 :=
  verifiedScrubbedF (api := finalizeBApi)
    { code := Impl.StackScratch.X86.withStackScratch 600 4
        (Impl.Blake2.X86.Stream.finalize 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress)
      verified := Proof.Blake2.X86.B.finalizeB_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeBPost_out _))

theorem initS_scrubbed :
    VerifiedScrubbed target (Impl.Blake2.X86.Fn.init s) (initSContract X86.abi) 0 :=
  verifiedScrubbed (api := initSApi)
    { code := Impl.Blake2.X86.Stream.init s
      verified := Proof.Blake2.X86.S.init_verified }

theorem updateS_scrubbed :
    VerifiedScrubbed target Impl.Blake2.X86.Fn.updateS (updateSContract X86.abi (32 + 604)) 0 :=
  verifiedScrubbedF (api := updateSApi)
    { code := Impl.StackScratch.X86.withStackScratch 604 5
        (Impl.Blake2.X86.Stream.update 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress)
      verified := Proof.Blake2.X86.S.update_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateSPost_out _))

theorem finalizeS_scrubbed :
    VerifiedScrubbed target Impl.Blake2.X86.Fn.finalizeS (finalizeSContract X86.abi (32 + 600)) 0 :=
  verifiedScrubbedF (api := finalizeSApi)
    { code := Impl.StackScratch.X86.withStackScratch 600 4
        (Impl.Blake2.X86.Stream.finalize 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress)
      verified := Proof.Blake2.X86.S.finalize_framed }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeSPost_out _))

end VG.Proof.Blake2.X86.Scrub
