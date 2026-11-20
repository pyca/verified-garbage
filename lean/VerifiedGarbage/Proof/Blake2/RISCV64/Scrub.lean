module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Verified
public import VerifiedGarbage.Proof.Blake2.Scratch
public import VerifiedGarbage.Proof.Blake2.PostOut
public import VerifiedGarbage.Impl.Blake2.RISCV64.Fn
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit

/-!
# BLAKE2b and BLAKE2s on RISC-V, without secret residue

Each of the streaming functions as emitted (`Impl.Blake2.RISCV64.Fn`): the
function followed by `Impl.Scrub.RISCV64.scrubTail`, which clears the
caller-saved registers and the stack its frames used. Each theorem below
states that one meets its contract in constant time and returns without
secret residue (`VerifiedScrubbed`, by `RISCV64.Scrub.verifiedScrubbed`),
which is what its registration binds. Their postconditions read the memory
on return only within their buffers (`Proof/Blake2/PostOut.lean`,
`Proof/Blake2/Scratch.lean`). Argon2 calls `vg_blake2b_init`'s code as the
internal `vg_blake2b_init_core` (`Impl.Argon2.RISCV64.HPrime.initName`), and
BLAKE2's update and finalize as their own internal `_scratch` functions.
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub

/-- `vg_blake2b_init` as emitted (`Impl.Blake2.RISCV64.Fn.initB`) meets its contract in
constant time and returns without secret residue. -/
theorem initB_scrubbed :
    VerifiedScrubbed target Impl.Blake2.RISCV64.Fn.initB (Spec.Blake2.initBContract RISCV64.abi) 0 :=
  verifiedScrubbed (api := Spec.Blake2.initBApi) (W := 0)
    { code := Impl.Blake2.RISCV64.Stream.init Spec.Blake2.b, verified := Proof.Blake2.RISCV64.Stream.initB_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.initBPost_out 64))
    (show scrubSide (Impl.Blake2.RISCV64.Stream.init Spec.Blake2.b) 0 0 [] = true by lit_decide)

/-- `vg_blake2b_update` as emitted (`Impl.Blake2.RISCV64.Fn.updateB`) meets its contract in
constant time and returns without secret residue. -/
theorem updateB_scrubbed :
    VerifiedScrubbed target Impl.Blake2.RISCV64.Fn.updateB (Spec.Blake2.updateBContract RISCV64.abi 336) 0 :=
  verifiedScrubbed (api := Spec.Blake2.updateBApi) (W := 336)
    { code := Impl.Blake2.RISCV64.Stream.update Spec.Blake2.b, verified := Proof.Blake2.RISCV64.Stream.updateB_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateBPost_out 64))
    (show scrubSide (Impl.Blake2.RISCV64.Stream.update Spec.Blake2.b) 336 0 [] = true by lit_decide)

/-- `vg_blake2b_finalize` as emitted (`Impl.Blake2.RISCV64.Fn.finalizeB`) meets its contract in
constant time and returns without secret residue. -/
theorem finalizeB_scrubbed :
    VerifiedScrubbed target Impl.Blake2.RISCV64.Fn.finalizeB (Spec.Blake2.finalizeBContract RISCV64.abi 336) 0 :=
  verifiedScrubbed (api := Spec.Blake2.finalizeBApi) (W := 336)
    { code := Impl.Blake2.RISCV64.Stream.finalize Spec.Blake2.b, verified := Proof.Blake2.RISCV64.Stream.finalizeB_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeBPost_out 64))
    (show scrubSide (Impl.Blake2.RISCV64.Stream.finalize Spec.Blake2.b) 336 0 [] = true by lit_decide)

/-- `vg_blake2s_init` as emitted (`Impl.Blake2.RISCV64.Fn.initS`) meets its contract in
constant time and returns without secret residue. -/
theorem initS_scrubbed :
    VerifiedScrubbed target Impl.Blake2.RISCV64.Fn.initS (Spec.Blake2.initSContract RISCV64.abi) 0 :=
  verifiedScrubbed (api := Spec.Blake2.initSApi) (W := 0)
    { code := Impl.Blake2.RISCV64.Stream.init Spec.Blake2.s, verified := Proof.Blake2.RISCV64.Stream.initS_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.initSPost_out 64))
    (show scrubSide (Impl.Blake2.RISCV64.Stream.init Spec.Blake2.s) 0 0 [] = true by lit_decide)

/-- `vg_blake2s_update` as emitted (`Impl.Blake2.RISCV64.Fn.updateS`) meets its contract in
constant time and returns without secret residue. -/
theorem updateS_scrubbed :
    VerifiedScrubbed target Impl.Blake2.RISCV64.Fn.updateS (Spec.Blake2.updateSContract RISCV64.abi 336) 0 :=
  verifiedScrubbed (api := Spec.Blake2.updateSApi) (W := 336)
    { code := Impl.Blake2.RISCV64.Stream.update Spec.Blake2.s, verified := Proof.Blake2.RISCV64.Stream.updateS_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateSPost_out 64))
    (show scrubSide (Impl.Blake2.RISCV64.Stream.update Spec.Blake2.s) 336 0 [] = true by lit_decide)

/-- `vg_blake2s_finalize` as emitted (`Impl.Blake2.RISCV64.Fn.finalizeS`) meets its contract in
constant time and returns without secret residue. -/
theorem finalizeS_scrubbed :
    VerifiedScrubbed target Impl.Blake2.RISCV64.Fn.finalizeS (Spec.Blake2.finalizeSContract RISCV64.abi 336) 0 :=
  verifiedScrubbed (api := Spec.Blake2.finalizeSApi) (W := 336)
    { code := Impl.Blake2.RISCV64.Stream.finalize Spec.Blake2.s, verified := Proof.Blake2.RISCV64.Stream.finalizeS_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeSPost_out 64))
    (show scrubSide (Impl.Blake2.RISCV64.Stream.finalize Spec.Blake2.s) 336 0 [] = true by lit_decide)

end VG.Proof.Blake2.RISCV64
