module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Verified
public import VerifiedGarbage.Proof.Blake2.Scratch
public import VerifiedGarbage.Proof.Blake2.PostOut
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit

/-!
# BLAKE2b and BLAKE2s on RISC-V, without secret residue

Each of the streaming functions, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.scrubOf`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`Proof/Blake2/PostOut.lean`, `Proof/Blake2/Scratch.lean`).
Argon2 calls `vg_blake2b_init`'s code as the internal `vg_blake2b_init_core`
(`Impl.Argon2.RISCV64.HPrime.initName`), and BLAKE2's update and finalize
as their own internal `_scratch` functions.
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub

/-- `vg_blake2b_init`. -/
def initBReg : Registration Spec.Blake2.initBApi RISCV64.target :=
  scrubOf { code := Impl.Blake2.RISCV64.Stream.init Spec.Blake2.b, verified := Proof.Blake2.RISCV64.Stream.initB_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.initBPost_out 64))

/-- `vg_blake2b_update`. -/
def updateBReg : Registration Spec.Blake2.updateBApi RISCV64.target :=
  scrubOf { code := Impl.Blake2.RISCV64.Stream.update Spec.Blake2.b, verified := Proof.Blake2.RISCV64.Stream.updateB_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateBPost_out 64))

/-- `vg_blake2b_finalize`. -/
def finalizeBReg : Registration Spec.Blake2.finalizeBApi RISCV64.target :=
  scrubOf { code := Impl.Blake2.RISCV64.Stream.finalize Spec.Blake2.b, verified := Proof.Blake2.RISCV64.Stream.finalizeB_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeBPost_out 64))

/-- `vg_blake2s_init`. -/
def initSReg : Registration Spec.Blake2.initSApi RISCV64.target :=
  scrubOf { code := Impl.Blake2.RISCV64.Stream.init Spec.Blake2.s, verified := Proof.Blake2.RISCV64.Stream.initS_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.initSPost_out 64))

/-- `vg_blake2s_update`. -/
def updateSReg : Registration Spec.Blake2.updateSApi RISCV64.target :=
  scrubOf { code := Impl.Blake2.RISCV64.Stream.update Spec.Blake2.s, verified := Proof.Blake2.RISCV64.Stream.updateS_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.updateSPost_out 64))

/-- `vg_blake2s_finalize`. -/
def finalizeSReg : Registration Spec.Blake2.finalizeSApi RISCV64.target :=
  scrubOf { code := Impl.Blake2.RISCV64.Stream.finalize Spec.Blake2.s, verified := Proof.Blake2.RISCV64.Stream.finalizeS_verified }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Blake2.finalizeSPost_out 64))

end VG.Proof.Blake2.RISCV64
