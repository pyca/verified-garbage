module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm3.RISCV64.Shared
public import VerifiedGarbage.Proof.Sm3.PostOut

/-!
# SM3 on RISC-V, without secret residue

Each of the streaming functions, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`Proof/Sm3/PostOut.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm3.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub

/-- `vg_sm3_init`. -/
def initReg : Registration Spec.Sm3.initApi RISCV64.target :=
  withScrub { code := Impl.Sm3.RISCV64.Stream.init, verified := Shared.init }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.initPost_out 64))

/-- `vg_sm3_update`. -/
def updateReg : Registration Spec.Sm3.updateApi RISCV64.target :=
  withScrub { code := Impl.Sm3.RISCV64.Stream.update, verified := Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.updatePost_out 64))

/-- `vg_sm3_finalize`. -/
def finalizeReg : Registration Spec.Sm3.finalizeApi RISCV64.target :=
  withScrub { code := Impl.Sm3.RISCV64.Stream.finalize, verified := Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.finalizePost_out 64))


end VG.Proof.Sm3.RISCV64
