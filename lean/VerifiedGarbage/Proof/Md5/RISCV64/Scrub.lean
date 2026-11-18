module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Md5.RISCV64.Shared
public import VerifiedGarbage.Proof.Md5.PostOut

/-!
# MD5 on RISC-V, without secret residue

Each of the streaming functions, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`Proof/Md5/PostOut.lean`). HMAC-MD5 and
PBKDF2 call their code as the internal `vg_md5_init_core`, … (an `_core`
suffix to each name), not these functions.
-/

@[expose] public section

namespace VG.Proof.Md5.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub

/-- `vg_md5_init`. -/
def initReg : Registration Spec.Md5.initApi RISCV64.target :=
  withScrub { code := Impl.Md5.RISCV64.Stream.init, verified := Shared.init }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.initPost_out 64))

/-- `vg_md5_update`. -/
def updateReg : Registration Spec.Md5.updateApi RISCV64.target :=
  withScrub { code := Impl.Md5.RISCV64.Stream.update, verified := Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.updatePost_out 64))

/-- `vg_md5_finalize`. -/
def finalizeReg : Registration Spec.Md5.finalizeApi RISCV64.target :=
  withScrub { code := Impl.Md5.RISCV64.Stream.finalize, verified := Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Md5.finalizePost_out 64))


end VG.Proof.Md5.RISCV64
