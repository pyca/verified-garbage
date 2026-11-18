module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha1.RISCV64.Shared
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
public import VerifiedGarbage.Proof.Sha1.PostOut

/-!
# SHA-1 on RISC-V, without secret residue

Each of the streaming functions, followed by `Impl.Scrub.RISCV64.scrubTail`
(`RISCV64.Scrub.withScrub`), which clears the caller-saved registers and the
stack its frames used. Their postconditions read the memory on return only
within their buffers (`Proof/Sha1/PostOut.lean`). HMAC-SHA-1,
PBKDF2 and the digest call their code as the internal `vg_sha1_init_core`,
… (an `_core` suffix to each name), not these functions.
-/

@[expose] public section

namespace VG.Proof.Sha1.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub

/-- `vg_sha1_init`. -/
def initReg : Registration Spec.Sha1.initApi RISCV64.target :=
  withScrub { code := Impl.Sha1.RISCV64.Stream.init, verified := Shared.init }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.initPost_out 64))

/-- `vg_sha1_update`. -/
def updateReg : Registration Spec.Sha1.updateApi RISCV64.target :=
  withScrub { code := Impl.Sha1.RISCV64.Stream.update, verified := Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.updatePost_out 64))

/-- `vg_sha1_finalize`. -/
def finalizeReg : Registration Spec.Sha1.finalizeApi RISCV64.target :=
  withScrub { code := Impl.Sha1.RISCV64.Stream.finalize, verified := Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.finalizePost_out 64))

/-- `vg_sha1_digest`. -/
def digestReg : Registration Spec.Sha1.digestApi RISCV64.target :=
  withScrub { code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha1.hash, verified := Proof.Hmac.Stream.RISCV64.Sha1.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.digestPost_out 64))


end VG.Proof.Sha1.RISCV64
