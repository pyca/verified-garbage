module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha256.RISCV64.Shared
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Proof.Sha256.PostOut

/-!
# SHA-224 and SHA-256 on RISC-V, without secret residue

Each of the streaming and one-shot functions, followed by
`Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.withScrub`), which clears the
caller-saved registers and the stack its frames used. Their postconditions
read the memory on return only within their buffers
(`Proof/Sha256/PostOut.lean`). HMAC, PBKDF2, DSA and RSA call their code
itself, not these functions.
-/

@[expose] public section

namespace VG.Proof.Sha256.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub

/-- `vg_sha256_init`. -/
def initReg : Registration Spec.Sha256.initApi RISCV64.target :=
  withScrub { code := Impl.Sha256.RISCV64.Stream.init, verified := Shared.init }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.initPost_out Spec.Sha256.H0 64))

/-- `vg_sha224_init`. -/
def init224Reg : Registration Spec.Sha256.init224Api RISCV64.target :=
  withScrub { code := Impl.Sha256.RISCV64.Stream.init224, verified := Shared.init224 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.initPost_out Spec.Sha256.H0_224 64))

/-- `vg_sha256_update`, which SHA-224 shares. -/
def updateReg : Registration Spec.Sha256.updateApi RISCV64.target :=
  withScrub { code := Impl.Sha256.RISCV64.Stream.update, verified := Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.updatePost_out 64))

/-- `vg_sha256_finalize`. -/
def finalizeReg : Registration Spec.Sha256.finalizeApi RISCV64.target :=
  withScrub { code := Impl.Sha256.RISCV64.Stream.finalize, verified := Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalizePost_out 64))

/-- `vg_sha224_finalize`. -/
def finalize224Reg : Registration Spec.Sha256.finalize224Api RISCV64.target :=
  withScrub { code := Impl.Sha256.RISCV64.Stream.finalize224, verified := Shared.finalize224 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalize224Post_out 64))

/-- `vg_sha256_digest`. -/
def digest256Reg : Registration Spec.Sha256.digest256Api RISCV64.target :=
  withScrub {
      code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha256Family.hash256
      verified := Proof.Hmac.Stream.RISCV64.Sha256.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash 64 (by decide)))

/-- `vg_sha224_digest`. -/
def digest224Reg : Registration Spec.Sha256.digest224Api RISCV64.target :=
  withScrub {
      code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha256Family.hash224
      verified := Proof.Hmac.Stream.RISCV64.Sha224.digest }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 64 (by decide)))

end VG.Proof.Sha256.RISCV64
