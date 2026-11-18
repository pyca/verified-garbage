module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
public import VerifiedGarbage.Proof.Sha1.PostOut
public import VerifiedGarbage.Proof.Sha1.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Sha1.RISCV64.Compress
public import VerifiedGarbage.Proof.Sha1.RISCV64.Stream
public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-! ### `Sha1.RISCV64.Shared`, which only this module used -/

section

/-!
# SHA-1 on RISC-V: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written
against per-target contracts (`Proof/Sha1/RISCV64/Contract.lean`); these
theorems move them to the shared contracts of `Spec/Sha1/Contract.lean`,
which the artifacts are emitted with. `update` and `finalize` keep their
working space in a frame of their own, of 144 bytes
(`Impl.MdStream.RISCV64.frameBytes`), the `stack` of their contracts.
-/

@[expose] public section

namespace VG.Proof.Sha1.RISCV64.Shared

open _root_.VG.RISCV64

theorem init :
    Verified RISCV64.target Impl.Sha1.RISCV64.Stream.init (Spec.Sha1.initContract RISCV64.abi) :=
  Proof.Sha1.RISCV64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha1.initContract, Spec.Sha1.initSig, Proof.Sha1.initRISCV64,
      RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.initSat] using MdStream.RISCV64.initSat 84)

theorem update :
    Verified RISCV64.target Impl.Sha1.RISCV64.Stream.update (Spec.Sha1.updateContract RISCV64.abi 144) :=
  Proof.Sha1.RISCV64.Stream.update_verified.of_implies (by
    contract_implies [Spec.Sha1.updateContract, Spec.Sha1.updateSig, Spec.Sha1.updatePost,
      Proof.Sha1.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.Update.sat] using MdStream.RISCV64.Update.sat 20)

theorem finalize :
    Verified RISCV64.target Impl.Sha1.RISCV64.Stream.finalize (Spec.Sha1.finalizeContract RISCV64.abi 144) :=
  Proof.Sha1.RISCV64.Stream.finalize_verified.of_implies (by
    contract_implies [Spec.Sha1.finalizeContract, Spec.Sha1.finalizeSig, Spec.Sha1.finalizePost,
      Proof.Sha1.finalizeRISCV64, RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.Finalize.sat] using MdStream.RISCV64.Finalize.sat 20 20)

end VG.Proof.Sha1.RISCV64.Shared

end

end

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
