module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Md5.PostOut
public import VerifiedGarbage.Proof.Md5.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Md5.RISCV64.Compress
public import VerifiedGarbage.Proof.Md5.RISCV64.Stream
public import VerifiedGarbage.Spec.Md5.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-! ### `Md5.RISCV64.Shared`, which only this module used -/

section

/-!
# MD5 on RISC-V: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written
against per-target contracts (`Proof/Md5/RISCV64/Contract.lean`); these
theorems move them to the shared contracts of `Spec/Md5/Contract.lean`,
which the artifacts are emitted with. `update` and `finalize` keep their
working space in a frame of their own, of 144 bytes
(`Impl.MdStream.RISCV64.frameBytes`), the `stack` of their contracts.
-/

@[expose] public section

namespace VG.Proof.Md5.RISCV64.Shared

theorem init :
    Verified RISCV64.target Impl.Md5.RISCV64.Stream.init (Spec.Md5.initContract RISCV64.abi) :=
  Proof.Md5.RISCV64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Md5.initContract, Spec.Md5.initSig, Proof.Md5.initRISCV64,
      RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.initSat] using MdStream.RISCV64.initSat 80)

theorem update :
    Verified RISCV64.target Impl.Md5.RISCV64.Stream.update (Spec.Md5.updateContract RISCV64.abi 144) :=
  Proof.Md5.RISCV64.Stream.update_verified.of_implies (by
    contract_implies [Spec.Md5.updateContract, Spec.Md5.updateSig, Spec.Md5.updatePost,
      Proof.Md5.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.Update.sat] using MdStream.RISCV64.Update.sat 16)

theorem finalize :
    Verified RISCV64.target Impl.Md5.RISCV64.Stream.finalize (Spec.Md5.finalizeContract RISCV64.abi 144) :=
  Proof.Md5.RISCV64.Stream.finalize_verified.of_implies (by
    contract_implies [Spec.Md5.finalizeContract, Spec.Md5.finalizeSig, Spec.Md5.finalizePost,
      Proof.Md5.finalizeRISCV64, RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.Finalize.sat] using MdStream.RISCV64.Finalize.sat 16 16)

end VG.Proof.Md5.RISCV64.Shared

end

end

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
