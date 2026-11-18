module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm3.PostOut
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Sm3.RISCV64.Compress
public import VerifiedGarbage.Proof.Sm3.RISCV64.Stream
public import VerifiedGarbage.Spec.Sm3.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-! ### `Sm3.RISCV64.Shared`, which only this module used -/

section

/-!
# SM3 on RISC-V: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written
against per-target contracts (`Proof/Sm3/RISCV64/Contract.lean`); these
theorems move them to the shared contracts of `Spec/Sm3/Contract.lean`,
which the artifacts are emitted with. `update` and `finalize` keep their
working space in a frame of their own, of 144 bytes
(`Impl.MdStream.RISCV64.frameBytes`), the `stack` of their contracts.
-/

@[expose] public section

namespace VG.Proof.Sm3.RISCV64.Shared

open _root_.VG.RISCV64

theorem init :
    Verified RISCV64.target Impl.Sm3.RISCV64.Stream.init (Spec.Sm3.initContract RISCV64.abi) :=
  Proof.Sm3.RISCV64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initRISCV64,
      RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.initSat] using MdStream.RISCV64.initSat 96)

theorem update :
    Verified RISCV64.target Impl.Sm3.RISCV64.Stream.update (Spec.Sm3.updateContract RISCV64.abi 144) :=
  Proof.Sm3.RISCV64.Stream.update_verified.of_implies (by
    contract_implies [Spec.Sm3.updateContract, Spec.Sm3.updateSig, Spec.Sm3.updatePost,
      Proof.Sm3.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.Update.sat] using MdStream.RISCV64.Update.sat 32)

theorem finalize :
    Verified RISCV64.target Impl.Sm3.RISCV64.Stream.finalize (Spec.Sm3.finalizeContract RISCV64.abi 144) :=
  Proof.Sm3.RISCV64.Stream.finalize_verified.of_implies (by
    contract_implies [Spec.Sm3.finalizeContract, Spec.Sm3.finalizeSig, Spec.Sm3.finalizePost,
      Proof.Sm3.finalizeRISCV64, RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.Finalize.sat] using MdStream.RISCV64.Finalize.sat 32 32)

end VG.Proof.Sm3.RISCV64.Shared

end

end

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
