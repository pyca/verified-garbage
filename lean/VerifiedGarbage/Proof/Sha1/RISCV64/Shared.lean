module

public import VerifiedGarbage.Proof.Sha1.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Sha1.RISCV64.Compress
public import VerifiedGarbage.Proof.Sha1.RISCV64.Stream
public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

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
