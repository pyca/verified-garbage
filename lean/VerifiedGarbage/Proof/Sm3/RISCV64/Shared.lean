module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Sm3.RISCV64.Compress
public import VerifiedGarbage.Proof.Sm3.RISCV64.Stream
public import VerifiedGarbage.Spec.Sm3.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

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
