module

public import VerifiedGarbage.Proof.Md5.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Md5.RISCV64.Compress
public import VerifiedGarbage.Proof.Md5.RISCV64.Stream
public import VerifiedGarbage.Spec.Md5.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

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

theorem compress :
    Verified RISCV64.target Impl.Md5.RISCV64.compress (Proof.Md5.compressContract RISCV64.abi) :=
  Proof.Md5.RISCV64.compress_verified.of_implies (by
    contract_implies [Proof.Md5.compressContract, Proof.Md5.compressSig, Proof.Md5.compressRISCV64,
      RISCV64.abi, RISCV64.argRegs]
      [Proof.Md5.RISCV64.satState] using Proof.Md5.RISCV64.satState)

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
