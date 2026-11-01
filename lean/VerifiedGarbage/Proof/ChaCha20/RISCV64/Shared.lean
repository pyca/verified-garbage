module

public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.ChaCha20.RISCV64.Block
public import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.Proof.ChaCha20.Contract
public import VerifiedGarbage.Impl.ChaCha20.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# ChaCha20 on RISC-V: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/ChaCha20/RISCV64/Contract.lean`); these theorems
move them to the shared contracts of `Spec/ChaCha20/Contract.lean`, which the
artifacts are emitted with.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.RISCV64.Shared

theorem block :
    Verified RISCV64.target Impl.ChaCha20.RISCV64.block (Proof.ChaCha20.blockContract RISCV64.abi) :=
  Proof.ChaCha20.RISCV64.block_verified.of_implies (by
    contract_implies [Proof.ChaCha20.blockContract, Proof.ChaCha20.blockSig,
      Proof.ChaCha20.blockRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.ChaCha20.RISCV64.satState] using Proof.ChaCha20.RISCV64.satState)

end VG.Proof.ChaCha20.RISCV64.Shared
