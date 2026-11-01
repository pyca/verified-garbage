module

public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Block
public import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.Proof.ChaCha20.Contract
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.ChaCha20.PPC64LE
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# ChaCha20 on PPC64LE: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/ChaCha20/PPC64LE/Contract.lean`); these theorems move
them to the shared contracts of `Spec/ChaCha20/Contract.lean`, which the
artifacts are emitted with.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.PPC64LE.Shared

theorem block :
    Verified PPC64LE.target Impl.ChaCha20.PPC64LE.block (Proof.ChaCha20.blockContract PPC64LE.abi) :=
  Proof.ChaCha20.PPC64LE.block_verified.of_implies (by
    contract_implies [Proof.ChaCha20.blockContract, Proof.ChaCha20.blockSig,
      Proof.ChaCha20.blockPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.ChaCha20.PPC64LE.satState] using Proof.ChaCha20.PPC64LE.satState)

end VG.Proof.ChaCha20.PPC64LE.Shared
