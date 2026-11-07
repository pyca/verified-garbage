module

public import VerifiedGarbage.Proof.Sha3.Contract
import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86.Stream.Squeeze
public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.Impl.Sha3.X86.Stream
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SHA-3 on x86 (32-bit): the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha3/X86/Permute.lean`); these theorems move them to the shared
contracts of `Spec/Sha3/Contract.lean`, which the artifacts are emitted with.
The streaming functions call the permutation, using the 12 bytes below the
return address; the permutation uses no stack.
-/

@[expose] public section

namespace VG.Proof.Sha3.X86.Shared

/-- The returned `usize` is the low word, `eax`, of the returned pair. -/
theorem setWidth_append32 (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt b.isLt]
  omega

end VG.Proof.Sha3.X86.Shared
