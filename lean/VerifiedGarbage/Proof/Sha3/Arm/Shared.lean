module

public import VerifiedGarbage.Proof.Sha3.Contract
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.Impl.Sha3.Arm.Stream
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# SHA-3 on ARMv7: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha3/Arm/Permute.lean`); these theorems move them to the shared
contracts of `Spec/Sha3/Contract.lean`, which the artifacts are emitted with.
The functions use no stack: `bl` leaves the return address in `lr`, which each
streaming function saves in its scratch space.
-/

@[expose] public section

namespace VG.Proof.Sha3.Arm.Shared

/-- The returned `usize` is the low word, `r0`, of the returned pair. -/
theorem setWidth_append32 (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt b.isLt]
  omega

end VG.Proof.Sha3.Arm.Shared
