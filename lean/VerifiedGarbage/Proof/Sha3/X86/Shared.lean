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

theorem permute :
    Verified X86.target Impl.Sha3.X86.permute (Proof.Sha3.permuteContract X86.abi) :=
  Proof.Sha3.X86.permute_verified.of_implies (by
    contract_implies [Proof.Sha3.permuteContract, Proof.Sha3.permuteSig, Proof.Sha3.permuteX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha3.X86.satState, Proof.Sha3.X86.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
      using Proof.Sha3.X86.satState)

theorem absorb :
    Verified X86.target Impl.Sha3.X86.Stream.absorb (Spec.Sha3.absorbScratchContract X86.abi 12) :=
  Proof.Sha3.X86.Stream.Absorb.absorb_verified.of_implies (by
    contract_implies [Spec.Sha3.absorbScratchContract, Spec.Sha3.absorbScratchSig, Spec.Sha3.absorbPre, Spec.Sha3.absorbPost, Proof.Sha3.absorbX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, setWidth_append32]
      [Proof.Sha3.X86.Stream.Absorb.sat, Proof.Sha3.X86.Stream.Absorb.satMem, X86.arg, X86.argAddr,
      Mem.readW, Mem.read] using Proof.Sha3.X86.Stream.Absorb.sat)

theorem pad :
    Verified X86.target Impl.Sha3.X86.Stream.pad (Proof.Sha3.padScratchContract X86.abi 12) :=
  Proof.Sha3.X86.Stream.Pad.pad_verified.of_implies (by
    contract_implies [Proof.Sha3.padScratchContract, Proof.Sha3.padScratchSig, Spec.Sha3.padPre, Spec.Sha3.padPost, Proof.Sha3.padX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha3.X86.Stream.Pad.sat, Proof.Sha3.X86.Stream.Pad.satMem, X86.arg, X86.argAddr,
      Mem.readW, Mem.read] using Proof.Sha3.X86.Stream.Pad.sat)

theorem squeeze :
    Verified X86.target Impl.Sha3.X86.Stream.squeeze (Proof.Sha3.squeezeScratchContract X86.abi 12) :=
  Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.of_implies (by
    contract_implies [Proof.Sha3.squeezeScratchContract, Proof.Sha3.squeezeScratchSig, Spec.Sha3.squeezePre, Spec.Sha3.squeezePost, Proof.Sha3.squeezeX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, setWidth_append32]
      [Proof.Sha3.X86.Stream.Squeeze.sat, Proof.Sha3.X86.Stream.Squeeze.satMem, X86.arg, X86.argAddr,
      Mem.readW, Mem.read] using Proof.Sha3.X86.Stream.Squeeze.sat)

end VG.Proof.Sha3.X86.Shared
