module

public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
public import VerifiedGarbage.Proof.Sha3.X2Contract
public import VerifiedGarbage.TCB.AArch64.Target

/-!
# Implementations of Keccak-f[1600] on two interleaved states, for their callers

The interface `KeccakX2` on AArch64 (`Variants/KeccakX2/AArch64/`): an
implementation of `vg_keccak_f1600_x2` (`Impl.Sha3.AArch64.Neon.X2.code sha3`,
with the SHA-3 extension or without), which a generic caller (e.g. ML-KEM's,
`Generic/KeccakX2/Keccak/AArch64/MlKem.lean`) calls under the name of its
suffix, with the CPU features it needs and its proof.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64

/-- An implementation of Keccak-f[1600] on two interleaved states. -/
structure X2Permutation where
  /-- Whether it uses the SHA-3 extension. -/
  sha3 : Bool
  suffix : String
  features : List String
  code : Prog isa
  /-- The code callers call: `Impl.Sha3.AArch64.Neon.X2.call sha3`'s. -/
  code_eq : code = Impl.Sha3.AArch64.Neon.X2.code sha3
  verified : Verified AArch64.target code (Proof.Sha3.permuteX2Contract AArch64.abi)

end VG.Proof.Sha3.AArch64
