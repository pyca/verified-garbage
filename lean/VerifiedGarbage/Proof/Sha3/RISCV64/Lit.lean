module

public import VerifiedGarbage.Impl.Sha3.RISCV64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha3.RISCV64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# Keccak-f[1600] on RISC-V: the code as a literal

The permutation's code as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`): its prologue builds the round constants, which
the kernel would otherwise compute in every check that evaluates the code.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64

materialize_code permute := Impl.Sha3.RISCV64.permute

end VG.Proof.Sha3.RISCV64
