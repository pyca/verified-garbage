module

public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.Proof.Sha3.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# The SHA-3 sponge on RISC-V: the code as literals

The streaming functions' code as literals (`materialize_code`), which
contain the permutation's (`Proof/Sha3/RISCV64/Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream

materialize_code absorb := Impl.Sha3.RISCV64.Stream.absorb
materialize_code pad := Impl.Sha3.RISCV64.Stream.pad
materialize_code squeeze := Impl.Sha3.RISCV64.Stream.squeeze

end VG.Proof.Sha3.RISCV64.Stream
