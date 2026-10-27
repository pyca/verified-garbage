module

public import VerifiedGarbage.Impl.Seed.RISCV64.ExpandKey
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Seed.RISCV64.ExpandKey
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# SEED on RISC-V, as literals

The code of the ECB functions and the key expansion, built by functions, as
literals (`materialize_code`): the checks that evaluate it (`lit_decide`,
`taint_decide`) read the literal instead of building the code again.
-/

@[expose] public section

namespace VG.Impl.Seed.RISCV64

materialize_value g16
materialize_code encrypt
materialize_code decrypt
materialize_code expandKey

end VG.Impl.Seed.RISCV64
