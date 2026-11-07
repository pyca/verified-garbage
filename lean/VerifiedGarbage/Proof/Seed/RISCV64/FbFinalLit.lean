module

public import VerifiedGarbage.Impl.Seed.RISCV64.FbFinal
import VerifiedGarbage.Proof.Seed.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Seed.RISCV64.FbFinal
meta import VerifiedGarbage.Proof.Seed.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # Seed's final CFB functions on RISC-V, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Seed.RISCV64.cfbEncryptFinal
materialize_code Impl.Seed.RISCV64.cfbDecryptFinal

end VG
