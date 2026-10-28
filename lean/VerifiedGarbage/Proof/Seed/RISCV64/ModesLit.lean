module

public import VerifiedGarbage.Impl.Seed.RISCV64.Modes
import VerifiedGarbage.Proof.Seed.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Seed.RISCV64.Modes
meta import VerifiedGarbage.Proof.Seed.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # SEED's modes on RISC-V, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Seed.RISCV64.cbcEncryptChained
materialize_code Impl.Seed.RISCV64.cbcDecryptChained
materialize_code Impl.Seed.RISCV64.ofb
materialize_code Impl.Seed.RISCV64.cfbEncrypt
materialize_code Impl.Seed.RISCV64.cfbDecrypt

end VG
