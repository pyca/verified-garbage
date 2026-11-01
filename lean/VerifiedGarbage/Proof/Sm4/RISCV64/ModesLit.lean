module

public import VerifiedGarbage.Impl.Sm4.RISCV64.Modes
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.RISCV64.Modes
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # SM4's modes on RISC-V, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Sm4.RISCV64.cbcEncryptChained
materialize_code Impl.Sm4.RISCV64.cbcDecryptChained
materialize_code Impl.Sm4.RISCV64.ofb
materialize_code Impl.Sm4.RISCV64.cfbEncrypt
materialize_code Impl.Sm4.RISCV64.cfbDecrypt
materialize_code Impl.Sm4.RISCV64.ctr
materialize_code Impl.Sm4.RISCV64.ctr32

end VG
