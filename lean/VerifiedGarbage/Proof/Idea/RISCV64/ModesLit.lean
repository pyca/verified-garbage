module

public import VerifiedGarbage.Impl.Idea.RISCV64.Modes
import VerifiedGarbage.Proof.Idea.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Idea.RISCV64.Modes
meta import VerifiedGarbage.Proof.Idea.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # IDEA's modes on RISC-V, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.RISCV64.cbcEncryptChained
materialize_code Impl.Idea.RISCV64.cbcDecryptChained
materialize_code Impl.Idea.RISCV64.ofb
materialize_code Impl.Idea.RISCV64.cfbEncrypt
materialize_code Impl.Idea.RISCV64.cfbDecrypt

end VG

