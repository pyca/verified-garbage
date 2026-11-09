module

public import VerifiedGarbage.Impl.Sm4.RISCV64.FbFinal
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.RISCV64.FbFinal
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # Sm4's final CFB and OFB functions on RISC-V, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Sm4.RISCV64.cfbEncryptFinal
materialize_code Impl.Sm4.RISCV64.cfbDecryptFinal
materialize_code Impl.Sm4.RISCV64.ofbFinal

end VG
