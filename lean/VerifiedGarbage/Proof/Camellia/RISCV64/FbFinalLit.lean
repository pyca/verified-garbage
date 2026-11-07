module

public import VerifiedGarbage.Impl.Camellia.RISCV64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
meta import VerifiedGarbage.Impl.Camellia.RISCV64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

/-! # Camellia's final CFB and OFB functions on RISC-V, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Camellia.RISCV64.cfbEncryptFinal
materialize_code Impl.Camellia.RISCV64.cfbDecryptFinal
materialize_code Impl.Camellia.RISCV64.ofbFinal

end VG
