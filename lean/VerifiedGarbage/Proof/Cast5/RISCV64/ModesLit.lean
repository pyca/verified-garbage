module

public import VerifiedGarbage.Impl.Cast5.RISCV64.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.RISCV64.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # CAST5's modes on RISC-V, evaluated once -/

@[expose] public section

namespace VG.Impl.Cast5.RISCV64
materialize_code cbcEncryptChained
materialize_code cbcDecryptChained
materialize_code ofb
materialize_code cfbEncrypt
materialize_code cfbDecrypt
end VG.Impl.Cast5.RISCV64
