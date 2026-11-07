module

public import VerifiedGarbage.Impl.Cast5.RISCV64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.RISCV64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # CAST5's final CFB functions on RISC-V, evaluated once -/

@[expose] public section

namespace VG.Impl.Cast5.RISCV64

materialize_code cfbEncryptFinal
materialize_code cfbDecryptFinal

end VG.Impl.Cast5.RISCV64
