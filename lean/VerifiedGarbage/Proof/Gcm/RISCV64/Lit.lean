module

public import VerifiedGarbage.Impl.Gcm.RISCV64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Gcm.RISCV64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # GHASH on RISC-V: the code as a literal, for the checks that evaluate it -/

@[expose] public section

namespace VG.Impl.Gcm.RISCV64
materialize_code ghash
end VG.Impl.Gcm.RISCV64
