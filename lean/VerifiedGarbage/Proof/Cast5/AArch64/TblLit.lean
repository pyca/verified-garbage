module

public import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Literal code for the kernel-evaluated checks (constant time, `spSafe`, the ABI) of the code
that reads the S-boxes by `tbl`. -/

@[expose] public section

namespace VG

/-! The table every load carries, evaluated once. -/

materialize_value Impl.Cast5.AArch64.Tbl.planeWords

/-! The functions. -/

materialize_code Impl.Cast5.AArch64.Tbl.ecbEncrypt
materialize_code Impl.Cast5.AArch64.Tbl.ecbDecrypt

end VG
