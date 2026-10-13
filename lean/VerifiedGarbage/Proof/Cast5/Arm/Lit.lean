module

public import VerifiedGarbage.Impl.Cast5.Arm
meta import VerifiedGarbage.Impl.Cast5.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Literal code for the kernel-evaluated checks (constant time, `spSafe`). -/

@[expose] public section

namespace VG.Impl.Cast5.Arm
materialize_code ecbEncrypt
materialize_code ecbDecrypt
materialize_code expandKey
end VG.Impl.Cast5.Arm
