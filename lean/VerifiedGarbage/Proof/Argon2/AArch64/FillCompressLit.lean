module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Argon2.AArch64.FillCompress
meta import VerifiedGarbage.Impl.Argon2.AArch64.FillCompress
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Checked literals for compression and the enclosing argument setup. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.AArch64.FillCompress.operation
materialize_code Impl.Argon2.AArch64.FillCompress.code

end VG
