module

public import VerifiedGarbage.Proof.Rc2.AArch64.Lit
meta import VerifiedGarbage.Proof.Rc2.AArch64.Lit
public import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
meta import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! # Literal CBC callers -/

@[expose] public section

namespace VG

materialize_flat_code Impl.Rc2.AArch64.Cbc.encrypt
materialize_flat_code Impl.Rc2.AArch64.Cbc.decrypt

end VG
