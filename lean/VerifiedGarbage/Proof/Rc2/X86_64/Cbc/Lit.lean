module

public import VerifiedGarbage.Proof.Rc2.X86_64.Lit
meta import VerifiedGarbage.Proof.Rc2.X86_64.Lit
public import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
meta import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Literal CBC callers -/

@[expose] public section

namespace VG

materialize_code Impl.Rc2.X86_64.Cbc.encrypt
materialize_code Impl.Rc2.X86_64.Cbc.decrypt

end VG
