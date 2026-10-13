module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Sm3.X86_64
meta import VerifiedGarbage.Impl.Sm3.X86_64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SM3 on x86-64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sm3.X86_64.compress

end VG
