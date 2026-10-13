module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Sha1.X86.ShaNi
meta import VerifiedGarbage.Impl.Sha1.X86.ShaNi
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SHA-1 on x86 with the SHA extensions: the compression function as a literal
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha1.X86.ShaNi.compress

end VG
