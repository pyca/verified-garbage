module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Sha512.X86_64.ShaNi
meta import VerifiedGarbage.Impl.Sha512.X86_64.ShaNi
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SHA-512 with the SHA512 extension on x86-64: the code as a literal

The compression function as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha512.X86_64.ShaNi.compress

end VG
