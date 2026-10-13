module

public import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Lit
public import VerifiedGarbage.Impl.Ed448.X86_64.Point64
meta import VerifiedGarbage.Impl.Ed448.X86_64.Point64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! The point functions' code as literals (`materialize_code`), which their checks, and those
of the code that calls them, read rather than build each field multiplication again. -/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.X86_64.Point64.doubleFn
materialize_code Impl.Ed448.X86_64.Point64.addFn

end VG
