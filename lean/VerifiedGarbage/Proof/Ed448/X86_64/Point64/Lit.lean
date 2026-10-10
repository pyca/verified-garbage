import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Impl.Ed448.X86_64.Point64

/-! The point functions' code as literals (`materialize_code`), which their checks, and those
of the code that calls them, read rather than build each field multiplication again. -/

namespace VG

materialize_code Impl.Ed448.X86_64.Point64.doubleFn
materialize_code Impl.Ed448.X86_64.Point64.addFn

end VG
