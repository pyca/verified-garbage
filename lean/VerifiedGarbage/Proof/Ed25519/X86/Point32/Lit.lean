import VerifiedGarbage.Proof.X25519.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.Point32

/-! The point functions' code as literals (`materialize_code`), which
its checks, and those of the code that calls it, read rather than build each
field multiplication again. -/

namespace VG.Impl.Ed25519.X86.Point32

materialize_code addFn
materialize_code affFn
materialize_code doubleFn

end VG.Impl.Ed25519.X86.Point32
