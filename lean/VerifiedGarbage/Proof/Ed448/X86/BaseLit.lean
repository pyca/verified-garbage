import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed448.X86.ScalarBase

/-!
# Ed448 base-point multiplication on x86 (32-bit): the code as a literal

The field arithmetic is fully unrolled: the literal of the code
(`materialize_code`, `Proof/Framework/Lit.lean`) spares the kernel building
the instructions again in every check that evaluates the code (constant time,
`spSafe`).
-/

namespace VG

materialize_code Impl.Ed448.X86.scalarBase

end VG
