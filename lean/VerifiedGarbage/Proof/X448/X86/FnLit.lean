import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.X448.X86

/-!
# Curve448's field functions on x86 (32-bit): the code as literals

Untrusted: everything here is checked by Lean. The rows of the product are
unrolled: the literals spare the kernel building the instructions again in
every check that evaluates the code (constant time, the stack pointer,
`spSafe`).
-/

namespace VG.Impl.X448.X86

materialize_code mulFn
materialize_code addFn
materialize_code subFn
materialize_code mulA24Fn

end VG.Impl.X448.X86
