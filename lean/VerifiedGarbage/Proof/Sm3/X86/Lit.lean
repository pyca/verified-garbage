import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Sm3.X86.Stream

/-!
# SM3 on x86: the code as literals
-/

namespace VG

materialize_code Impl.Sm3.X86.compress
materialize_code Impl.Sm3.X86.Stream.update
materialize_code Impl.Sm3.X86.Stream.finalize

end VG
