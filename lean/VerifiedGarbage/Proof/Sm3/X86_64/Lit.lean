import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Sm3.X86_64

/-!
# SM3 on x86-64: the code as literals
-/

namespace VG

materialize_code Impl.Sm3.X86_64.compress

end VG
