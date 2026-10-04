import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Sha1.X86.ShaNi

/-!
# SHA-1 on x86 with the SHA extensions: the compression function as a literal
-/

namespace VG

materialize_code Impl.Sha1.X86.ShaNi.compress

end VG
