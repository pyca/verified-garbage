import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation

/-!
# Ed448 verification's equation on AArch64: the code as a literal

The kernel checks the literal once; the taint and instruction checks reuse it.
-/

namespace VG

materialize_code Impl.Ed448.AArch64.verifyEquation

end VG
