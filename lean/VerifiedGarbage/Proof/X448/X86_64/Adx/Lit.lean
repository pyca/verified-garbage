import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.X448.X86_64.Adx
import VerifiedGarbage.Proof.X448.X86_64.Lit

/-!
# X448 on x86-64 with BMI2 and ADX: the code as a literal

The field operations are templates (`materialize_template`): the
multiplications here, and the additions, subtractions and swaps the
baseline's literal shares (`Proof/X448/X86_64/Lit.lean`).
-/

namespace VG.Proof.X448.X86_64.Adx.Lit
open VG.Impl.X448.X86_64

materialize_template mulXT := mulX
materialize_template sqrXT := sqrX
materialize_template a24XT := Field.a24 adx

end VG.Proof.X448.X86_64.Adx.Lit

namespace VG

materialize_code Impl.X448.X86_64.x448Adx

end VG
