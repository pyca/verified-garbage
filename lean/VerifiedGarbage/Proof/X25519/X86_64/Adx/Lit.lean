import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.X25519.X86_64.Lit

/-!
# X25519 on x86-64 with BMI2 and ADX: the code as a literal

As for `vg_x25519` (`Proof/X25519/X86_64/Lit.lean`): the literal of the
unrolled code, checked once here, for the checks that evaluate it.
-/

namespace VG.Proof.X25519.X86_64.Adx.Lit
open VG.Impl.X25519.X86_64

/-! The multiplications with BMI2 and ADX are templates (`materialize_template`),
beside the baseline's additions, subtractions and swaps
(`Proof/X25519/X86_64/Lit.lean`). -/

materialize_template mulXT := mulX
materialize_template sqrXT := sqrX
materialize_template a24XT := a24X
materialize_template mul2XT := mul2X
materialize_template sqr2XT := sqr2X

end VG.Proof.X25519.X86_64.Adx.Lit

namespace VG

materialize_code Impl.X25519.X86_64.x25519Adx

end VG
