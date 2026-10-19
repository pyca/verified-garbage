module

public import VerifiedGarbage.Impl.X25519.X86_64.Adx
meta import VerifiedGarbage.Impl.X25519.X86_64.Adx
public import VerifiedGarbage.Proof.X25519.X86_64.Lit
meta import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# X25519 on x86-64 with BMI2 and ADX: the code as a literal

As for `vg_x25519` (`Proof/X25519/X86_64/Lit.lean`): the literal of the
unrolled code, checked once here, for the checks that evaluate it.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Adx.Lit
open VG.Impl.X25519.X86_64

/-! The multiplications with BMI2 and ADX are templates (`materialize_template`),
beside the baseline's additions, subtractions and swaps
(`Proof/X25519/X86_64/Lit.lean`). -/

materialize_template mulXT := mulX
materialize_template sqrXT := sqrX
materialize_template a24XT := a24addX
materialize_template mul2XT := mul2X
materialize_template sqr2XT := sqr2X

end VG.Proof.X25519.X86_64.Adx.Lit

namespace VG

materialize_code Impl.X25519.X86_64.x25519Adx

end VG
