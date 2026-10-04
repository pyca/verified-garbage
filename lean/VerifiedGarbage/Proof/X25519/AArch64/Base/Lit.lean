import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.X25519.AArch64.Base
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseLit

/-! Checked literals for `vg_x25519_base` and its engine. -/

namespace VG

materialize_code Impl.X25519.AArch64.Base.engine
materialize_code Impl.X25519.AArch64.Base.x25519Base

end VG
