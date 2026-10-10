import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.Point32

/-! `vg_ed25519_r32_point_add`'s code as a literal (`materialize_code`), which
its checks, and those of the code that calls it, read rather than build each
field multiplication again. -/

namespace VG.Impl.Ed25519.X86.Point32

materialize_code addFn

end VG.Impl.Ed25519.X86.Point32
