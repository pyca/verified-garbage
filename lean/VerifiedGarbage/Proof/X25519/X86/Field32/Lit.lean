import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.X25519.X86.Field32

/-! `vg_gf25519_r32_pow250`'s code as a literal (`materialize_code`), which
its checks, and those of the code that calls it, read rather than build each
field multiplication again. -/

namespace VG.Impl.X25519.X86.Field32

materialize_code pow250Fn

end VG.Impl.X25519.X86.Field32
