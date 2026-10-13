module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.X25519.X86.Field32
meta import VerifiedGarbage.Impl.X25519.X86.Field32
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! `vg_gf25519_r32_pow250`'s code as a literal (`materialize_code`), which
its checks, and those of the code that calls it, read rather than build each
field multiplication again. -/

@[expose] public section

namespace VG.Impl.X25519.X86.Field32

materialize_code pow250Fn

end VG.Impl.X25519.X86.Field32
