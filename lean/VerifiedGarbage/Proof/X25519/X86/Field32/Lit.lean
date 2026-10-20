module

public import VerifiedGarbage.Impl.X25519.X86.Field32
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.X25519.X86.Field32
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! `vg_gf25519_r32_pow250`'s code as a literal (`materialize_code`), which
its checks, and those of the code that calls it, read rather than build each
field multiplication again. -/

@[expose] public section

namespace VG.Impl.X25519.X86.Field32

materialize_code pow250Fn

end VG.Impl.X25519.X86.Field32
