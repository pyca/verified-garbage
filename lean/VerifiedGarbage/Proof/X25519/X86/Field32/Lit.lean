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
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! The code of `vg_gf25519_r32_mul` and `vg_gf25519_r32_sqn` as literals
(`materialize_code`), which their checks, and those of the code that calls
them, read rather than build the field multiplication again. -/

@[expose] public section

namespace VG.Impl.X25519.X86.Field32

materialize_code mulFn
materialize_code sqnFn

end VG.Impl.X25519.X86.Field32
