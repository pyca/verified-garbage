module

public import VerifiedGarbage.Proof.X25519.X86.Field32.CallTaint
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
public import VerifiedGarbage.Impl.X25519.X86.Field32
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.X86.Field32.CallTaint
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
meta import VerifiedGarbage.Impl.X25519.X86.Field32
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The summaries of `vg_gf25519_r32_mul` and `vg_gf25519_r32_sqn`, which
`pow250Call` calls (see `Field32/CallTaint`). -/

@[expose] public section

namespace VG.Proof.X25519.X86

taint_summary gfMulSum : VG.X86.taint τField Impl.X25519.X86.Field32.mulCall

taint_summary gfSqnSum : VG.X86.taint τFieldN Impl.X25519.X86.Field32.sqnCall

end VG.Proof.X25519.X86
