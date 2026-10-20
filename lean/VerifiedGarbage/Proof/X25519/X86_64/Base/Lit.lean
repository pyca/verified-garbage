module

public import VerifiedGarbage.Impl.X25519.X86_64.Base
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
public import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.X25519.X86_64.Base
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.X25519.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! Checked literals for fixed-base X25519. -/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Base
open VG VG.Impl.X25519.X86_64
materialize_code baseLit := (Base.x25519Base baseline)
materialize_code baseAdxLit := (Base.x25519Base adx)
materialize_code baseAdxYLit := Base.x25519BaseAdx
end VG.Proof.X25519.X86_64.Base
