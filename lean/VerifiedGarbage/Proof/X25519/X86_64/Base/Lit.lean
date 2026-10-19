module

public import VerifiedGarbage.Impl.X25519.X86_64.Base
meta import VerifiedGarbage.Impl.X25519.X86_64.Base
public import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
import VerifiedGarbage.Impl.Ed25519.X86_64.FieldCheck
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ed25519.X86_64.FieldCheck
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-! Checked literals for fixed-base X25519. -/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Base
open VG VG.Impl.X25519.X86_64
materialize_code baseLit := (Base.x25519Base baseline)
materialize_code baseAdxLit := (Base.x25519Base adx)
materialize_code baseAdxYLit := Base.x25519BaseAdx
end VG.Proof.X25519.X86_64.Base
