import VerifiedGarbage.Impl.X25519.X86_64.Base
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit

/-! Checked literals for fixed-base X25519. -/
namespace VG.Proof.X25519.X86_64.Base
open VG VG.Impl.X25519.X86_64
materialize_code baseLit := (Base.x25519Base baseline)
materialize_code baseAdxLit := (Base.x25519Base adx)
materialize_code baseAdxYLit := Base.x25519BaseAdx
end VG.Proof.X25519.X86_64.Base
