import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.X25519.X86.Base
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Ed25519.X86.CombLit

/-! `vg_x25519_base`'s code as literals (`materialize_code`), for the
constant-time checks and `spSafe`. -/
namespace VG.Impl.X25519.X86.Base
open VG VG.X86 VG.Impl.Ed25519.X86

materialize_code x25519BaseStartBlock := (.block x25519BaseStart : Prog isa)
materialize_code x25519BaseFinishTail :=
  (.block (outputWords 64 8 ++ Impl.X25519.X86.restore) : Prog isa)
materialize_code x25519Base

end VG.Impl.X25519.X86.Base
