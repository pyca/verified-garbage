module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.X25519.X86.Base
meta import VerifiedGarbage.Impl.X25519.X86.Base
public import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
public import VerifiedGarbage.Proof.Ed25519.X86.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! `vg_x25519_base`'s code as literals (`materialize_code`), for the
constant-time checks and `spSafe`. -/

@[expose] public section

namespace VG.Impl.X25519.X86.Base
open VG VG.X86 VG.Impl.Ed25519.X86

materialize_code x25519BaseStartBlock := (.block x25519BaseStart : Prog isa)
materialize_code x25519BaseFinishTail :=
  (.block (outputWords 64 8 ++ Impl.X25519.X86.restore) : Prog isa)
materialize_code x25519Base

end VG.Impl.X25519.X86.Base
