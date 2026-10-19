module

public import VerifiedGarbage.Impl.X25519.X86.Base
meta import VerifiedGarbage.Impl.X25519.X86.Base
public import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
public import VerifiedGarbage.Proof.Ed25519.X86.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.PointMul
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.Ed25519.X86.PointMul
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! `vg_x25519_base`'s code as literals (`materialize_code`), for the
constant-time checks and `spSafe`. -/

@[expose] public section

namespace VG.Impl.X25519.X86.Base
open VG VG.X86 VG.Impl.Ed25519.X86

materialize_code x25519BaseStart
materialize_code x25519BaseFinishTail :=
  (.block (outputWords 64 8 ++ Impl.X25519.X86.restore) : Prog isa)
materialize_code x25519Base

end VG.Impl.X25519.X86.Base
