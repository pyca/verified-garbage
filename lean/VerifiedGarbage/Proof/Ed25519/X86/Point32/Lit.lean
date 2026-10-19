module

import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Lit
public import VerifiedGarbage.Impl.Ed25519.X86.Point32
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Ed25519.X86.Point32
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! The point functions' code as literals (`materialize_code`), which
its checks, and those of the code that calls it, read rather than build each
field multiplication again. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86.Point32

materialize_code addFn
materialize_code affFn
materialize_code doubleFn

end VG.Impl.Ed25519.X86.Point32
