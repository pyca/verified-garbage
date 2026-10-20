module

public import VerifiedGarbage.Impl.X25519.X86.Field32
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.X25519.X86.Field32
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

/-! `vg_gf25519_r32_pow250`'s code as a literal (`materialize_code`), which
its checks, and those of the code that calls it, read rather than build each
field multiplication again. -/

@[expose] public section

namespace VG.Impl.X25519.X86.Field32

materialize_code pow250Fn

end VG.Impl.X25519.X86.Field32
