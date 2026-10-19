module

public import VerifiedGarbage.Impl.X448.X86
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.X448.X86
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

/-!
# Curve448's field functions on x86 (32-bit): the code as literals

Untrusted: everything here is checked by Lean. The rows of the product are
unrolled: the literals spare the kernel building the instructions again in
every check that evaluates the code (constant time, the stack pointer,
`spSafe`).
-/

@[expose] public section

namespace VG.Impl.X448.X86

materialize_code mulFn
materialize_code addFn
materialize_code subFn
materialize_code mulA24Fn

end VG.Impl.X448.X86
