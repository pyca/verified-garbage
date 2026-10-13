module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Md5.X86.Stream
meta import VerifiedGarbage.Impl.Md5.X86.Stream
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# MD5 on x86 (32-bit): the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Md5.X86.compress
materialize_code Impl.Md5.X86.Stream.update
materialize_code Impl.Md5.X86.Stream.finalize

end VG
