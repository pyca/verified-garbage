module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Ed448.X86_64.Scalar
meta import VerifiedGarbage.Impl.Ed448.X86_64.Scalar
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Ed448 scalar arithmetic on x86-64: the code as literals

The kernel checks each literal once; the taint and instruction checks reuse it.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.X86_64.scalarReduce
materialize_code Impl.Ed448.X86_64.scalarMulAdd

end VG
