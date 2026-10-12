module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Sha512.X86.Stream
meta import VerifiedGarbage.Impl.Sha512.X86.Stream
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SHA-512 on x86 (32-bit): the code as literals

The compression function is fully unrolled (6,500 instructions): its
literal (`materialize_code`) spares the kernel building the instructions in
every check that evaluates the code (constant time, `spSafe`), and the
streaming functions call it.
-/

@[expose] public section

namespace VG.Impl.Sha512.X86

materialize_code compress
materialize_code Stream.update
materialize_code Stream.finalize

end VG.Impl.Sha512.X86
