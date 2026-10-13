module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Argon2.X86.Compress
meta import VerifiedGarbage.Impl.Argon2.X86.Compress
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Argon2 compression on x86 (32-bit): the code as a literal

The compression function is fully unrolled: its literal (`materialize_code`)
spares the kernel building the instructions in every check that evaluates
the code (constant time, `spSafe`), and its callers call it.
-/

@[expose] public section

namespace VG.Impl.Argon2.X86

materialize_code compress

end VG.Impl.Argon2.X86
