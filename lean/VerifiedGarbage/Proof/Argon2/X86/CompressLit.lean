module

public import VerifiedGarbage.Impl.Argon2.X86.Compress
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Argon2.X86.Compress
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

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
