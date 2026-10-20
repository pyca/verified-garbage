module

public import VerifiedGarbage.Impl.Sha512.X86.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha512.X86.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

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
