module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Blake2.X86.CompressB
meta import VerifiedGarbage.Impl.Blake2.X86.CompressB
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# BLAKE2b on x86 (32-bit): the code as literals

The compression function is fully unrolled (about 6,500 instructions): its
literal (`materialize_code`) spares the kernel building the instructions in
every check that evaluates the code (constant time, `spSafe`), and the
streaming functions call it.
-/

@[expose] public section

namespace VG.Impl.Blake2.X86.CompressB

materialize_code compress

end VG.Impl.Blake2.X86.CompressB
