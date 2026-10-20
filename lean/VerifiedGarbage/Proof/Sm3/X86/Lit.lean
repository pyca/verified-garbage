module

public import VerifiedGarbage.Impl.Sm3.X86.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm3.X86.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SM3 on x86: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sm3.X86.compress
materialize_code Impl.Sm3.X86.Stream.update
materialize_code Impl.Sm3.X86.Stream.finalize

end VG
