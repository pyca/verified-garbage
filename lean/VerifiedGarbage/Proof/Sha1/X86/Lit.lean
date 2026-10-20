module

public import VerifiedGarbage.Impl.Sha1.X86.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha1.X86.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SHA-1 on x86 (32-bit): the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha1.X86.compress
materialize_code Impl.Sha1.X86.Stream.update
materialize_code Impl.Sha1.X86.Stream.finalize

end VG
