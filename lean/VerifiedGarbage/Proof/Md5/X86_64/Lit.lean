module

public import VerifiedGarbage.Impl.Md5.X86_64.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Md5.X86_64.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# MD5 on x86-64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Md5.X86_64.compress
materialize_code Impl.Md5.X86_64.Stream.update
materialize_code Impl.Md5.X86_64.Stream.finalize

end VG
