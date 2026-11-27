module

public import VerifiedGarbage.Impl.Md5.Arm.Stream
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Md5.Arm.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# MD5 on Arm: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Md5.Arm.Stream.init
materialize_code Impl.Md5.Arm.Stream.update
materialize_code Impl.Md5.Arm.Stream.finalize

end VG
