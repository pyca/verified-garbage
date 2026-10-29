module

public import VerifiedGarbage.Impl.Rc2.RISCV64.Stream
public import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Rc2.RISCV64.Stream
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! Literal code keeps the audits that evaluate it (constant time, `spSafe`)
from rebuilding it. -/

@[expose] public section

namespace VG

materialize_code Impl.Rc2.RISCV64.Stream.encryptUpdate
materialize_code Impl.Rc2.RISCV64.Stream.decryptUpdate

end VG
