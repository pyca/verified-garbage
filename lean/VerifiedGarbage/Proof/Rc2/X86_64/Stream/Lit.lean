module

public import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Lit
public import VerifiedGarbage.Impl.Rc2.X86_64.Stream
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Lit
meta import VerifiedGarbage.Impl.Rc2.X86_64.Stream
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # Literal streaming functions -/

@[expose] public section

namespace VG

materialize_code Impl.Rc2.X86_64.Stream.init
materialize_code Impl.Rc2.X86_64.Stream.encryptUpdate
materialize_code Impl.Rc2.X86_64.Stream.decryptUpdate

end VG
